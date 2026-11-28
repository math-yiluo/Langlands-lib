import Langlands.Global.RankinSelberg.RealStandardCompactFinite
import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.RealSmoothCompactFiniteDensity

/-! # The Banach compact carrier is determined by the compact shape -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors RealExponentDeformation

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {n : ℕ}

local notation "I" => matrixModel ℝ n
local notation:max "R" ds:max => representation (n := n) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)

private theorem denseRange_embed_compactFinite (ds : List RealBlock) :
    DenseRange (fun f : KF n ds => embed ds ⟨f.val, f.property.1⟩) := by
  let a := derivativeCLM I (R ds) []
  have ha : DenseRange a := by
    apply (denseRange_embed ds).mono
    rintro _ ⟨f, rfl⟩
    exact ⟨derivativeEquiv ds f, toSmooth_derivativeEquiv ds f⟩
  have hf : DenseRange (fun f : KF n ds => (compactFiniteEquiv (n := n) ds f).val) := by
    have hrange : Set.range (fun f : KF n ds => (compactFiniteEquiv (n := n) ds f).val) =
        (smoothKFinite ℝ n (R ds) : Set (D ds)) := by
      rw [show (fun f : KF n ds => (compactFiniteEquiv (n := n) ds f).val) =
          Subtype.val ∘ compactFiniteEquiv (n := n) ds from rfl,
        (compactFiniteEquiv (n := n) ds).surjective.range_comp, Subtype.range_coe]
    show Dense _
    rw [hrange]
    exact realSmoothCompactFiniteDensity n _ (R ds) (isContinuousRepresentation ds)
  have h := ha.comp hf a.continuous
  convert h using 1
  funext f
  change embed ds ⟨f.val, f.property.1⟩ = a (compactFiniteEquiv ds f).val
  rw [compactFiniteEquiv_val]
  exact (toSmooth_derivativeEquiv ds ⟨f.val, f.property.1⟩).symm

/-- Shape compatible lists give an inclusion of compact Banach carriers. -/
theorem closureSubmodule_le_of_shape {ds es : List RealBlock} (he : realRank es = n)
    (h : IsShapeCompatible ds es) :
    closureSubmodule (n := n) ds ≤ closureSubmodule es := by
  intro v hv
  let U := (Subtype.val : Carrier n ds → C(Matrix.unitaryGroup (Fin n) ℝ, ℂ)) ⁻¹'
    (closureSubmodule (n := n) es : Set C(Matrix.unitaryGroup (Fin n) ℝ, ℂ))
  have hU : IsClosed U := (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have hf : Set.range (fun f : KF n ds => embed ds ⟨f.val, f.property.1⟩) ⊆ U := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := exists_eqOn he h f
    have heq : compactRestriction ds ⟨f.val, f.property.1⟩ =
        compactRestriction es ⟨g.val, g.property.1⟩ := by
      ext k
      exact (hg k.prop).symm
    change compactRestriction ds ⟨f.val, f.property.1⟩ ∈ closureSubmodule (n := n) es
    rw [heq]
    exact (embed es ⟨g.val, g.property.1⟩).prop
  exact closure_minimal hf hU (denseRange_embed_compactFinite ds ⟨v, hv⟩)

/-- Mutual compatibility of compact shapes identifies the norm closures of the
two standard modules as subspaces of the same continuous function space. -/
def RealStandardCompactShapeStatement : Prop :=
  ∀ (n : ℕ) (ds es : List RealBlock), realRank ds = n → realRank es = n →
    IsShapeCompatible ds es → IsShapeCompatible es ds →
    closureSubmodule (n := n) ds = closureSubmodule (n := n) es

theorem realStandardCompactShape : RealStandardCompactShapeStatement :=
  fun _ _ _ hd he h h' => le_antisymm (closureSubmodule_le_of_shape he h) (closureSubmodule_le_of_shape hd h')

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
