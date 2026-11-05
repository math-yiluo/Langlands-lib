import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.Topology.LocallyConstant.Basic

/-! # Openness of the actual finite-character valuation kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [Valued k Γ₀] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

local instance kpCharacterKernelPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X

private theorem isLocallyConstant_valuationUnits :
    IsLocallyConstant (fun x : kˣ => (Valued.v : Valuation k Γ₀) (x : k)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact Units.continuous_val.continuousAt.preimage_mem_nhds
    (Valued.locally_const ((Valued.v : Valuation k Γ₀).ne_zero_iff.mpr x.ne_zero))

private def valuationCharacterAt (g : rationalPoints G) :
    rationalCharacters G →+ Additive Γ₀ˣ where
  toFun χ := Additive.ofMul
    (Units.map (Valued.v : Valuation k Γ₀).toMonoidHom (rationalCharacterEval χ g))
  map_zero' := by simp [rationalCharacterEval_zero]
  map_add' χ ψ := by
    simp only [rationalCharacterEval_add, map_mul]
    rfl

omit [IsAffine G.X.left] in
/-- Finitely many character generators suffice to test membership in the
existing common valuation kernel. -/
theorem mem_characterValuationKernel_iff_generators
    {n : ℕ} (s : Fin n → rationalCharacters G)
    (hs : Submodule.span ℤ (Set.range s) = ⊤) (g : rationalPoints G) :
    g ∈ characterValuationKernel (Valued.v : Valuation k Γ₀) G ↔
      ∀ i, (Valued.v : Valuation k Γ₀) (rationalCharacterEval (s i) g : k) = 1 := by
  rw [mem_characterValuationKernel]
  refine ⟨fun h i => h (s i), fun h χ => ?_⟩
  let f := (valuationCharacterAt G g).toIntLinearMap
  have htop : (⊤ : Submodule ℤ (rationalCharacters G)) ≤ f.ker := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change Additive.ofMul
      (Units.map (Valued.v : Valuation k Γ₀).toMonoidHom
        (rationalCharacterEval (s i) g)) = 0
    apply Additive.ofMul.injective
    apply Units.ext
    exact h i
  have hf := htop (Submodule.mem_top : χ ∈ (⊤ : Submodule ℤ (rationalCharacters G)))
  change valuationCharacterAt G g χ = 0 at hf
  exact congrArg (fun a : Additive Γ₀ˣ => (a.toMul : Γ₀)) hf

/-- The original common valuation kernel is open whenever the actual rational
character module is finitely generated. No completeness is required. -/
theorem isOpen_characterValuationKernel [Module.Finite ℤ (rationalCharacters G)] :
    IsOpen (characterValuationKernel (Valued.v : Valuation k Γ₀) G :
      Set (rationalPoints G)) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := rationalCharacters G)
  have he : (characterValuationKernel (Valued.v : Valuation k Γ₀) G :
      Set (rationalPoints G)) =
      ⋂ i, {g | (Valued.v : Valuation k Γ₀) (rationalCharacterEval (s i) g : k) = 1} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_characterValuationKernel_iff_generators G s hs g
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact ((isLocallyConstant_valuationUnits (k := k) (Γ₀ := Γ₀)).comp_continuous
    (continuous_rationalCharacterEval G (s i))).isOpen_fiber 1

/-- Bundle the unchanged character valuation kernel as an open subgroup in
exactly the canonical rational-point topology. -/
def characterValuationOpenSubgroup [Module.Finite ℤ (rationalCharacters G)] :
    OpenSubgroup (rationalPoints G) where
  toSubgroup := characterValuationKernel (Valued.v : Valuation k Γ₀) G
  isOpen' := isOpen_characterValuationKernel G

@[simp] theorem characterValuationOpenSubgroup_toSubgroup
    [Module.Finite ℤ (rationalCharacters G)] :
    (characterValuationOpenSubgroup G (Γ₀ := Γ₀)).toSubgroup =
      characterValuationKernel (Valued.v : Valuation k Γ₀) G := rfl

/-- The finite-character hypothesis follows from connected reductivity. -/
theorem isOpen_characterValuationKernel_of_isConnectedReductive
    (hG : IsConnectedReductive G) :
    IsOpen (characterValuationKernel (Valued.v : Valuation k Γ₀) G :
      Set (rationalPoints G)) := by
  let := (rationalCharacterLattice k G hG).2
  exact isOpen_characterValuationKernel G

/-- In particular, the actual split-torus kernel is open over a possibly
noncomplete valued field. -/
theorem isOpen_characterValuationKernel_of_isSplitTorus (hG : IsSplitTorus G) :
    IsOpen (characterValuationKernel (Valued.v : Valuation k Γ₀) G :
      Set (rationalPoints G)) :=
  isOpen_characterValuationKernel_of_isConnectedReductive G hG.isConnectedReductive

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  (E : UnramifiedZeroDatum F H)

private instance splitBaseChange_isAffine :
    IsAffine (GaloisPointComparison.baseChanged
      (UnramifiedClosure F) E.L E.T.toGrp).X.left := by
  let : IsAffineHom (GaloisPointComparison.baseChanged
      (UnramifiedClosure F) E.L E.T.toGrp).X.hom := E.isSplitTorus.isAffineHom
  exact isAffine_of_isAffineHom (GaloisPointComparison.baseChanged
    (UnramifiedClosure F) E.L E.T.toGrp).X.hom

/-- The exact bounded-character subgroup used in the supplied datum's norm
definition is open in the topology of its actual intermediate valuation. -/
theorem UnramifiedZeroDatum.isOpen_splitCharacterValuationKernel :
    letI : Valued E.L ℝ≥0 := Valued.mk' (intermediateValuation F E.L)
    letI : TopologicalSpace (rationalPoints
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)) :=
      rationalPointTopology E.L
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp).X
    IsOpen (characterValuationKernel (intermediateValuation F E.L)
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp) :
      Set (rationalPoints
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp))) := by
  let : Valued E.L ℝ≥0 := Valued.mk' (intermediateValuation F E.L)
  exact isOpen_characterValuationKernel_of_isSplitTorus _ E.isSplitTorus

end Unramified

end Langlands.Geometry.Building
