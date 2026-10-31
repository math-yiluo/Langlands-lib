import Langlands.Shimura.PEL.HarrisPolarizedWeilTower
import Langlands.AbelianScheme.Tate.AdelicFrameBaseChange
import Mathlib.RingTheory.SimpleRing.Basic

/-! # Faithfulness of actual Harris actions witnessed by pointed adelic frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  {S : Scheme.{0}} (B : AbelianScheme S)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (i : A →ₐ[ℚ] End0 B)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "Af" => Global.FiniteAdeles ℚ
set_option quotPrecheck false in
local notation "Frame" =>
  (letI := scalarExtensionAlgebraModule A A Af
   Tate.AdelicFrame B h i (Af ⊗[ℚ] A) s)

include D C

/-- A frame on the actual nonzero regular Harris source prevents the rational
endomorphism ring of the actual abelian scheme from collapsing. -/
theorem rationalEnd_nontrivial_of_adelicFrame (eta : Frame) : Nontrivial (End0 B) := by
  let : IsSimpleRing A := D.simple
  let := scalarExtensionAlgebraModule A A Af
  obtain ⟨x, y, hxy⟩ := (hodgeRationalPELConditions D C).baseChange_attains_one Af
  have hx : x ≠ 0 := by
    intro hz
    have hzero : (0 : Af) = 1 := by simpa only [hz, map_zero, LinearMap.zero_apply] using hxy
    obtain ⟨v, _, _⟩ := Global.existsUnique_finitePlace_natCast_mem 2 Nat.prime_two
    have hv := congrArg (fun a : Af => a v) hzero
    exact zero_ne_one hv
  refine ⟨⟨1, 0, ?_⟩⟩
  intro hzero
  have hvalue := congrArg
    (fun f : End0 B => Tate.rationalEndAction B (Over.mk s) (fun _ => True) f (eta x))
    hzero
  have heta : eta x = 0 := by
    simpa only [map_one, map_zero, Module.End.one_apply, LinearMap.zero_apply] using hvalue
  exact hx (eta.injective (heta.trans (map_zero eta).symm))

/-- Simplicity of the actual Harris algebra turns that noncollapse into
injectivity of the actual rational algebra action. -/
theorem action_injective_of_adelicFrame (eta : Frame) : Function.Injective i := by
  let : IsSimpleRing A := D.simple
  let : Nontrivial (End0 B) :=
    rationalEnd_nontrivial_of_adelicFrame D C B h i s eta
  exact RingHom.injective i.toRingHom

/-- The actual framed Harris action, bundled as an embedding without replacing
its rational endomorphism values. -/
def adelicFrameActionEmbedding (eta : Frame) : A ↪ End0 B where
  toFun := i
  inj' := action_injective_of_adelicFrame D C B h i s eta

@[simp] theorem adelicFrameActionEmbedding_apply (eta : Frame) (a : A) :
    adelicFrameActionEmbedding D C B h i s eta a = i a := rfl

variable {T : Scheme.{0}} (b : T ⟶ S)
  (t : Spec (.of Ω) ⟶ T)

/-- Pointed actual pullback preserves faithfulness when the actual Harris frame
is present over the composed geometric point. -/
theorem action_baseChange_injective_of_adelicFrame
    (eta : letI := scalarExtensionAlgebraModule A A Af
      Tate.AdelicFrame B h i (Af ⊗[ℚ] A) (t ≫ b)) :
    Function.Injective ((rationalBaseChangeEnd b B).comp i) := by
  let := scalarExtensionAlgebraModule A A Af
  exact action_injective_of_adelicFrame D C ((baseChange b).obj B) h
    ((rationalBaseChangeEnd b B).comp i) t
    ((Tate.adelicFrameBaseChange b B h i (Af ⊗[ℚ] A) t).symm eta)

/-- Mere existence of the actual pointed frame suffices; no frame choice is
part of the resulting injectivity proposition. -/
theorem action_baseChange_injective_of_nonempty_adelicFrame
    (heta : Nonempty (letI := scalarExtensionAlgebraModule A A Af
      Tate.AdelicFrame B h i (Af ⊗[ℚ] A) (t ≫ b))) :
    Function.Injective ((rationalBaseChangeEnd b B).comp i) := by
  obtain ⟨eta⟩ := heta
  exact action_baseChange_injective_of_adelicFrame D C B h i b t eta

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
