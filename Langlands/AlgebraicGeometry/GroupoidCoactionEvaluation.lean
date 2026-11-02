import Langlands.AlgebraicGeometry.GroupoidCoactionFinitePi
import Langlands.AlgebraicGeometry.GroupoidCoactionArtinRees
import Langlands.AlgebraicGeometry.GroupoidCoactionCoveringIdealPowers

/-! # Evaluation, Artin–Rees and coordinate retracts -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {Y H : Type v} [AddCommGroup Y] [Module B Y]
  [AddCommGroup H] [Module B H]
variable {ι : Type}

/-- Simultaneous evaluation at a finite family of source elements. -/
def evaluationFamily (a : ι → Y) : (Y →ₗ[B] H) →ₗ[B] (ι → H) :=
  LinearMap.pi (fun i => LinearMap.applyₗ (R := B) (M₂ := H) (a i))

@[simp]
lemma evaluationFamily_apply (a : ι → Y) (f : Y →ₗ[B] H) (i : ι) :
    evaluationFamily a f i = f (a i) := rfl

@[simp]
lemma proj_comp_evaluationFamily (a : ι → Y) (i : ι) :
    (LinearMap.proj i).comp (evaluationFamily (B := B) (H := H) a) =
      LinearMap.applyₗ (R := B) (M₂ := H) (a i) := rfl

variable [Fintype ι] [DecidableEq ι]

/-- Evaluation at invariant source elements is equivariant for the product coaction. -/
lemma evaluationFamily_isHom [Module.FinitePresentation B Y]
    (hE : RingEtaleEquivalenceRelation t)
    (θY : GroupoidCoaction t Y) (θH : GroupoidCoaction t H)
    (a : ι → Y) (ha : ∀ i, a i ∈ θY.invariants) :
    (hom hE θY θH).IsHom (finitePi θH) (evaluationFamily a) := by
  intro f
  apply finitePi_tensor_ext
  intro i
  rw [finitePi_coaction, finitePiCoactionMap_proj, ← LinearMap.lTensor_comp_apply,
    proj_comp_evaluationFamily]
  exact hom_eval_isHom hE θY θH (a i) (ha i) f

attribute [local instance] Module.finitePresentation_of_finite

/-- Artin–Rees and a coordinate retract transfer vanishing through finite evaluation. -/
theorem oneCohomologyVanishes_of_evaluation [IsNoetherianRing B]
    [Module.Finite B Y] [Module.Finite B H]
    (hE : RingEtaleEquivalenceRelation t)
    (θY : GroupoidCoaction t Y) (θH : GroupoidCoaction t H)
    (a : ι → Y) (ha : ∀ i, a i ∈ θY.invariants) (i₀ : ι)
    (I : Ideal B) (hI : IsInvariantIdeal t I)
    (hK : I ≤ (Module.annihilator B (LinearMap.ker (evaluationFamily (B := B) (H := H) a))).radical)
    (hQ : I ≤ (Module.annihilator B
      ((ι → H) ⧸ LinearMap.range (evaluationFamily (B := B) (H := H) a))).radical)
    (hvan : FiniteAnnihilatorVanishing.{u, v} t I)
    (hpowers : ∀ n : ℕ, ∀ hstable : (hom hE θY θH).IsStableSubmodule
      (I ^ n • (⊤ : Submodule B (Y →ₗ[B] H))),
      (submodule (hom hE θY θH) _ hE hstable).OneCohomologyVanishes) :
    θH.OneCohomologyVanishes := by
  apply oneCohomologyVanishes_of_finitePi θH i₀
  exact oneCohomologyVanishes_of_artinRees hE (hom hE θY θH) (finitePi θH)
    (evaluationFamily a) (evaluationFamily_isHom hE θY θH a ha) I hI hK hQ hvan hpowers

section Covering

variable {D P : Type u} [CommRing D] [CommRing P]
  [Algebra B D] [Algebra D P] [Algebra B P] [IsScalarTower B D P]
variable {G K : Type (max u v)} [AddCommGroup G] [Module D G] [Module B G]
  [IsScalarTower B D G] [AddCommGroup K] [Module B K]
variable (e : P ≃ₐ[D] D ⊗[B] C)
variable {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
variable (ψ : GroupoidCoaction td G) (θ : GroupoidCoaction t K)
variable (ε : P ≃ₐ[D] D ⊗[invariantRing td] D)
  (hε : ∀ d : D, ε (td d) = (1 : D) ⊗ₜ[invariantRing td] d)
variable [Module.FaithfullyFlat (invariantRing td) D]

include ε hε in
/-- Under an effective faithfully flat covering presentation, ideal-power
vanishing for the evaluation source follows from covering Hom descent. -/
theorem oneCohomologyVanishes_of_covering_evaluation [IsNoetherianRing B]
    [Module.Finite B G] [Module.Finite B K]
    (a : ι → G) (ha : ∀ i, a i ∈ (pushforward e ht ψ hE hP).invariants) (i₀ : ι)
    (I : Ideal B) (hI : IsInvariantIdeal t I)
    (hK : I ≤ (Module.annihilator B (LinearMap.ker (evaluationFamily (B := B) (H := K) a))).radical)
    (hQ : I ≤ (Module.annihilator B
      ((ι → K) ⧸ LinearMap.range (evaluationFamily (B := B) (H := K) a))).radical)
    (hvan : FiniteAnnihilatorVanishing.{u, max u v} t I) :
    θ.OneCohomologyVanishes := by
  apply oneCohomologyVanishes_of_evaluation hE (pushforward e ht ψ hE hP) θ
    a ha i₀ I hI hK hQ hvan
  intro n hstable
  exact idealPower_hom_pushforward_oneCohomologyVanishes e ht hE hP ψ θ ε hε I hI n hstable

end Covering

end Langlands.AlgebraicGeometry.GroupoidCoaction
