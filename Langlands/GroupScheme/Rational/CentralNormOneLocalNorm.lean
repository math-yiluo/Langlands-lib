import Langlands.ClassField.Global.TensorNormPrimitiveBaseChange
import Langlands.ClassField.Global.CompletionTower
import Langlands.Global.Arithmetic.ArchimedeanAlgebraicClosure
import Langlands.Global.Arithmetic.CompletionTensorFullDegree
import Langlands.GroupScheme.Rational.CentralNormOneCocycleLift

/-! # The scalar norm condition from local central trivializations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct NumberField.LiesOver CategoryTheory.MonObj
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.GroupScheme.IsCentralIsogeny

open Langlands.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassField.Global.TensorUnitShapiro
open Langlands.LocalClassField
open KummerCocycle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B L : Type u} [Field F] [Field B] [Field L] [Algebra F B] [Algebra F L]
  [FiniteDimensional F B] [IsGalois F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)
  (n : ℕ) (e : kernel f ≅ WeilGm.normOneTorsion F B n)
  {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ)
  (a : Gal(L/F) → (B ⊗[F] L)ˣ) (ha : ∀ σ, a σ ^ n = 1)
  (hδ : ∀ σ τ, tensorDifferential a σ τ =
    hf.kernelTensorDefect (kernelNormOneToWeil n e) d (σ, τ))
  {s : Fˣ} {z : Lˣ} (hz : z ^ n = Units.map (algebraMap F L).toMonoidHom s)
  (hN : ∀ σ, tensorNormUnits F B L (a σ) = value z σ)

section NewBase

variable {K D : Type u} [Field K] [Field D] [Algebra F K] [Algebra K D]

include hf e d a ha hδ hz hN in
/-- If the base-changed tensor has a field model, a local trivialization forces the
scalar norm radical of the tensor primitive to be a norm modulo powers. -/
theorem isNormMulPower_of_normOneKernel_baseChange {M : Type u} [Field M]
    [Algebra K M] [Algebra F M] [Algebra L M] [Algebra D M]
    [IsScalarTower F K M] [IsScalarTower F L M] [IsScalarTower K D M]
    [FiniteDimensional K D] [FiniteDimensional K M] [IsGalois K M] [CharZero K]
    (j : K ⊗[F] B ≃ₐ[K] D)
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    IsNormMulPower (E := D) n (Units.map (algebraMap F K).toMonoidHom s) := by
  obtain ⟨N, _, _, _, _, _, _, _, _, _, _, _, _, p, hp⟩ :=
    hf.exists_primitive_of_baseChange_isTrivial (K := K) (M := M) ξ d h
  let : Algebra D N := Algebra.compHom N (algebraMap D M)
  let : IsScalarTower K D N := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K M N, IsScalarTower.algebraMap_apply K D M]
    rfl
  let k := kernelNormOneToWeil n e
  let u := kernelTensorUnitMap k N
  let v := baseChangeTensorUnitEquiv (M := N) j
  let b (σ : Gal(N/K)) := v (u (p σ))
  have hb (σ : Gal(N/K)) : b σ ^ n = 1 := by
    dsimp only [b]
    rw [← map_pow, kernelTensorUnitMap_pow_eq_one n e, map_one]
  have hnorm (σ : Gal(N/K)) : tensorNormUnits K D N (b σ) = 1 := by
    change tensorNormUnits K D N (baseChangeTensorUnitEquiv j (u (p σ))) = _
    rw [baseChangeTensorUnitEquiv_norm, kernelTensorUnitMap_norm_eq_one n e]
  apply isNormMulPower_of_transferred_primitive j n a ha b hb hnorm _ hz hN
  intro σ τ
  have hact (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F N)) :
      u (GaloisPoint.relativeConjugate F K N (kernel f) σ x) =
        tensorAction F B N (σ.restrictScalars F) (u x) :=
    kernelTensorUnitMap_naturality k (σ.restrictScalars F).toAlgHom x
  have hext (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F L)) :
      u (GaloisPoint.relativeExtend F L N (kernel f) x) =
        extendTensorUnit N (kernelTensorUnitMap k L x) :=
    kernelTensorUnitMap_naturality k (IsScalarTower.toAlgHom F L N) x
  rw [hδ]
  change tensorAction K D N σ (v (u (p τ))) / v (u (p (σ * τ))) * v (u (p σ)) =
    v (extendTensorUnit N (kernelTensorUnitMap k L (d.defect
      ((σ.restrictScalars F).restrictNormal L, (τ.restrictScalars F).restrictNormal L))))
  have hact' : v (tensorAction F B N (σ.restrictScalars F) (u (p τ))) =
      tensorAction K D N σ (v (u (p τ))) := baseChangeTensorUnitEquiv_action j σ _
  rw [← hact', ← hact, ← hext, ← map_div v, ← map_mul v, ← map_div u, ← map_mul u]
  exact congrArg (fun x => v (u x)) (hp σ τ)

end NewBase

section Completions

variable [NumberField F] [NumberField B] [NumberField L]

private theorem isNormMulPower_of_finrank_one {K D : Type u} [Field K] [Field D]
    [Algebra K D] [FiniteDimensional K D] (h : Module.finrank K D = 1) (n : ℕ) (x : Kˣ) :
    IsNormMulPower (E := D) n x := by
  apply isNormMulPower_of_coprime
  rw [h]
  exact Nat.coprime_one_left _

include hf e d a ha hδ hz hN in
/-- For a quadratic norm-one kernel the norm-radical condition holds at a finite
completion where the cocycle is trivial on the actual pullback cover. -/
theorem isNormMulPower_of_normOneKernel_finite [Algebra B L] [IsScalarTower F B L]
    (hB : Module.finrank F B = 2)
    (v : Global.FinitePlace F) (w : Global.FinitePlace B) [w.asIdeal.LiesOver v.asIdeal]
    (h : (ξ.baseChangePullback (Spec.algebraMap F (v.adicCompletion F))).IsTrivial) :
    IsNormMulPower (E := w.adicCompletion B) n
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom s) := by
  let K := v.adicCompletion F
  let D := w.adicCompletion B
  let : FiniteDimensional K D := FiniteExtension.local_finite v w
  let : Algebra.IsQuadraticExtension F B := { finrank_eq_two' := hB }
  let : IsGalois F B := inferInstance
  have hdeg := finiteCompletion_finrank_dvd v w
  rw [hB] at hdeg
  rcases (Nat.dvd_prime Nat.prime_two).mp hdeg with h₁ | h₂
  · exact isNormMulPower_of_finrank_one h₁ n _
  · obtain ⟨t, ht⟩ := exists_place_above (L := L) w
    let : t.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans t.asIdeal w.asIdeal v.asIdeal
    let M := t.adicCompletion L
    let : FiniteDimensional K M := FiniteExtension.local_finite v t
    let : IsGalois K M := isGalois_adicCompletion v t
    let : IsScalarTower K D M := ClassField.Global.CompletionTower.isScalarTower_completion v w t
    let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
    exact hf.isNormMulPower_of_normOneKernel_baseChange (M := M) n e d a ha hδ hz hN
      (finiteCompletionTensorEquiv v w (h₂.trans hB.symm)) h

omit [NumberField L] in
include hf e d a ha hδ hz hN in
/-- For a quadratic norm-one kernel the norm-radical condition also holds at an infinite
completion where the cocycle is trivial on the actual pullback cover. -/
theorem isNormMulPower_of_normOneKernel_infinite [FiniteDimensional F L]
    (hB : Module.finrank F B = 2) (v : NumberField.InfinitePlace F)
    (w : NumberField.InfinitePlace B) [w.LiesOver v]
    (h : (ξ.baseChangePullback (Spec.algebraMap F v.Completion)).IsTrivial) :
    IsNormMulPower (E := w.Completion) n (Units.map (algebraMap F v.Completion).toMonoidHom s) := by
  rcases w.isUnramified_or_isRamified F with h₁ | h₂
  · exact isNormMulPower_of_finrank_one (h₁.finrank_eq_one v) n _
  · let K := v.Completion
    let D := w.Completion
    let M := AlgebraicClosure K
    let : FiniteDimensional K M := Global.finiteArchimedeanAlgebraicClosure F v
    let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
    let : IsGalois K M := isGalois_iff.mpr ⟨inferInstance, ⟨fun _ => IsAlgClosed.splits _⟩⟩
    let jL : L →ₐ[F] M := IsAlgClosed.lift
    let jD : D →ₐ[K] M := IsAlgClosed.lift
    let : Algebra L M := jL.toRingHom.toAlgebra
    let : Algebra D M := jD.toRingHom.toAlgebra
    let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => (jL.commutes x).symm
    let : IsScalarTower K D M := IsScalarTower.of_algebraMap_eq fun x => (jD.commutes x).symm
    exact hf.isNormMulPower_of_normOneKernel_baseChange (M := M) n e d a ha hδ hz hN
      (infiniteCompletionTensorEquiv v w ((h₂.finrank_eq_two v).trans hB.symm)) h

end Completions
end Langlands.GroupScheme.IsCentralIsogeny

namespace Langlands.GroupScheme

open Langlands.Algebra Langlands.Global Langlands.ClassField.Global.TensorUnitShapiro
open KummerCocycle
open IsCentralIsogeny

/-- For a quadratic norm-one kernel, a scalar Kummer radicand of a torsion
primitive for an everywhere locally trivial central defect is a norm modulo powers. -/
def NumberFieldQuadraticNormOneRadicalDescentStatement : Prop :=
  ∀ (F B L : Type u) [Field F] [Field B] [Field L] [NumberField F] [NumberField B] [NumberField L]
    [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L] [IsGalois F L],
    Module.finrank F B = 2 →
    ∀ {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)
      (n : ℕ) (e : kernel f ≅ WeilGm.normOneTorsion F B n)
      {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ),
      ξ.LocallyTrivial →
      ∀ (a : Gal(L/F) → (B ⊗[F] L)ˣ), (∀ σ, a σ ^ n = 1) →
        (∀ σ τ, tensorDifferential a σ τ =
          hf.kernelTensorDefect (kernelNormOneToWeil n e) d (σ, τ)) →
        ∀ (s : Fˣ) (z : Lˣ), z ^ n = Units.map (algebraMap F L).toMonoidHom s →
          (∀ σ, tensorNormUnits F B L (a σ) = value z σ) → IsNormMulPower (E := B) n s

/-- The actual completed norm conditions and quadratic norm descent give the global correction. -/
theorem numberFieldQuadraticNormOneRadicalDescent :
    NumberFieldQuadraticNormOneRadicalDescentStatement.{u} := by
  intro F B L _ _ _ _ _ _ _ _ _ _ _ hB G H f hf n e ξ d h a ha hδ s z hz hN
  apply numberFieldQuadraticNormPowerDescent F B hB n s
  · intro v w _
    exact hf.isNormMulPower_of_normOneKernel_finite n e d a ha hδ hz hN hB v w (h (.inr v))
  · intro v w _
    exact hf.isNormMulPower_of_normOneKernel_infinite n e d a ha hδ hz hN hB v w (h (.inl v))

end Langlands.GroupScheme
