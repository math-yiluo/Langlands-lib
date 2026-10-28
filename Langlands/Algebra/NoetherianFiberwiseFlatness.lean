import Langlands.Algebra.NoetherianFiberwiseFlatnessStatement
import Langlands.Algebra.IdealLocalFlatnessCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The Noetherian local fibrewise flatness criterion -/

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra

open TensorProduct

private theorem faithfullyFlat_of_finite_local
    (S : Type v) (S' : Type w) (M : Type z)
    [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S']
    [Algebra S S'] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S M] [Module S' M] [IsScalarTower S S' M]
    [Module.Finite S' M] [Nontrivial M] [Module.Flat S M] :
    Module.FaithfullyFlat S M := by
  refine ⟨?_⟩
  intro m hm htop
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  have htop' :
      (IsLocalRing.maximalIdeal S).map (algebraMap S S') •
        (⊤ : Submodule S' M) = ⊤ := by
    apply Submodule.restrictScalars_injective S S' M
    simpa only [Ideal.smul_restrictScalars, Submodule.restrictScalars_top] using htop
  have hle : (⊤ : Submodule S' M) ≤
      IsLocalRing.maximalIdeal S' • (⊤ : Submodule S' M) := by
    calc
      (⊤ : Submodule S' M) = _ := htop'.symm
      _ ≤ _ := Submodule.smul_mono
        (IsLocalRing.map_maximalIdeal_le (algebraMap S S')) le_rfl
  exact top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (IsLocalRing.maximalIdeal S') ⊤ Module.Finite.fg_top hle (by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]))

private theorem baseChange_lTensor_injective
    (R : Type u) (S : Type v) (M : Type z)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R M] (I : Ideal R) :
    Function.Injective ((I.subtype.baseChange S).lTensor M) := by
  let f := I.subtype.baseChange S
  let eI := AlgebraTensorModule.cancelBaseChange R S S M I
  let eR := AlgebraTensorModule.cancelBaseChange R S S M R
  have he : eR.toLinearMap ∘ₗ f.lTensor M =
      AlgebraTensorModule.lTensor S M I.subtype ∘ₗ eI.toLinearMap := by
    ext
    simp [eI, eR, f]
  have hinj : Function.Injective
      (AlgebraTensorModule.lTensor S M I.subtype ∘ₗ eI.toLinearMap) :=
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype
      Subtype.val_injective).comp eI.injective
  rw [← he] at hinj
  intro x y h
  apply hinj
  exact congrArg eR h

private theorem flat_of_faithfullyFlat_module
    (R : Type u) (S : Type v) (M : Type z)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R M] [Module.FaithfullyFlat S M] :
    Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective S M
    (I.subtype.baseChange S)).mp (baseChange_lTensor_injective R S M I)

private theorem extendedIdeal_rTensor_injective
    (R : Type u) (S : Type v) (M : Type z)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R M] (I : Ideal R) :
    Function.Injective ((I.map (algebraMap R S)).subtype.rTensor M) := by
  let J := I.map (algebraMap R S)
  let e := AlgebraTensorModule.rid R S S
  let f : S ⊗[R] I →ₗ[S] S := e.toLinearMap ∘ₗ I.subtype.baseChange S
  have hfr : f.restrictScalars R =
      ((TensorProduct.lid R S).toLinearMap ∘ₗ I.subtype.rTensor S) ∘ₗ
        (TensorProduct.comm R S I).toLinearMap := by
    ext s i
    simp [f, e, Algebra.smul_def, mul_comm]
  have hrange : f.range = J := by
    apply Submodule.restrictScalars_injective R S S
    rw [← LinearMap.range_restrictScalars, hfr, LinearEquiv.range_comp,
      Ideal.subtype_rTensor_range, Ideal.smul_top_eq_map]
  let p : S ⊗[R] I →ₗ[S] J := f.codRestrict J (fun x => by
    rw [← hrange]
    exact LinearMap.mem_range_self f x)
  have hp : Function.Surjective p := by
    intro y
    have hy : (y : S) ∈ f.range := by
      rw [hrange]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hf : Function.Injective (f.lTensor M) := by
    have he : f.lTensor M =
        (e.lTensor M).toLinearMap ∘ₗ (I.subtype.baseChange S).lTensor M := by
      ext
      simp [f]
    rw [he]
    exact (e.lTensor M).injective.comp (baseChange_lTensor_injective R S M I)
  have hcomp : J.subtype.lTensor M ∘ₗ p.lTensor M = f.lTensor M := by
    ext
    rfl
  have hinj : Function.Injective (J.subtype.lTensor M) := by
    intro x y h
    obtain ⟨a, rfl⟩ := LinearMap.lTensor_surjective M hp x
    obtain ⟨b, rfl⟩ := LinearMap.lTensor_surjective M hp y
    apply congrArg (p.lTensor M)
    apply hf
    simpa only [← hcomp, LinearMap.comp_apply] using h
  exact (LinearMap.lTensor_inj_iff_rTensor_inj M J.subtype).mp hinj

private theorem quotient_flat_of_tensor_fibre_flat
    (R : Type u) (S : Type v) (M : Type z)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R)
    [Module.Flat (S ⊗[R] (R ⧸ I)) ((S ⊗[R] (R ⧸ I)) ⊗[S] M)] :
    Module.Flat (S ⧸ I.map (algebraMap R S))
      ((S ⧸ I.map (algebraMap R S)) ⊗[S] M) := by
  let C := S ⧸ I.map (algebraMap R S)
  let F := S ⊗[R] (R ⧸ I)
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I
  let : Algebra C F := e.toRingHom.toAlgebra
  let : IsScalarTower S C F := IsScalarTower.of_algebraMap_eq fun s => by
    change algebraMap S F s = e (algebraMap S C s)
    exact (e.commutes s).symm
  let eC : C ≃ₗ[C] F :=
    LinearEquiv.ofBijective (Algebra.linearMap C F) e.bijective
  let : Module.Flat C F := Module.Flat.of_linearEquiv eC.symm
  let : Module.Flat C (F ⊗[S] M) := Module.Flat.trans C F _
  exact Module.Flat.of_linearEquiv
    (AlgebraTensorModule.congr eC (LinearEquiv.refl S M))

/-- Stacks Project, Lemma 10.99.15 (00MP), via the ideal local criterion,
Nakayama's lemma, and faithful flatness. -/
theorem noetherianFiberwiseFlatness :
    NoetherianFiberwiseFlatnessStatement.{u, v, w, z} := by
  intro R S S' M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hfin hnontriv hfibre hflat
  let : Module.Finite S' M := hfin
  let : Nontrivial M := hnontriv
  let : Module.Flat R M := hflat
  let I := IsLocalRing.maximalIdeal R
  let J := I.map (algebraMap R S)
  have hJ : J ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  let : Module.Flat (S ⊗[R] (R ⧸ I)) ((S ⊗[R] (R ⧸ I)) ⊗[S] M) := hfibre
  have hquot : Module.Flat (S ⧸ J) ((S ⧸ J) ⊗[S] M) :=
    quotient_flat_of_tensor_fibre_flat R S M I
  have hS : Module.Flat S M :=
    idealLocalFlatnessCriterion.{v, w, z} S S' M J hJ hfin
      (extendedIdeal_rTensor_injective R S M I) hquot
  let : Module.Flat S M := hS
  let : Module.FaithfullyFlat S M := faithfullyFlat_of_finite_local S S' M
  exact ⟨flat_of_faithfullyFlat_module R S M, hS⟩

example : NoetherianFiberwiseFlatnessStatement.{u, v, w, z} :=
  noetherianFiberwiseFlatness.{u, v, w, z}

end Langlands.Algebra
