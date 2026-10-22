import Langlands.Global.AdelicFunctoriality.NormStatement
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Data.Fintype.Option

/-! # Determinant reduction of the principal-norm formula

The infinite-place formula is unconditional. The finite-place and global formulas
in this file explicitly depend on bijectivity of the constructed finite tensor map.
The complete `NormCompatibility` proposition is not proved here.
-/

noncomputable section
open scoped TensorProduct
universe u v w

namespace Langlands.Global.AdelicFunctoriality

/-- Determinant norms commute with scalar extension from a field. -/
theorem norm_baseChange {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Module.Finite K B] (x : B) :
    Algebra.norm A (1 ⊗ₜ[K] x : A ⊗[K] B) = algebraMap K A (Algebra.norm K x) := by
  classical
  let b := Module.finBasis K B
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul,
    ← LinearMap.det_toMatrix (Algebra.TensorProduct.basis A b),
    LinearMap.toMatrix_baseChange]
  simpa only [RingHom.mapMatrix_apply, LinearMap.det_toMatrix, Algebra.norm_apply] using
    ((algebraMap K A).map_det (LinearMap.toMatrix b b (Algebra.lmul K B x))).symm

/-- The norm of an element of a product algebra is the product of its norms. -/
theorem norm_prod {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Module.Finite K A] [Module.Finite K B] (x : A × B) :
    Algebra.norm K x = Algebra.norm K x.1 * Algebra.norm K x.2 := by
  simp only [Algebra.norm_apply]
  have h : Algebra.lmul K (A × B) x =
      (Algebra.lmul K A x.1).prodMap (Algebra.lmul K B x.2) := by
    ext y <;> rfl
  rw [h, LinearMap.det_prodMap]

/-- The determinant norm of a dependent finite product algebra. -/
theorem norm_pi (K : Type u) [Field K] (ι : Type v) [Fintype ι]
    (B : ι → Type w) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    [∀ i, Module.Finite K (B i)] (x : ∀ i, B i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  classical
  revert B
  refine Fintype.induction_empty_option (P := fun ι _ =>
    ∀ (B : ι → Type w) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
      [∀ i, Module.Finite K (B i)] (x : ∀ i, B i),
      Algebra.norm K x = ∏ i, Algebra.norm K (x i)) ?_ ?_ ?_ ι
  · intro α β _ e ih B _ _ _ x
    let : Fintype α := Fintype.ofEquiv β e.symm
    let e' := (AlgEquiv.piCongrLeft K B e).symm
    calc
      Algebra.norm K x = Algebra.norm K (e' x) :=
        (Algebra.norm_eq_of_algEquiv e' x).symm
      _ = ∏ i, Algebra.norm K (x (e i)) := ih _ _
      _ = ∏ i, Algebra.norm K (x i) := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro B _ _ _ x
    have hx : x = 1 := Subsingleton.elim _ _
    simp [hx]
  · intro α _ ih B _ _ _ x
    let e : ((i : Option α) → B i) ≃ₐ[K] B none × ((i : α) → B (some i)) :=
      { Equiv.piOptionEquivProd with
        map_add' := fun _ _ => rfl
        map_mul' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    calc
      Algebra.norm K x = Algebra.norm K (e x) :=
        (Algebra.norm_eq_of_algEquiv e x).symm
      _ = Algebra.norm K (x none) * Algebra.norm K (fun i => x (some i)) :=
        norm_prod _
      _ = Algebra.norm K (x none) * ∏ i, Algebra.norm K (x (some i)) := by
        rw [ih]
      _ = ∏ i, Algebra.norm K (x i) :=
        (Fintype.prod_option (fun i => Algebra.norm K (x i))).symm

/-- A specified tensor decomposition transports the norm to a product of norms. -/
theorem norm_tensor_pi {K A B : Type*} [Field K] [Field A] [CommRing B]
    [Algebra K A] [Algebra K B] [Module.Finite K B]
    {ι : Type*} [Fintype ι] (C : ι → Type*)
    [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)] [∀ i, Module.Finite A (C i)]
    (e : A ⊗[K] B ≃ₐ[A] ∀ i, C i) (x : B) :
    (∏ i, Algebra.norm A (e (1 ⊗ₜ[K] x) i)) = algebraMap K A (Algebra.norm K x) := by
  rw [← norm_pi A ι C, Algebra.norm_eq_of_algEquiv e, norm_baseChange]

open NumberField IsDedekindDomain
open scoped NumberField

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

section Infinite

open scoped NumberField.LiesOver InfiniteExtension

/-- The product formula for a principal element at every infinite place. -/
theorem infiniteNorm_principal (p : InfinitePlace K) (x : L) :
    (∏ q : InfinitePlacesAbove L p,
      InfiniteExtension.localNorm p q.1 (algebraMap L q.1.Completion x)) =
        algebraMap K p.Completion (Algebra.norm K x) := by
  simpa only [infiniteTensorEquiv_apply, infiniteTensorMap_one_tmul,
    InfiniteExtension.localNorm] using
    norm_tensor_pi (fun q : InfinitePlacesAbove L p => q.1.Completion)
      (infiniteTensorEquiv p) x

end Infinite

section Finite

open scoped FiniteExtension

/-- The finite-place formula, conditional on the canonical comparison being bijective. -/
theorem finiteNorm_principal_of_bijective (p : HeightOneSpectrum (𝓞 K))
    (hp : Function.Bijective (finiteTensorMap (L := L) p)) (x : L) :
    (∏ q : FinitePlacesAbove L p,
      FiniteExtension.localNorm p q.1 (algebraMap L (q.1.adicCompletion L) x)) =
        algebraMap K (p.adicCompletion K) (Algebra.norm K x) := by
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := L) p) hp
  have he (z) : e z = finiteTensorMap p z := rfl
  simpa only [he, finiteTensorMap_one_tmul, FiniteExtension.localNorm] using
    norm_tensor_pi (fun q : FinitePlacesAbove L p => q.1.adicCompletion L) e x

end Finite

/-- The full diagonal formula reduced to the finite-place tensor decompositions. -/
theorem adeleNorm_principal_of_finiteTensorMap_bijective
    (h : ∀ p : HeightOneSpectrum (𝓞 K), Function.Bijective (finiteTensorMap (L := L) p))
    (x : L) :
    adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x) := by
  apply Prod.ext
  · funext p
    exact infiniteNorm_principal p x
  · apply FiniteAdeleRing.ext
    intro p
    exact finiteNorm_principal_of_bijective p (h p) x

/-- The tensor comparison target implies the principal norm target. -/
theorem principalNormCompatibility_of_completedTensorComparison
    (h : CompletedTensorComparison.{u, v}) : PrincipalNormCompatibility.{u, v} := by
  intro K L _ _ _ _ _ x
  exact adeleNorm_principal_of_finiteTensorMap_bijective (h K L).1 x

end Langlands.Global.AdelicFunctoriality
