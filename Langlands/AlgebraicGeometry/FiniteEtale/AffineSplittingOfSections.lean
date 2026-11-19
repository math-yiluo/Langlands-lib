import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberConservativeProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionMaps
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Etale.Pi

/-! # Splitting a finite étale algebra by sections through a geometric fibre -/

noncomputable section

universe u

open CategoryTheory _root_.AlgebraicGeometry
open Function
open scoped BigOperators

namespace Langlands.AlgebraicGeometry.FiniteEtale

open PointTopology

private def affineCover (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] : Cover (Spec (.of R)) :=
  ⟨ringTest R A,
    by
      change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      exact (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr inferInstance),
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.mpr inferInstance)⟩

private theorem bijective_of_precomp_bijective {R K A B : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [IsAlgClosed K]
    [Algebra R K] [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
    (f : A →ₐ[R] B) (hf : Bijective (fun p : B →ₐ[R] K => p.comp f)) :
    Bijective f := by
  let s := Spec.algebraMap R K
  let XA := affineCover R A
  let XB := affineCover R B
  let g : XB ⟶ XA := ObjectProperty.homMk (ringTestMap R f)
  let hfin := geometricFiberFinite s
  let eA : Fiber s XA ≃ (A →ₐ[R] K) := affineRingPointEquiv R A K
  let eB : Fiber s XB ≃ (B →ₐ[R] K) := affineRingPointEquiv R B K
  have : IsIso ((fiberFunctor s hfin).map g) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Bijective (fun p : Fiber s XB => p ≫ ringTestMap R f)
    have h (p : Fiber s XB) :
        p ≫ ringTestMap R f = eA.symm ((eB p).comp f) := by
      apply eA.injective
      rw [Equiv.apply_symm_apply]
      exact affineRingPointEquiv_postcomp_ringTestMap R f p
    rw [funext h]
    exact eA.symm.bijective.comp (hf.comp eB.bijective)
  let : (fiberFunctor s hfin).ReflectsIsomorphisms := geometricFiberConservative s hfin
  have : IsIso g := isIso_of_reflects_iso g (fiberFunctor s hfin)
  have : IsIso (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    change IsIso (((inclusion (Spec (.of R))) ⋙ Over.forget (Spec (.of R))).map g)
    infer_instance
  exact isIso_SpecMap_iff.mp (show IsIso (Spec.map (CommRingCat.ofHom f.toRingHom)) from inferInstance)

private theorem bijective_product_coordinates (R K I : Type*) [CommRing R] [Field K]
    [Algebra R K] [Fintype I] :
    Bijective (fun i : I => (Algebra.ofId R K).comp (Pi.evalAlgHom R (fun _ : I => R) i)) := by
  classical
  let e (i : I) : I → R := Pi.single i 1
  constructor
  · intro i j h
    by_contra hij
    have he := congrArg (fun p : (I → R) →ₐ[R] K => p (e i)) h
    change algebraMap R K (e i i) = algebraMap R K (e i j) at he
    simp [e, Ne.symm hij] at he
  · intro p
    have hsum : ∑ i : I, e i = 1 := by
      funext j
      simp [e, Finset.sum_apply, Pi.single_apply]
    have hex : ∃ i, p (e i) ≠ 0 := by
      by_contra! hn
      have h := congrArg p hsum
      rw [map_sum, map_one] at h
      simp [hn] at h
    obtain ⟨i, hi⟩ := hex
    have hei : IsIdempotentElem (e i) := by
      funext j
      change e i j * e i j = e i j
      by_cases h : j = i <;> simp [e, h]
    have hpi : p (e i) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.mp (hei.map p)).resolve_left hi
    refine ⟨i, AlgHom.ext fun a => ?_⟩
    change algebraMap R K (a i) = p a
    have hm : e i * a = e i * algebraMap R (I → R) (a i) := by
      funext j
      change e i j * a j = e i j * a i
      by_cases h : j = i <;> simp [e, h]
    simpa only [map_mul, hpi, one_mul, AlgHom.commutes] using (congrArg p hm).symm

/-- A field-valued point of a split algebra extends to a section. -/
theorem exists_section_of_algEquiv_pi {R K A : Type*}
    [CommRing R] [Field K] [Algebra R K] [CommRing A] [Algebra R A]
    {m : ℕ} (e : A ≃ₐ[R] (Fin m → R)) (p : A →ₐ[R] K) :
    ∃ φ : A →ₐ[R] R, (Algebra.ofId R K).comp φ = p := by
  obtain ⟨i, hi⟩ := (bijective_product_coordinates R K (Fin m)).surjective
    (p.comp e.symm.toAlgHom)
  refine ⟨(Pi.evalAlgHom R (fun _ : Fin m => R) i).comp e.toAlgHom, AlgHom.ext fun a => ?_⟩
  simpa using congrArg (fun f : (Fin m → R) →ₐ[R] K => f (e a)) hi

/-- A finite étale algebra splits if every point in one geometric fibre lifts to an
algebra section of its structural map. -/
theorem exists_algEquiv_pi_of_sections {R K A : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [IsAlgClosed K]
    [Algebra R K] [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    (h : ∀ p : A →ₐ[R] K, ∃ φ : A →ₐ[R] R, (Algebra.ofId R K).comp φ = p) :
    ∃ m : ℕ, Nonempty (A ≃ₐ[R] (Fin m → R)) := by
  classical
  let I := A →ₐ[R] K
  let : Finite (RingPoint R (ringTest R A) K) :=
    geometricFiberFinite (Spec.algebraMap R K) (affineCover R A)
  let : Finite I := Finite.of_equiv _ (affineRingPointEquiv R A K)
  let := Fintype.ofFinite I
  choose φ hφ using h
  let f : A →ₐ[R] (I → R) := AlgHom.pi φ
  let e := Equiv.ofBijective _ (bijective_product_coordinates R K I)
  have he : (fun p : (I → R) →ₐ[R] K => p.comp f) = e.symm := by
    funext p
    obtain ⟨i, rfl⟩ := e.surjective p
    rw [Equiv.symm_apply_apply]
    exact hφ i
  have hf : Bijective f := bijective_of_precomp_bijective f (he.symm ▸ e.symm.bijective)
  let reindex := AlgEquiv.piCongrLeft' R (fun _ : I => R) (Fintype.equivFin I)
  exact ⟨Fintype.card I, ⟨(AlgEquiv.ofBijective f hf).trans reindex⟩⟩

end Langlands.AlgebraicGeometry.FiniteEtale
