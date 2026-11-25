/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization
import Mathlib.RingTheory.Regular.Flat

/-! # Boundary depth transferred from a finite structure algebra

## References

* Stacks Project, Tag 0AUK, applied as in the proof of Tag 0EY6(2)
* Tag 0EY6, proof of (2)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- Linear equivalences preserve depth for every ideal, including infinite depth.
private theorem depth_equiv {R : Type*} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (e : M ≃ₗ[R] P) : I.depth M = I.depth P := by
  have hmap : (I • (⊤ : Submodule R M)).map e.toLinearMap =
      I • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have htop : (I • (⊤ : Submodule R M) = ⊤) ↔
      (I • (⊤ : Submodule R P) = ⊤) := by
    constructor
    · intro h
      rw [← hmap, h]
      simp
    · intro h
      rw [← hmap] at h
      exact (Submodule.map_eq_top_iff.mp h)
  unfold Ideal.depth
  split_ifs with hM hP hP
  · rfl
  · exact (hP (htop.mp hM)).elim
  · exact (hM (htop.mpr hP)).elim
  · congr 1
    ext n
    constructor
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mp hreg, hmem, rfl⟩
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mpr hreg, hmem, rfl⟩

-- A proper ideal does not generate the ring viewed as a module over itself.
private theorem ideal_smul_top_ne_top {A : Type*} [CommRing A]
    (I : Ideal A) (hI : I ≠ ⊤) : (I • (⊤ : Submodule A A)) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change I.map (algebraMap A A) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using hI

-- Ring equivalences transport depth along arbitrary proper ideals.
private theorem ideal_depth_le_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] (e : A ≃+* B) (I : Ideal A) (hI : I ≠ ⊤) :
    I.depth A ≤ (I.map e).depth B := by
  classical
  have hmap : I.map e ≠ ⊤ := by
    intro h
    apply hI
    have hh := congrArg (Ideal.comap e) h
    simpa only [Ideal.comap_map_of_bijective _ e.bijective, Ideal.comap_top] using hh
  simp only [Ideal.depth, ideal_smul_top_ne_top I hI,
    ideal_smul_top_ne_top (I.map e) hmap, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Ideal.mem_map_of_mem e (hmem a ha)

-- Only the lower bound in Tag 0AUK is needed: localize each regular sequence.
private theorem depth_le_localization {R B : Type*} [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = IsLocalRing.maximalIdeal R) :
    IsLocalRing.depth (R := R) B ≤
      IsLocalRing.depth (R := Localization.AtPrime q) (Localization.AtPrime q) := by
  classical
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ q :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hq.symm)
  have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R B) ≠ ⊤ := by
    rw [Ideal.smul_top_eq_map]
    intro h
    have h1 : (1 : B) ∈
        ((IsLocalRing.maximalIdeal R).map (algebraMap R B)).restrictScalars R := by
      rw [h]
      trivial
    exact (inferInstance : q.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ (hmap h1) isUnit_one)
  unfold IsLocalRing.depth Ideal.depth
  rw [ite_eq_right hproper]
  split_ifs with hlocal
  · exact le_top
  · apply sSup_le
    rintro n ⟨rs, hreg, hmem, rfl⟩
    let ss := rs.map (algebraMap R B)
    have hss : RingTheory.Sequence.IsWeaklyRegular B ss :=
      (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff B B rs).mpr hreg.1
    have hmemq : ∀ b ∈ ss, b ∈ q := by
      intro b hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      change r ∈ q.comap (algebraMap R B)
      rw [hq]
      exact hmem r hr
    have hloc := hss.isRegular_of_isLocalization_of_mem (Localization.AtPrime q) q hmemq
    apply le_sSup
    refine ⟨ss.map (algebraMap B (Localization.AtPrime q)), hloc, ?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime q) q a).mpr (hmemq a ha)
    · simp [ss]

-- The canonical map from the affine pushforward stalk to a source stalk is a localization.
private theorem pushforward_stalk_localization
    {E L : Scheme.{u}} (p : E ⟶ L) [IsAffineHom p] (z : E) :
    let F := (TopCat.Presheaf.pushforward CommRingCat p.base).obj E.presheaf
    ∃ q : PrimeSpectrum (F.stalk (p z)),
      q.asIdeal.comap ((TopCat.Presheaf.stalkFunctor CommRingCat (p z)).map p.c).hom =
        IsLocalRing.maximalIdeal (L.presheaf.stalk (p z)) ∧
      Nonempty (Localization.AtPrime q.asIdeal ≃+* E.presheaf.stalk z) := by
  let F := (TopCat.Presheaf.pushforward CommRingCat p.base).obj E.presheaf
  let B := F.stalk (p z)
  let T := E.presheaf.stalk z
  let g : B →+* T := (TopCat.Presheaf.stalkPushforward CommRingCat p.base E.presheaf z).hom
  let : Algebra B T := g.toAlgebra
  let q : Ideal B := (IsLocalRing.maximalIdeal T).comap g
  have : q.IsPrime := Ideal.IsPrime.comap g
  refine ⟨⟨q, inferInstance⟩, ?_, ?_⟩
  · change Ideal.comap _ (Ideal.comap g (IsLocalRing.maximalIdeal T)) = _
    rw [Ideal.comap_comap]
    exact IsLocalRing.maximalIdeal_comap (p.stalkMap z).hom
  · obtain ⟨U, hU, hzU, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := L) (x := p z) (U := ⊤) (by trivial)
    let S := E.presheaf.obj (Opposite.op (p ⁻¹ᵁ U))
    let : Algebra S B := (F.germ U (p z) hzU).hom.toAlgebra
    let : Algebra S T := (E.presheaf.germ (p ⁻¹ᵁ U) z hzU).hom.toAlgebra
    have : IsScalarTower S B T := IsScalarTower.of_algebraMap_eq' <| by
      ext a
      exact (TopCat.Presheaf.stalkPushforward_germ_apply
        CommRingCat p.base E.presheaf U z hzU a).symm
    let M := (hU.primeIdealOf ⟨p z, hzU⟩).asIdeal.primeCompl.map (p.app U).hom
    let N := ((hU.preimage p).primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
    have : IsLocalization M B := affine_pushforward_stalk_isLocalization p hU ⟨p z, hzU⟩
    have : IsLocalization N T := (hU.preimage p).isLocalization_stalk ⟨z, hzU⟩
    have hMN : M ≤ N := by
      intro a ha
      have hu := (IsLocalization.map_units B ⟨a, ha⟩).map g
      change IsUnit (algebraMap B T (algebraMap S B a)) at hu
      have hunit : IsUnit (algebraMap S T a) := by
        rw [IsScalarTower.algebraMap_apply S B T]
        exact hu
      exact (IsLocalization.AtPrime.isUnit_to_map_iff T _ a).mp hunit
    have : IsLocalization (N.map (algebraMap S B)) T :=
      IsLocalization.isLocalization_of_submonoid_le B T M N hMN
    have hNq : N.map (algebraMap S B) ≤ q.primeCompl := by
      rintro _ ⟨a, ha, rfl⟩
      change g (algebraMap S B a) ∉ IsLocalRing.maximalIdeal T
      apply IsLocalRing.notMem_maximalIdeal.mpr
      change IsUnit (algebraMap B T (algebraMap S B a))
      rw [← IsScalarTower.algebraMap_apply S B T]
      exact IsLocalization.map_units T ⟨a, ha⟩
    have : IsLocalization.AtPrime T q :=
      IsLocalization.of_le (N.map (algebraMap S B)) q.primeCompl hNq fun b hb ↦
        IsLocalRing.notMem_maximalIdeal.mp hb
    exact ⟨(IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) T).toRingEquiv⟩

/-- Depth two of the stalks of a finite direct image algebra implies depth two
at the points of its relative spectrum above those stalks. -/
theorem depth_two_of_finite_structure_algebra
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (A : L.CommAlgebraSheaf)
    (hdepth : ∀ y : L, y ∉ U →
      letI : Algebra (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj A.right.obj) :=
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map A.hom.hom).hom.toAlgebra
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj A.right.obj),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj A.right.obj))
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p]
    (α : A ≅ Under.mk
      (⟨p.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj E.sheaf)) :
    ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z) := by
  intro z hz
  let R := L.presheaf.stalk (p z)
  let F := (TopCat.Presheaf.pushforward CommRingCat p.base).obj E.presheaf
  let B := F.stalk (p z)
  let C := (TopCat.Presheaf.stalkFunctor CommRingCat (p z)).obj A.right.obj
  let : Algebra R C :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat (p z)).map A.hom.hom).hom.toAlgebra
  let : Algebra R B :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat (p z)).map p.c).hom.toAlgebra
  obtain ⟨hfinite, hd⟩ := hdepth (p z) hz
  let := hfinite
  let β := (TopCat.Presheaf.stalkFunctor CommRingCat (p z)).mapIso
    ((TopCat.Sheaf.forget CommRingCat L.toTopCat).mapIso ((Under.forget L.sheaf).mapIso α))
  let e : C ≃+* B := β.commRingCatIsoToRingEquiv
  have he (r : R) : e (algebraMap R C r) = algebraMap R B r := by
    have hw : A.hom.hom ≫ α.hom.right.hom = p.c :=
      congrArg (fun f ↦ f.hom) (Under.w α.hom)
    have hw' := congrArg (fun f ↦
      (TopCat.Presheaf.stalkFunctor CommRingCat (p z)).map f) hw
    rw [Functor.map_comp] at hw'
    exact congrArg (fun f ↦ f r) hw'
  let eA : C ≃ₐ[R] B := { e with commutes' := he }
  have : Module.Finite R B := Module.Finite.equiv eA.toLinearEquiv
  have hdB : (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) B :=
    hd.trans_eq (depth_equiv (IsLocalRing.maximalIdeal R) eA.toLinearEquiv)
  obtain ⟨q, hq, ⟨eT⟩⟩ := pushforward_stalk_localization p z
  have hdT : IsLocalRing.depth (R := Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) ≤
      IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z) := by
    simpa only [IsLocalRing.depth, IsLocalRing.map_ringEquiv_maximalIdeal] using
      ideal_depth_le_of_ringEquiv eT _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  exact (hdB.trans (depth_le_localization q.asIdeal hq)).trans hdT

end AlgebraicGeometry.Scheme
