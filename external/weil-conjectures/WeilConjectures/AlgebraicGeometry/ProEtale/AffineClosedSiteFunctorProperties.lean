/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
import WeilConjectures.RingTheory.ProEtale.ClosedLiftAdjunction
import WeilConjectures.RingTheory.ProEtale.ClosedLiftUnits

/-! # Affine closed-immersion site functor properties

The functors are the recorded `closedSiteBaseChange` and `closedSiteLift`.
The geometric inclusion below is the spectrum of the retained algebra map.

## References

* Stacks Project, Tag 09BK, the map V → v(V)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The canonical map from an affine object of the closed site to its lift. -/
def closedSiteLiftInclusion (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    V.left ⟶ ((closedSiteLift A I).obj V).left :=
  V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    (Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I V)).toRingHom)

private noncomputable instance coordinatesQuotientAlgebra (A : Type u) [CommRing A]
    (I : Ideal A) (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    Algebra (A ⧸ I) (closedSiteCoordinates A I V) :=
  ((Scheme.ΓSpecIso (.of (A ⧸ I))).inv ≫ V.hom.appTop).hom.toAlgebra

private theorem coordinates_tower (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    IsScalarTower A (A ⧸ I) (closedSiteCoordinates A I V) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change (((Scheme.ΓSpecIso (.of A)).inv ≫
    (V.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop).hom) a = _
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem coordinates_indEtale (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    Algebra.IndEtale (A ⧸ I) (closedSiteCoordinates A I V) := by
  have : IsAffine V.left := inferInstance
  change (((Scheme.ΓSpecIso (.of (A ⧸ I))).inv ≫ V.hom.appTop).hom).IndEtale
  apply RingHom.IndEtale.comp
  · exact indEtale_appTop_of_proAffineEtale (X := V.left) (Y := Spec (.of (A ⧸ I))) V.prop
  · exact (proAffineEtale_Spec_iff (f := (Scheme.ΓSpecIso (.of (A ⧸ I))).inv)).mp
      (proAffineEtale.of_isAffine _)

private theorem lift_specializes (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C] (x : PrimeSpectrum (Algebra.ClosedLift A C)) :
    ∃ z : PrimeSpectrum C,
      x ⤳ PrimeSpectrum.comap (Algebra.ClosedLift.toAlgHom A C).toRingHom z := by
  let ε := (Algebra.ClosedLift.toAlgHom A C).toRingHom
  obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal x.asIdeal x.isPrime.ne_top
  have hker : RingHom.ker ε ≤ m := by
    intro b hb
    have hj : b ∈ Ideal.jacobson (⊥ : Ideal (Algebra.ClosedLift A C)) := by
      rw [Ideal.mem_jacobson_bot]
      intro y
      apply Algebra.ClosedLift.isUnit_of_isUnit_toAlgHom I
      have hb0 : Algebra.ClosedLift.toAlgHom A C b = 0 := hb
      simpa only [map_add, map_mul, map_one, hb0,
        zero_mul, zero_add] using isUnit_one (M := C)
    exact (show Ideal.jacobson (⊥ : Ideal (Algebra.ClosedLift A C)) ≤ m from
      sInf_le ⟨bot_le, hm⟩) hj
  have hr : (⟨m, hm.isPrime⟩ : PrimeSpectrum (Algebra.ClosedLift A C)) ∈
      Set.range (PrimeSpectrum.comap ε) := by
    rw [range_comap_of_surjective C ε (Algebra.ClosedLift.surjective_toAlgHom A C I)]
    exact hker
  obtain ⟨z, hz⟩ := hr
  refine ⟨z, ?_⟩
  rw [hz, ← PrimeSpectrum.le_iff_specializes]
  exact hxm

private theorem lift_isPushout (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C] :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (algebraMap A (Algebra.ClosedLift A C)))
      (CommRingCat.ofHom (algebraMap (A ⧸ I) C))
      (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom A C).toRingHom) := by
  let e := (RingEquiv.ofBijective (Algebra.ClosedLift.reduction A C I)
    (Algebra.ClosedLift.bijective_reduction A C I)).toCommRingCatIso
  refine (CommRingCat.isPushout_quotient
    (CommRingCat.ofHom (algebraMap A (Algebra.ClosedLift A C))) I).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Algebra.ClosedLift.toAlgHom A C
      (algebraMap A (Algebra.ClosedLift A C) a) = algebraMap (A ⧸ I) C _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) C]
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
private theorem inclusion_pullback (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    IsPullback (closedSiteLiftInclusion A I V) V.hom
      ((closedSiteLift A I).obj V).hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  have : IsAffine V.left := inferInstance
  have := coordinates_tower A I V
  have := coordinates_indEtale A I V
  have h := (isPullback_SpecMap_of_isPushout _ _ _ _
    (lift_isPushout A (closedSiteCoordinates A I V) I)).flip
  refine h.of_iso' V.left.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [closedSiteLiftInclusion]) ?_ (by simp; rfl) (by simp)
  change V.left.isoSpec.hom ≫ Spec.map
    ((Scheme.ΓSpecIso (.of (A ⧸ I))).inv ≫ V.hom.appTop) = V.hom ≫ 𝟙 _
  rw [Spec.map_comp, ← Category.assoc,
    Scheme.isoSpec_hom_naturality (X := V.left) (Y := Spec (.of (A ⧸ I))) V.hom,
    Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id, Category.comp_id]

private theorem inclusion_specializes (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (x : ((closedSiteLift A I).obj V).left) :
    ∃ z : V.left, x ⤳ (closedSiteLiftInclusion A I V) z := by
  have := coordinates_tower A I V
  have := coordinates_indEtale A I V
  obtain ⟨z, hz⟩ := lift_specializes A (closedSiteCoordinates A I V) I x
  refine ⟨V.left.isoSpec.inv z, ?_⟩
  have he : V.left.isoSpec.hom (V.left.isoSpec.inv z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  change (x : PrimeSpectrum _) ⤳ PrimeSpectrum.comap
    (Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I V)).toRingHom
    (V.left.isoSpec.hom (V.left.isoSpec.inv z))
  rwa [he]

private theorem inclusion_closed (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    IsClosedImmersion (closedSiteLiftInclusion A I V) := by
  have := coordinates_tower A I V
  have := coordinates_indEtale A I V
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I V)).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (Algebra.ClosedLift.surjective_toAlgHom A _ I)
  unfold closedSiteLiftInclusion
  infer_instance

private theorem inclusion_naturality (A : Type u) [CommRing A] (I : Ideal A)
    {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) :
    closedSiteLiftInclusion A I V ≫ ((closedSiteLift A I).map f).left =
      f.left ≫ closedSiteLiftInclusion A I W := by
  change (V.left.isoSpec.hom ≫ Spec.map _) ≫ Spec.map _ = _
  rw [Category.assoc, ← Spec.map_comp]
  have hn := Algebra.ClosedLift.toAlgHom_map (closedSiteCoordinatesMap A I f)
  have he : CommRingCat.ofHom
      ((Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I V)).comp
        (Algebra.ClosedLift.map (closedSiteCoordinatesMap A I f))).toRingHom =
      CommRingCat.ofHom
        ((closedSiteCoordinatesMap A I f).comp
          (Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I W))).toRingHom :=
    congrArg (fun φ ↦ CommRingCat.ofHom φ.toRingHom) hn
  change V.left.isoSpec.hom ≫ Spec.map
    (CommRingCat.ofHom ((Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I V)).comp
      (Algebra.ClosedLift.map (closedSiteCoordinatesMap A I f))).toRingHom) = _
  rw [he]
  change V.left.isoSpec.hom ≫ Spec.map
    (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I W)).toRingHom ≫
      f.left.appTop) = _
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc]
  rfl

private theorem finite_covers {S : Scheme.{u}} {U : S.AffineProEt}
    {ι : Type*} [Finite ι] (Z : ι → S.AffineProEt) (f : ∀ i, Z i ⟶ U)
    (hsurj : ∀ x : U.left, ∃ i, x ∈ Set.range (f i).left.base) :
    Presieve.ofArrows Z f ∈ precoverage U := by
  let D : PreZeroHypercover U.left := ⟨ι, fun i ↦ (Z i).left, fun i ↦ (f i).left⟩
  have : ∀ i, QuasiCompact (D.f i) := fun i ↦ inferInstance
  have hD : QuasiCompactCover D :=
    ⟨fun {W} hW ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun i ↦ (D.f i).isSpectralMap) (fun x _ ↦ hsurj x) W.2 hW.isCompact⟩
  change (Presieve.ofArrows Z f).map
    (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) ∈ Scheme.proetalePrecoverage U.left
  rw [Presieve.map_ofArrows]
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hD,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mpr
      ⟨hsurj, fun i ↦ inferInstanceAs (WeaklyEtale (f i).left)⟩⟩

private theorem finite_subfamily {S : Scheme.{u}} {U : S.AffineProEt}
    {ι : Type*} (Z : ι → S.AffineProEt) (f : ∀ i, Z i ⟶ U)
    (hf : Presieve.ofArrows Z f ∈ precoverage U) :
    ∃ (n : ℕ) (a : Fin n → ι),
      ∀ x : U.left, ∃ i, x ∈ Set.range (f (a i)).left.base := by
  let D : PreZeroHypercover U.left := ⟨ι, fun i ↦ (Z i).left, fun i ↦ (f i).left⟩
  have hD : QuasiCompactCover D := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    change (Presieve.ofArrows Z f).map
      (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) ∈ Scheme.proetalePrecoverage U.left at hf
    rw [Presieve.map_ofArrows] at hf
    exact hf.1
  have hc : IsCompact ((⊤ : U.left.Opens) : Set U.left) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set U.left))
  obtain ⟨n, a, W, hW, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact D hc
  refine ⟨n, a, fun x ↦ ?_⟩
  have hx : x ∈ ((⊤ : U.left.Opens) : Set U.left) := Set.mem_univ _
  rw [← hcov] at hx
  obtain ⟨i, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, y, hxy⟩

private theorem lift_jointlySurjective (A : Type u) [CommRing A] (I : Ideal A)
    {V : (Spec (.of (A ⧸ I))).AffineProEt} {ι : Type*}
    (Z : ι → (Spec (.of (A ⧸ I))).AffineProEt) (f : ∀ i, Z i ⟶ V)
    (hf : ∀ z : V.left, ∃ i, z ∈ Set.range (f i).left.base) :
    ∀ x : ((closedSiteLift A I).obj V).left,
      ∃ i, x ∈ Set.range ((closedSiteLift A I).map (f i)).left.base := by
  intro x
  obtain ⟨z, hxz⟩ := inclusion_specializes A I V x
  obtain ⟨i, w, hw⟩ := hf z
  have he : ((closedSiteLift A I).map (f i)).left
      (closedSiteLiftInclusion A I (Z i) w) = closedSiteLiftInclusion A I V z := by
    rw [← Scheme.Hom.comp_apply, inclusion_naturality, Scheme.Hom.comp_apply]
    rw [hw]
  rw [← he] at hxz
  obtain ⟨y, hxy, hy⟩ := Flat.generalizingMap
    (((closedSiteLift A I).map (f i)).left) hxz
  exact ⟨i, y, hy⟩

private theorem subfamily_covers {S : Scheme.{u}} {U : S.AffineProEt}
    {ι : Type*} (Z : ι → S.AffineProEt) (f : ∀ i, Z i ⟶ U)
    {κ : Type*} [Finite κ] (a : κ → ι)
    (hf : ∀ x : U.left, ∃ i, x ∈ Set.range (f (a i)).left.base) :
    Presieve.ofArrows Z f ∈ precoverage U := by
  let D : PreZeroHypercover U.left := ⟨ι, fun i ↦ (Z i).left, fun i ↦ (f i).left⟩
  let E : PreZeroHypercover U.left := ⟨κ, fun i ↦ (Z (a i)).left,
    fun i ↦ (f (a i)).left⟩
  have : ∀ i, QuasiCompact (E.f i) := fun i ↦ inferInstance
  have : QuasiCompactCover E :=
    ⟨fun {W} hW ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun i ↦ (E.f i).isSpectralMap) (fun x _ ↦ hf x) W.2 hW.isCompact⟩
  have hD : QuasiCompactCover D := QuasiCompactCover.of_hom (𝒱 := E)
    { s₀ := a, h₀ := fun i ↦ 𝟙 _, w₀ := fun i ↦ Category.id_comp _ }
  change (Presieve.ofArrows Z f).map
    (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) ∈ Scheme.proetalePrecoverage U.left
  rw [Presieve.map_ofArrows]
  refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hD,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mpr ⟨?_, ?_⟩⟩
  · intro x
    obtain ⟨i, hi⟩ := hf x
    exact ⟨a i, hi⟩
  · intro i
    exact inferInstanceAs (WeaklyEtale (f i).left)

private theorem lift_covers (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) (R : Presieve V)
    (hR : R ∈ precoverage V) :
    R.map (closedSiteLift A I) ∈ precoverage ((closedSiteLift A I).obj V) := by
  obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨n, a, ha⟩ := finite_subfamily Z f hR
  rw [Presieve.map_ofArrows]
  apply subfamily_covers _ _ a
  exact lift_jointlySurjective A I (fun i ↦ Z (a i)) (fun i ↦ f (a i)) ha

set_option backward.isDefEq.respectTransparency false in
private theorem generate_mem_topology {S : Scheme.{u}} {U : S.AffineProEt}
    {R : Presieve U} (hR : R ∈ precoverage U) :
    Sieve.generate R ∈ topology S U := by
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [← Sieve.generate_map_eq_functorPushforward]
  apply Precoverage.generate_mem_toGrothendieck
  change (R.map (toProEt S)).map (ProEt.forget S ⋙ Over.forget S) ∈
    Scheme.proetalePrecoverage U.left
  change R.map (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) ∈
    Scheme.proetalePrecoverage U.left at hR
  simpa only [Presieve.map_comp] using hR

private theorem baseChange_covers (A : Type u) [CommRing A] (I : Ideal A)
    (U : (Spec (.of A)).AffineProEt) (R : Presieve U) (hR : R ∈ precoverage U) :
    R.map (closedSiteBaseChange A I) ∈ precoverage ((closedSiteBaseChange A I).obj U) := by
  obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
  simp only [precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Functor.comp_map, toProEt_map, ProEt.forget_map, Over.forget_map] at hR ⊢
  exact Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hR
    (pullback.fst U.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) _
    (fun i ↦ pullback.fst (Z i).hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (fun i ↦ (MorphismProperty.Over.isPullback_map_left
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (f i)).flip)

private theorem retained_comp_bijective (A : Type u) [CommRing A] (I : Ideal A)
    (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale A D] [Algebra.IndEtale (A ⧸ I) C] :
    Function.Bijective (fun f : D →ₐ[A] Algebra.ClosedLift A C ↦
      (Algebra.ClosedLift.toAlgHom A C).comp f) := by
  obtain ⟨β, hβ⟩ := Algebra.ClosedLift.exists_natural_homEquiv A I
  have hβ := (hβ D C).2.1
  constructor
  · intro f g hfg
    apply (β D C).injective
    ext q
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hβ, hβ]
    exact DFunLike.congr_fun hfg d
  · intro f
    have hkill : I.map (algebraMap A D) ≤ RingHom.ker f.toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change f (algebraMap A D a) = 0
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) C,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    let f' : @AlgHom (A ⧸ I) (D ⧸ I.map (algebraMap A D)) C _ _ _
        (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) _ :=
      { Ideal.Quotient.lift _ f.toRingHom hkill with
        commutes' := by
          intro a
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
          change f (algebraMap A D a) = algebraMap (A ⧸ I) C (Ideal.Quotient.mk I a)
          rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) C]
          rfl }
    refine ⟨(β D C).symm f', ?_⟩
    ext d
    have he := (β D C).apply_symm_apply f'
    have hv := DFunLike.congr_fun he (Ideal.Quotient.mk _ d)
    rw [hβ] at hv
    exact hv

private def affineCoordinates (A : Type u) [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) : CommAlgCat.{u} A :=
  @CommAlgCat.of A _ Γ(X, ⊤) _
    (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra)

private theorem affineCoordinates_structure (A : Type u) [CommRing A] (X : Scheme.{u})
    [IsAffine X] (f : X ⟶ Spec (.of A)) :
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (affineCoordinates A X f))) =
      f := by
  change X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

private def affineCoordinatesHomEquiv (A : Type u) [CommRing A] (C : CommAlgCat.{u} A)
    {X Y : Scheme.{u}} [IsAffine Y] (e : X ≅ Spec (.of C))
    (x : X ⟶ Spec (.of A)) (y : Y ⟶ Spec (.of A))
    (hx : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = x) :
    {f : X ⟶ Y // f ≫ y = x} ≃
      (affineCoordinates A Y y →ₐ[A] C) where
  toFun f :=
    { (Spec.preimage (e.inv ≫ f.val ≫ Y.isoSpec.hom)).hom with
      commutes' := by
        intro a
        have h : CommRingCat.ofHom (algebraMap A (affineCoordinates A Y y)) ≫
            Spec.preimage (e.inv ≫ f.val ≫ Y.isoSpec.hom) =
            CommRingCat.ofHom (algebraMap A C) := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage, Category.assoc, Category.assoc,
            affineCoordinates_structure, f.property,
            ← cancel_epi e.hom, Iso.hom_inv_id_assoc,
            hx]
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a }
  invFun φ := ⟨e.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.isoSpec.inv, by
    have hy : Y.isoSpec.inv ≫ y =
        Spec.map (CommRingCat.ofHom (algebraMap A (affineCoordinates A Y y))) := by
      apply (cancel_epi Y.isoSpec.hom).mp
      simpa only [Iso.hom_inv_id_assoc] using (affineCoordinates_structure A Y y).symm
    rw [Category.assoc, Category.assoc, hy, ← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap A (affineCoordinates A Y y)) ≫
        CommRingCat.ofHom φ.toRingHom =
        CommRingCat.ofHom (algebraMap A C) := by
      ext a
      exact φ.commutes a
    rw [he, hx]⟩
  left_inv := by
    intro f
    apply Subtype.ext
    change e.hom ≫ Spec.map (Spec.preimage
      (e.inv ≫ f.val ≫ Y.isoSpec.hom)) ≫ Y.isoSpec.inv = f.val
    simp
  right_inv := by
    intro φ
    apply AlgHom.ext
    intro d
    have he : Spec.preimage (e.inv ≫
        (e.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.isoSpec.inv) ≫
          Y.isoSpec.hom) = CommRingCat.ofHom φ.toRingHom := by
      simp
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) d

private theorem affineCoordinates_indEtale (A : Type u) [CommRing A]
    (U : (Spec (.of A)).AffineProEt) : Algebra.IndEtale A (affineCoordinates A U.left U.hom) := by
  have : IsAffine U.left := inferInstance
  change (((Scheme.ΓSpecIso (.of A)).inv ≫ U.hom.appTop).hom).IndEtale
  apply RingHom.IndEtale.comp
  · exact indEtale_appTop_of_proAffineEtale (X := U.left) (Y := Spec (.of A)) U.prop
  · exact (proAffineEtale_Spec_iff (f := (Scheme.ΓSpecIso (.of A)).inv)).mp
      (proAffineEtale.of_isAffine _)

private def inclusionComp (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) (U : (Spec (.of A)).AffineProEt)
    (f : {f : ((closedSiteLift A I).obj V).left ⟶ U.left //
      f ≫ U.hom = ((closedSiteLift A I).obj V).hom}) :
    {f : V.left ⟶ U.left // f ≫ U.hom =
      V.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))} :=
  ⟨closedSiteLiftInclusion A I V ≫ f.val, by
    rw [Category.assoc, f.property, (inclusion_pullback A I V).w]⟩

private theorem inclusionComp_bijective (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) (U : (Spec (.of A)).AffineProEt) :
    Function.Bijective (inclusionComp A I V U) := by
  have := coordinates_tower A I V
  have := coordinates_indEtale A I V
  have := affineCoordinates_indEtale A U
  let C := closedSiteCoordinates A I V
  let H := CommAlgCat.of A (Algebra.ClosedLift A C)
  let e₁ := affineCoordinatesHomEquiv A H (Y := U.left) (Iso.refl _)
    ((closedSiteLift A I).obj V).hom U.hom (by rfl)
  let e₂ := affineCoordinatesHomEquiv A C (Y := U.left) V.left.isoSpec
    (V.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) U.hom
    (affineCoordinates_structure A V.left _)
  have hbij := e₂.symm.bijective.comp
    ((retained_comp_bijective A I (affineCoordinates A U.left U.hom) C).comp e₁.bijective)
  suffices he : inclusionComp A I V U = e₂.symm ∘
      (fun f ↦ (Algebra.ClosedLift.toAlgHom A C).comp f) ∘ e₁ from he.symm ▸ hbij
  funext f
  obtain ⟨φ, rfl⟩ := e₁.symm.surjective f
  simp only [Function.comp_apply, e₁.apply_symm_apply]
  apply Subtype.ext
  change (V.left.isoSpec.hom ≫ Spec.map
      (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom A C).toRingHom)) ≫
      (𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.left.isoSpec.inv) =
    V.left.isoSpec.hom ≫ Spec.map
      (CommRingCat.ofHom ((Algebra.ClosedLift.toAlgHom A C).comp φ).toRingHom) ≫
      U.left.isoSpec.inv
  rw [show CommRingCat.ofHom ((Algebra.ClosedLift.toAlgHom A C).comp φ).toRingHom =
    CommRingCat.ofHom φ.toRingHom ≫
      CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom A C).toRingHom from rfl,
    Spec.map_comp]
  simp only [Category.id_comp, Category.assoc]

private def siteHomMap (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) (U : (Spec (.of A)).AffineProEt)
    (f : (closedSiteLift A I).obj V ⟶ U) : V ⟶ (closedSiteBaseChange A I).obj U :=
  MorphismProperty.Over.homMk
    (pullback.lift (closedSiteLiftInclusion A I V ≫ f.left) V.hom (by
      rw [Category.assoc, MorphismProperty.Over.w f, (inclusion_pullback A I V).w]))
    (by simp [closedSiteBaseChange, MorphismProperty.Over.pullback])

private theorem siteHomMap_bijective (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) (U : (Spec (.of A)).AffineProEt) :
    Function.Bijective (siteHomMap A I V U) := by
  constructor
  · intro f g hfg
    apply MorphismProperty.Over.Hom.ext
    have hf := congrArg (fun k ↦ k.left ≫ pullback.fst U.hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) hfg
    change pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫ _ at hf
    simp only [pullback.lift_fst] at hf
    have he := (inclusionComp_bijective A I V U).injective
      (a₁ := ⟨f.left, MorphismProperty.Over.w f⟩)
      (a₂ := ⟨g.left, MorphismProperty.Over.w g⟩) (Subtype.ext hf)
    exact congrArg Subtype.val he
  · intro g
    let f₀ := g.left ≫ pullback.fst U.hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    have hf₀ : f₀ ≫ U.hom = V.hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      dsimp [f₀]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (g.left ≫ ((closedSiteBaseChange A I).obj U).hom) ≫ _ = _
      rw [MorphismProperty.Over.w g]
    obtain ⟨f, hf⟩ := (inclusionComp_bijective A I V U).surjective ⟨f₀, hf₀⟩
    refine ⟨MorphismProperty.Over.homMk f.val f.property, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_fst]
      exact congrArg Subtype.val hf
    · change _ = g.left ≫ ((closedSiteBaseChange A I).obj U).hom
      change pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_snd, MorphismProperty.Over.w g]

private theorem siteHomMap_naturality_left (A : Type u) [CommRing A] (I : Ideal A)
    {V W : (Spec (.of (A ⧸ I))).AffineProEt} {U : (Spec (.of A)).AffineProEt}
    (f : V ⟶ W) (g : (closedSiteLift A I).obj W ⟶ U) :
    siteHomMap A I V U ((closedSiteLift A I).map f ≫ g) =
      f ≫ siteHomMap A I W U g := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change pullback.lift _ _ _ ≫ _ =
      (f.left ≫ pullback.lift _ _ _) ≫ _
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    change closedSiteLiftInclusion A I V ≫
      ((closedSiteLift A I).map f).left ≫ g.left = _
    rw [← Category.assoc, inclusion_naturality, Category.assoc]
  · change pullback.lift _ _ _ ≫ _ =
      (f.left ≫ pullback.lift _ _ _) ≫ _
    rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact (MorphismProperty.Over.w f).symm

private theorem siteHomMap_naturality_right (A : Type u) [CommRing A] (I : Ideal A)
    {V : (Spec (.of (A ⧸ I))).AffineProEt} {U W : (Spec (.of A)).AffineProEt}
    (f : (closedSiteLift A I).obj V ⟶ U) (g : U ⟶ W) :
    siteHomMap A I V W (f ≫ g) =
      siteHomMap A I V U f ≫ (closedSiteBaseChange A I).map g := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change pullback.lift _ _ _ ≫ _ = (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ _
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
    rfl
  · change pullback.lift _ _ _ ≫ _ = (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ _
    rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

/-- The affine closed-site lift is a fully faithful cocontinuous left adjoint,
preserves covering families, and contains its input as its closed fibre, with every
point specializing to that fibre. -/
theorem affine_closed_site_functor_properties (A : Type u) [CommRing A] (I : Ideal A) :
    (∀ (U : (Spec (.of A)).AffineProEt) (R : Presieve U),
      R ∈ precoverage U →
      R.map (closedSiteBaseChange A I) ∈ precoverage ((closedSiteBaseChange A I).obj U)) ∧
    (∀ (U T W : (Spec (.of A)).AffineProEt) (R : Presieve U),
      R ∈ precoverage U →
      ∀ (f : T ⟶ U) (g : W ⟶ U), R f →
        PreservesLimit (cospan f g) (closedSiteBaseChange A I)) ∧
    (closedSiteLift A I).Full ∧
    (closedSiteLift A I).Faithful ∧
    (closedSiteLift A I).IsCocontinuous
      (topology (Spec (.of (A ⧸ I)))) (topology (Spec (.of A))) ∧
    Nonempty (closedSiteLift A I ⊣ closedSiteBaseChange A I) ∧
    (∀ (V : (Spec (.of (A ⧸ I))).AffineProEt) (R : Presieve V),
      R ∈ precoverage V →
      R.map (closedSiteLift A I) ∈ precoverage ((closedSiteLift A I).obj V)) ∧
    (∀ V : (Spec (.of (A ⧸ I))).AffineProEt,
      IsClosedImmersion (closedSiteLiftInclusion A I V) ∧
      IsPullback (closedSiteLiftInclusion A I V) V.hom
        ((closedSiteLift A I).obj V).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ∧
      ∀ x : ((closedSiteLift A I).obj V).left,
        ∃ z : V.left, x ⤳ (closedSiteLiftInclusion A I V) z) := by
  have hgeom : ∃ adj : closedSiteLift A I ⊣ closedSiteBaseChange A I, IsIso adj.unit := by
    let e V U := Equiv.ofBijective (siteHomMap A I V U) (siteHomMap_bijective A I V U)
    let adj : closedSiteLift A I ⊣ closedSiteBaseChange A I := Adjunction.mkOfHomEquiv
      { homEquiv := e
        homEquiv_naturality_left_symm := by
          intro V W U f g
          apply (e V U).injective
          change siteHomMap A I V U _ = siteHomMap A I V U _
          rw [siteHomMap_naturality_left]
          exact (e V U).apply_symm_apply (f ≫ g) |>.trans
            (congrArg (fun k ↦ f ≫ k) ((e W U).apply_symm_apply g)).symm
        homEquiv_naturality_right := siteHomMap_naturality_right A I }
    refine ⟨adj, ?_⟩
    have : ∀ V, IsIso (adj.unit.app V) := by
      intro V
      let h := inclusion_pullback A I V
      let eV : V ≅ (closedSiteBaseChange A I).obj ((closedSiteLift A I).obj V) :=
        MorphismProperty.Over.isoMk h.isoPullback (by
          change h.isoPullback.hom ≫ pullback.snd _ _ = _
          exact h.isoPullback_hom_snd)
      have he : adj.unit.app V = eV.hom := by
        apply MorphismProperty.Over.Hom.ext
        change pullback.lift (closedSiteLiftInclusion A I V ≫ 𝟙 _) V.hom _ =
          h.isoPullback.hom
        apply pullback.hom_ext
        · rw [pullback.lift_fst, h.isoPullback_hom_fst, Category.comp_id]
        · rw [pullback.lift_snd, h.isoPullback_hom_snd]
      rw [he]
      infer_instance
    exact NatIso.isIso_of_isIso_app adj.unit
  obtain ⟨adj, hunit⟩ := hgeom
  have : IsIso adj.unit := hunit
  have ff := adj.fullyFaithfulLOfIsIsoUnit
  have : (closedSiteLift A I).Full := ff.full
  have : (closedSiteLift A I).Faithful := ff.faithful
  have : (closedSiteBaseChange A I).IsRightAdjoint := adj.isRightAdjoint
  refine ⟨baseChange_covers A I, ?_, ff.full, ff.faithful, ?_, ⟨adj⟩, ?_, ?_⟩
  · intro U T W R hR f g hf
    infer_instance
  · apply (adj.isCocontinuous_iff_coverPreserving _ _).mpr
    constructor
    intro U S hS
    obtain ⟨ι, hι, Z, f, hf, hsurj⟩ := exists_finite_jointly_surjective_of_mem_topology hS
    have : Finite ι := hι
    have hc := baseChange_covers A I U _ (finite_covers Z f hsurj)
    refine GrothendieckTopology.superset_covering _ ?_ (generate_mem_topology hc)
    rw [Sieve.generate_le_iff]
    rw [Presieve.map_ofArrows]
    rintro _ _ ⟨i⟩
    exact ⟨Z i, f i, 𝟙 _, hf i, (Category.id_comp _).symm⟩
  · exact lift_covers A I
  · intro V
    exact ⟨inclusion_closed A I V, inclusion_pullback A I V, inclusion_specializes A I V⟩

end AlgebraicGeometry.Scheme.AffineProEt
