/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor

import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# The profinite basis over a separably closed field

Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11; Stacks Tags 092Q, 096D, 096T.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace TestLC
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra A B] (S : Profinite.{u})
private noncomputable def projection (φ : LocallyConstant S A →+* B) : C(PrimeSpectrum B, S) :=
  ⟨fun p ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm
      (PrimeSpectrum.comap φ p)).1,
    continuous_fst.comp
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm.continuous.comp
        (PrimeSpectrum.continuous_comap φ))⟩
private lemma localization_eq (φ : LocallyConstant S A →ₐ[A] B)
    (p : PrimeSpectrum B) (g : LocallyConstant S A) :
    algebraMap B (Localization.AtPrime p.asIdeal) (φ g) =
      algebraMap B (Localization.AtPrime p.asIdeal)
        (algebraMap A B (g (projection S φ.toRingHom p))) := by
  classical
  let s := projection S φ.toRingHom p
  let q := ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm
    (PrimeSpectrum.comap φ.toRingHom p)).2
  have hp : PrimeSpectrum.comap φ.toRingHom p = LocallyConstant.toPrimeSpectrum (s, q) :=
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).apply_symm_apply _).symm
  let χ := LocallyConstant.charFn A (g.isLocallyConstant.isClopen_fiber (g s))
  have hχ : φ χ ∉ p.asIdeal := by
    change χ ∉ (PrimeSpectrum.comap φ.toRingHom p).asIdeal
    rw [hp, LocallyConstant.mem_toPrimeSpectrum_asIdeal]
    simpa [χ, LocallyConstant.charFn_apply_of_mem] using q.isPrime.one_notMem
  have hid : IsIdempotentElem χ := by
    change χ * χ = χ
    ext x
    by_cases hx : g x = g s
    · simp [χ, LocallyConstant.charFn_apply_of_mem, hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have hχloc : algebraMap B (Localization.AtPrime p.asIdeal) (φ χ) = 1 :=
    (hid.map φ.toRingHom).algebraMap_localization_atPrime_of_notMem hχ
  have hmul : χ * g = χ * algebraMap A (LocallyConstant S A) (g s) := by
    ext x
    change χ x * g x = χ x * g s
    by_cases hx : g x = g s
    · simp [hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have h := congrArg (fun v ↦ algebraMap B (Localization.AtPrime p.asIdeal) (φ v)) hmul
  simpa only [map_mul, φ.commutes, hχloc, one_mul] using h
private noncomputable def fromIntegers (φ : LocallyConstant S ℤ →+* B) :
    LocallyConstant S A →ₐ[A] B :=
  { LocallyConstant.liftPrimeSpectrum (algebraMap A B) (projection S φ) with
    commutes' := LocallyConstant.liftPrimeSpectrum_algebraMap _ _ }
private noncomputable def toIntegers (φ : LocallyConstant S A →ₐ[A] B) :
    LocallyConstant S ℤ →+* B :=
  φ.toRingHom.comp (LocallyConstant.mapRingHom (Int.castRingHom A))
private lemma projection_toIntegers (φ : LocallyConstant S A →ₐ[A] B) (p : PrimeSpectrum B) :
    projection S (toIntegers S φ) p = projection S φ.toRingHom p := by
  obtain ⟨⟨s, q⟩, hq⟩ := LocallyConstant.toPrimeSpectrum_surjective
    (PrimeSpectrum.comap φ.toRingHom p)
  have hZ : PrimeSpectrum.comap (toIntegers S φ) p =
      LocallyConstant.toPrimeSpectrum (s, PrimeSpectrum.comap (Int.castRingHom A) q) := by
    rw [toIntegers, PrimeSpectrum.comap_comp_apply, ← hq]
    ext f
    rfl
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm _).1 =
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm _).1
  rw [hZ, ← hq]
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)) (s, _))).1 =
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)) (s, _))).1
  simp only [Homeomorph.symm_apply_apply]
private lemma from_to (φ : LocallyConstant S A →ₐ[A] B) :
    fromIntegers S (toIntegers S φ) = φ := by
  ext g
  apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
  intro p
  change algebraMap B (Localization.AtPrime p.asIdeal)
    (LocallyConstant.liftPrimeSpectrum _ _ g) = _
  rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum,
    projection_toIntegers, localization_eq]
private lemma to_from (φ : LocallyConstant S ℤ →+* B) :
    toIntegers S (fromIntegers (A := A) S φ) = φ := by
  ext g
  apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
  intro p
  change algebraMap B (Localization.AtPrime p.asIdeal)
    (LocallyConstant.liftPrimeSpectrum _ _
      (LocallyConstant.mapRingHom (Int.castRingHom A) g)) = _
  rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
  rw [show algebraMap B (Localization.AtPrime p.asIdeal) (φ g) =
    algebraMap B (Localization.AtPrime p.asIdeal)
      (g (projection S φ p) : B) from localization_eq S φ.toIntAlgHom p g]
  change algebraMap B (Localization.AtPrime p.asIdeal)
    (algebraMap A B (g (projection S φ p) : A)) = _
  simp only [map_intCast]

open CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false in
private theorem pushout (A : Type u) [CommRing A] (S : Profinite.{u}) :
    IsPushout
      (CommRingCat.ofHom ((Int.castRingHom (LocallyConstant S ℤ)).comp
        ULift.ringEquiv.toRingHom) : CommRingCat.of (ULift.{u} ℤ) ⟶ _)
      (CommRingCat.ofHom ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom))
      (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom A)))
      (CommRingCat.ofHom (algebraMap A (LocallyConstant S A))) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk _ _ (by ext z s; rfl))
  apply PushoutCocone.isColimitAux'
  intro c
  let : Algebra A c.pt := c.inr.hom.toAlgebra
  let d := fromIntegers (A := A) S c.inl.hom
  refine ⟨CommRingCat.ofHom d.toRingHom, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    exact to_from (A := A) S c.inl.hom
  · ext r
    exact d.commutes r
  · intro m hl hr
    let ψ : LocallyConstant S A →ₐ[A] c.pt :=
      { m.hom with commutes' := fun r ↦ congrArg (fun f ↦ f.hom r) hr }
    have ht : toIntegers S ψ = c.inl.hom := congrArg CommRingCat.Hom.hom hl
    have heq : ψ = d := by
      rw [← from_to S ψ, ht]
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom heq)

open AlgebraicGeometry
private theorem pullback (A : Type u) [CommRing A] (S : Profinite.{u}) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (LocallyConstant.mapRingHom (Int.castRingHom A))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (LocallyConstant S A))))
      (toSpecZ (profiniteToScheme.obj S)) (toSpecZ (Spec (.of A))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (pushout A S)
  convert h using 1 <;> exact specULiftZIsTerminal.hom_ext _ _
private noncomputable def lcIso (A : Type u) [CommRing A] (S : Profinite.{u}) :
    Spec (.of (LocallyConstant S A)) ≅ ((profiniteToProEtOf (Spec (.of A))).obj S).left :=
  (pullback A S).isoPullback
end TestLC

open TopologicalSpace

private theorem stalks (K R : Type u) [Field K] [IsSepClosed K] [CommRing R] [Algebra K R]
    [Algebra.WeaklyEtale K R] : Algebra.BijectiveOnStalks K R := by
  have : Ring.AbsolutelyFlat R :=
    .of_flat_lmul' K R (Algebra.WeaklyEtale.flat_lmul' K R)
  constructor
  intro p hp
  let : Field (Localization.AtPrime p) :=
    (Ring.AbsolutelyFlat.isField_of_isLocalization_prime R p _).toField
  have : Algebra.WeaklyEtale R (Localization.AtPrime p) :=
    .of_isLocalization R p.primeCompl _
  have : Algebra.WeaklyEtale K (Localization.AtPrime p) := .trans K R _
  have : Algebra.IsSeparable K (Localization.AtPrime p) := Algebra.WeaklyEtale.isAlgebraic
  have hK : Function.Bijective (algebraMap K (Localization.AtPrime p)) :=
    IsSepClosed.algebraMap_bijective K _
  have hloc : Function.Bijective
      (algebraMap K (Localization.AtPrime (p.comap (algebraMap K R)))) := by
    exact (IsLocalization.atUnits K (p.comap (algebraMap K R)).primeCompl
      (S := Localization.AtPrime (p.comap (algebraMap K R)))
      (fun x hx ↦ isUnit_iff_ne_zero.mpr (fun h ↦ hx (h ▸ Ideal.zero_mem _)))).bijective
  have heq : (Localization.localRingHom (p.comap (algebraMap K R)) p
      (algebraMap K R) rfl).comp
      (algebraMap K (Localization.AtPrime (p.comap (algebraMap K R)))) =
      algebraMap K (Localization.AtPrime p) := by
    ext x
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
    exact (IsScalarTower.algebraMap_apply K R (Localization.AtPrime p) x).symm
  apply (Function.Bijective.of_comp_iff _ hloc).mp
  change Function.Bijective ((Localization.localRingHom _ p (algebraMap K R) rfl).comp
    (algebraMap K (Localization.AtPrime (p.comap (algebraMap K R)))))
  rw [heq]
  exact hK

open TopologicalSpace
private theorem separated (R : Type u) [CommRing R] [Ring.AbsolutelyFlat R] :
    TotallySeparatedSpace (PrimeSpectrum R) := by
  have hc (r : R) : IsClopen (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    obtain ⟨s, hs⟩ := Ring.AbsolutelyFlat.exists_eq_mul_self_mul r
    have he : r * s * (1 - r * s) = 0 := by
      calc r * s * (1 - r * s) = r * s - r * r * s * s := by ring
           _ = 0 := sub_eq_zero.mpr (congrArg (fun t ↦ t * s) hs)
    have heq : PrimeSpectrum.basicOpen (r * s) = PrimeSpectrum.basicOpen r := by
      apply le_antisymm
      · exact PrimeSpectrum.basicOpen_mul_le_left _ _
      · conv_lhs => rw [hs]
        simp only [PrimeSpectrum.basicOpen_mul, inf_idem]
        exact le_rfl
    rw [← heq]
    exact PrimeSpectrum.isClopen_basicOpen_of_mul_add _ _ he (by ring)
  suffices ZeroDimensionalSpace (PrimeSpectrum R) from inferInstance
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.of_isOpen_of_subset
  · exact fun _ h ↦ h.isOpen
  · rintro _ ⟨r, rfl⟩
    exact hc r

private noncomputable def classification (K B : Type u) [Field K] [IsSepClosed K]
    [CommRing B] [Algebra K B] [Algebra.WeaklyEtale K B] :
    LocallyConstant (PrimeSpectrum B) K ≃ₐ[K] B := by
  have : Ring.AbsolutelyFlat B :=
    .of_flat_lmul' K B (Algebra.WeaklyEtale.flat_lmul' K B)
  have : TotallySeparatedSpace (PrimeSpectrum B) := separated B
  have : Algebra.BijectiveOnStalks K B := stalks K B
  let φ : LocallyConstant (PrimeSpectrum B) K →ₐ[K] B :=
    { LocallyConstant.liftPrimeSpectrum (algebraMap K B) ⟨id, continuous_id⟩ with
      commutes' := LocallyConstant.liftPrimeSpectrum_algebraMap _ _ }
  apply AlgEquiv.ofBijective φ
  have hstalk : φ.toRingHom.BijectiveOnStalks := by
    apply RingHom.BijectiveOnStalks.of_comp
      (RingHom.bijectiveOnStalks_algebraMap.mpr
        (inferInstance : Algebra.BijectiveOnStalks K (LocallyConstant (PrimeSpectrum B) K)))
    convert RingHom.bijectiveOnStalks_algebraMap.mpr
      (inferInstance : Algebra.BijectiveOnStalks K B) using 1
    exact φ.comp_algebraMap
  apply hstalk.bijective_of_bijective
  constructor
  · intro p q h
    have hh := congrArg
      (fun x ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := PrimeSpectrum B)
        (R := K)).symm x).1) h
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := PrimeSpectrum B)
      (R := K)).symm (PrimeSpectrum.comap (LocallyConstant.liftPrimeSpectrum
        (algebraMap K B) ⟨id, continuous_id⟩) p)).1 = _ at hh
    rw [LocallyConstant.comap_liftPrimeSpectrum,
      LocallyConstant.comap_liftPrimeSpectrum] at hh
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := PrimeSpectrum B)
      (R := K)).symm ((LocallyConstant.homeomorphPrimeSpectrum
        (T := PrimeSpectrum B) (R := K)) (p, _))).1 =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := PrimeSpectrum B)
      (R := K)).symm ((LocallyConstant.homeomorphPrimeSpectrum
        (T := PrimeSpectrum B) (R := K)) (q, _))).1 at hh
    simpa only [Homeomorph.symm_apply_apply] using hh
  · intro p
    obtain ⟨⟨q, t⟩, rfl⟩ := LocallyConstant.toPrimeSpectrum_surjective p
    refine ⟨q, ?_⟩
    change PrimeSpectrum.comap (LocallyConstant.liftPrimeSpectrum
      (algebraMap K B) ⟨id, continuous_id⟩) q = _
    rw [LocallyConstant.comap_liftPrimeSpectrum]
    congr 1
    exact Prod.ext rfl (Subsingleton.elim _ _)

namespace AlgebraicGeometry.ProEtale
private noncomputable def specSpaceHomeo (K : Type u) [Field K] (S : Profinite.{u}) :
    S ≃ₜ Spec (.of (LocallyConstant S K)) := by
  let : Unique (PrimeSpectrum K) :=
    { default := ⟨⊥, Ideal.isPrime_bot⟩
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  exact (Homeomorph.prodUnique S (PrimeSpectrum K)).symm.trans
    LocallyConstant.homeomorphPrimeSpectrum
private noncomputable def testSpaceHomeo (K : Type u) [Field K] (S : Profinite.{u}) :
    S ≃ₜ ((profiniteToProEtOf (Spec (.of K))).obj S).left :=
  (specSpaceHomeo K S).trans (Scheme.homeoOfIso (TestLC.lcIso K S))
private noncomputable def testHomEquiv (K : Type u) [Field K] (S T : Profinite.{u}) :
    ((profiniteToProEtOf (Spec (.of K))).obj S ⟶
      (profiniteToProEtOf (Spec (.of K))).obj T) ≃ (S ⟶ T) :=
  (relativeMapEquiv _ _ T).trans
    ((Iso.homCongr (TestLC.lcIso K S).symm (Iso.refl _)).trans
      ((specMapEquiv _ T).trans
        (((specSpaceHomeo K S).symm.continuousMapCongr (Homeomorph.refl T)).trans
          { toFun := fun f ↦ ConcreteCategory.ofHom f
            invFun := fun f ↦ f.hom.hom })))
private noncomputable def testProjection (K : Type u) [Field K] (S : Profinite.{u})
    (x : ((profiniteToProEtOf (Spec (.of K))).obj S).left) : S :=
  ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    ((pullback.fst (toSpecZ (profiniteToScheme.obj S))
      (toSpecZ (Spec (.of K)))) x)).1
private theorem testProjection_homeo (K : Type u) [Field K] (S : Profinite.{u}) (s : S) :
    testProjection K S (testSpaceHomeo K S s) = s := by
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    (((TestLC.lcIso K S).hom ≫ pullback.fst _ _) (specSpaceHomeo K S s))).1 = s
  erw [(TestLC.pullback K S).isoPullback_hom_fst]
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    (PrimeSpectrum.comap (LocallyConstant.mapRingHom (Int.castRingHom K))
      (LocallyConstant.toPrimeSpectrum (s, _)))).1 = s
  have he (q : PrimeSpectrum K) :
      PrimeSpectrum.comap (LocallyConstant.mapRingHom (Int.castRingHom K))
      (LocallyConstant.toPrimeSpectrum (s, q)) =
      LocallyConstant.toPrimeSpectrum (s,
        PrimeSpectrum.comap (Int.castRingHom K) q) := by
    ext g
    rfl
  rw [he]
  exact congrArg Prod.fst (Homeomorph.symm_apply_apply
    (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)) _)
private theorem testProjection_natural (K : Type u) [Field K]
    {S T : Profinite.{u}} (f : S ⟶ T)
    (x : ((profiniteToProEtOf (Spec (.of K))).obj S).left) :
    testProjection K T (((profiniteToProEtOf (Spec (.of K))).map f).left x) =
      f (testProjection K S x) := by
  have hn := relativeMapEquiv_target (Spec (.of K))
    ((profiniteToProEtOf (Spec (.of K))).obj S) S T f (𝟙 _)
  simp only [Category.id_comp] at hn
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
    (relativeMapEquiv _ _ T ((profiniteToProEtOf (Spec (.of K))).map f) x)).1 = _
  rw [hn, Scheme.Hom.comp_apply, profiniteProjection_natural]
  rfl
private theorem testHomEquiv_map (K : Type u) [Field K] {S T : Profinite.{u}} (f : S ⟶ T) :
    testHomEquiv K S T ((profiniteToProEtOf (Spec (.of K))).map f) = f := by
  ext s
  change specMapEquiv _ T
    ((TestLC.lcIso K S).hom ≫ relativeMapEquiv _ _ T
      ((profiniteToProEtOf (Spec (.of K))).map f)) (specSpaceHomeo K S s) = f s
  rw [specMapEquiv_apply]
  change testProjection K T (((profiniteToProEtOf (Spec (.of K))).map f).left
    (testSpaceHomeo K S s)) = _
  rw [testProjection_natural, testProjection_homeo]
private theorem testFullyFaithful (K : Type u) [Field K] :
    (profiniteToProEtOf (Spec (.of K))).Full ∧
      (profiniteToProEtOf (Spec (.of K))).Faithful := by
  have h (S T : Profinite.{u}) : Function.Bijective
      ((profiniteToProEtOf (Spec (.of K))).map : (S ⟶ T) → _) := by
    constructor
    · intro f g hfg
      have hh := congrArg (testHomEquiv K S T) hfg
      simpa only [testHomEquiv_map] using hh
    · intro f
      refine ⟨testHomEquiv K S T f, ?_⟩
      apply (testHomEquiv K S T).injective
      rw [testHomEquiv_map]
  exact ⟨⟨fun f ↦ ⟨(h _ _).surjective f |>.choose,
    (h _ _).surjective f |>.choose_spec⟩⟩, ⟨fun e ↦ (h _ _).injective e⟩⟩

private theorem affineClassification (K : Type u) [Field K] [IsSepClosed K]
    (U : (Spec (.of K)).ProEt) [IsAffine U.left] :
    ∃ S : Profinite.{u}, Nonempty (U ≅ (profiniteToProEtOf (Spec (.of K))).obj S) := by
  let R := Γ(U.left, ⊤)
  let φ : CommRingCat.of K ⟶ R := Spec.preimage (U.left.isoSpec.inv ≫ U.hom)
  let : Algebra K R := φ.hom.toAlgebra
  have hφ : Spec.map φ = U.left.isoSpec.inv ≫ U.hom := Spec.map_preimage _
  have : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
    change WeaklyEtale (Spec.map φ)
    rw [hφ]
    infer_instance
  have : Algebra.WeaklyEtale K R := weaklyEtale_SpecMap_algebraMap_iff.mp this
  have : Ring.AbsolutelyFlat R :=
    .of_flat_lmul' K R (Algebra.WeaklyEtale.flat_lmul' K R)
  have : TotallySeparatedSpace (PrimeSpectrum R) := separated R
  let S := Profinite.of (PrimeSpectrum R)
  let e : LocallyConstant S K ≃ₐ[K] R := classification K R
  let eSpec : Spec R ≅ Spec (.of (LocallyConstant S K)) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  refine ⟨S, ⟨MorphismProperty.Over.isoMk
    (U.left.isoSpec ≪≫ eSpec ≪≫ TestLC.lcIso K S) ?_⟩⟩
  change U.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    ((TestLC.lcIso K S).hom ≫ pullback.snd _ _) = U.hom
  erw [(TestLC.pullback K S).isoPullback_hom_snd]
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K (LocallyConstant S K)) ≫
      CommRingCat.ofHom e.toRingHom = φ := by
    ext x
    exact e.commutes x
  rw [he, hφ, Iso.hom_inv_id_assoc]

private theorem testProAffine (K : Type u) [Field K] (S : Profinite.{u}) :
    proAffineEtale ((profiniteToProEtOf (Spec (.of K))).obj S).hom := by
  have h : proAffineEtale (Spec.map (CommRingCat.ofHom
      (algebraMap K (LocallyConstant S K)))) := by
    rw [proAffineEtale_Spec_iff]
    change Algebra.IndEtale K (LocallyConstant S K)
    infer_instance
  rw [← (TestLC.pullback K S).isoPullback_hom_snd] at h
  exact (proAffineEtale.cancel_left_of_respectsIso _ _).mp h
private theorem testCoverDense (K : Type u) [Field K] [IsSepClosed K] :
    (profiniteToProEtOf (Spec (.of K))).IsCoverDense (Scheme.ProEt.topology (Spec (.of K))) := by
  constructor
  intro U
  apply (Scheme.ProEt.topology (Spec (.of K))).superset_covering _
    ((Scheme.AffineProEt.toProEt (Spec (.of K))).is_cover_of_isCoverDense _ U)
  rintro V f ⟨⟨A, g, h, w⟩⟩
  let : IsAffine ((Scheme.AffineProEt.toProEt (Spec (.of K))).obj A).left :=
    inferInstanceAs (IsAffine A.left)
  obtain ⟨S, ⟨e⟩⟩ := affineClassification K
    ((Scheme.AffineProEt.toProEt (Spec (.of K))).obj A)
  exact ⟨⟨S, g ≫ e.hom, e.inv ≫ h, by simp [Category.assoc, w]⟩⟩

private theorem testTopologyReflect (K : Type u) [Field K]
    {T : Profinite.{u}} {R : Sieve T}
    (hR : R.functorPushforward (profiniteToProEtOf (Spec (.of K))) ∈
      Scheme.ProEt.topology (Spec (.of K)) _) : R ∈ coherentTopology Profinite T := by
  let F := profiniteToProEtOf (Spec (.of K))
  let G := Scheme.AffineProEt.toProEt (Spec (.of K))
  let A : (Spec (.of K)).AffineProEt :=
    Scheme.AffineProEt.mk (F.obj T).hom (testProAffine K T)
  let eA : G.obj A ≅ F.obj T :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp _)
  let R' : Sieve (G.obj A) := (R.functorPushforward F).pullback eA.hom
  have hR' : R' ∈ Scheme.ProEt.topology (Spec (.of K)) _ :=
    (Scheme.ProEt.topology (Spec (.of K))).pullback_stable eA.hom hR
  have hA : R'.functorPullback G ∈
      Scheme.AffineProEt.topology (Spec (.of K)) A := by
    apply (Functor.functorPushforward_mem_iff
      (Scheme.AffineProEt.topology (Spec (.of K)))
      (Scheme.ProEt.topology (Spec (.of K))) G).mp
    exact Functor.IsCoverDense.functorPullback_pushforward_covering (G := G) ⟨_, hR'⟩
  obtain ⟨I, hI, V, f, hf, hjoint⟩ :=
    Scheme.AffineProEt.exists_finite_jointly_surjective_of_mem_topology hA
  let := hI
  have hmem (i : I) : (R.functorPushforward F) (G.map (f i) ≫ eA.hom) := hf i
  choose S r l hr hfac using hmem
  apply (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mpr
  let _ := Fintype.ofFinite I
  let e := (Fintype.equivFin I).symm
  refine ⟨Fin (Fintype.card I), inferInstance, fun i ↦ S (e i),
    fun i ↦ r (e i), ?_, fun i ↦ hr (e i)⟩
  apply ((Profinite.effectiveEpiFamily_tfae (fun i ↦ S (e i))
    (fun i ↦ r (e i))).out 1 3).mpr
  intro t
  obtain ⟨i, y, hy⟩ := hjoint (testSpaceHomeo K T t)
  refine ⟨e.symm i, ?_⟩
  change ∃ s : S (e (e.symm i)), r (e (e.symm i)) s = t
  rw [e.apply_symm_apply]
  refine ⟨testProjection K (S i) ((l i).left y), ?_⟩
  rw [← testProjection_natural]
  have he : (F.map (r i)).left ((l i).left y) = testSpaceHomeo K T t := by
    rw [← Scheme.Hom.comp_apply]
    change (l i ≫ F.map (r i)).left y = _
    rw [← hfac i]
    exact hy
  rw [he, testProjection_homeo]
private theorem testCoverPreserving (K : Type u) [Field K] :
    CoverPreserving (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology (Spec (.of K))) (profiniteToProEtOf (Spec (.of K))) := by
  constructor
  intro T R hR
  obtain ⟨I, hI, S, f, hf, hmem⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mp hR
  let := hI
  have hs := ((Profinite.effectiveEpiFamily_tfae S f).out 1 3).mp hf
  let S' : ULift.{u} I → Profinite.{u} := fun i ↦ S i.down
  let f' : ∀ i, S' i ⟶ T := fun i ↦ f i.down
  have hs' : ∀ t, ∃ i s, f' i s = t := fun t ↦ by
    obtain ⟨i, s, h⟩ := hs t
    exact ⟨⟨i⟩, s, h⟩
  have hfpqc := (profinite_test_object_functor (Spec (.of K))).2.2.2.2.1
    (ULift.{u} I) S' T f' hs'
  have hcover : Presieve.ofArrows
      (fun i ↦ (profiniteToProEtOf (Spec (.of K))).obj (S' i))
      (fun i ↦ (profiniteToProEtOf (Spec (.of K))).map (f' i)) ∈
      Scheme.ProEt.precoverage (Spec (.of K)) _ := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    refine ⟨hfpqc.1, ?_⟩
    apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
    refine ⟨((Scheme.ofArrows_mem_precoverage_iff _).mp hfpqc.2).1, ?_⟩
    intro i
    change WeaklyEtale ((profiniteToProEtOf (Spec (.of K))).map (f' i)).left
    apply MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale)
      _ ((profiniteToProEtOf (Spec (.of K))).obj T).hom
    · infer_instance
    · rw [MorphismProperty.Over.w]
      infer_instance
  apply (Scheme.ProEt.topology (Spec (.of K))).superset_covering _
    (Precoverage.generate_mem_toGrothendieck hcover)
  apply (Sieve.generate_le_iff _ _).mpr
  intro W g hg
  obtain ⟨i⟩ := hg
  exact ⟨S i.down, f i.down, 𝟙 _, hmem i.down, (Category.id_comp _).symm⟩
/-- The specified relative profinite test functor is a dense subsite over a
separably closed field.

Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11; Stacks Tags 092Q, 096D, 096T
(auxiliary; not a blueprint node).

Proof: Locally constant functions commute with extension of scalars from the integers,
as follows by evaluating a ring map at each prime localization and using characteristic
functions of its clopen fibres. The resulting ring pushout identifies the specified
fibre-product test scheme with Spec LC(S,K). Its space of connected components is S,
and the proved correspondence for maps to test schemes establishes full faithfulness.
A weakly etale K-algebra is absolutely flat. Its prime localizations are separable
algebraic fields, hence K, as K is separably closed. Thus its structure map identifies local
rings. Its spectrum has a clopen basis, since every principal ideal is generated by an
idempotent. The map LC(Spec B,K) to B obtained by the locally constant lifting construction
is bijective on local rings and spectra, hence is an isomorphism. This classifies every affine
pro-etale object as a test scheme and proves cover density using the affine basis.
A pro-etale cover of a test object has a finite affine refinement; under the spectrum
identification its containing profinite arrows are jointly surjective. Conversely,
finite jointly surjective profinite families give fpqc weakly etale covers by the
proved test-object theorem. This identifies the induced topology with the coherent
topology, including empty objects and empty covering families. -/
theorem geometricFieldProfiniteDenseSubsite (K : Type u) [Field K] [IsSepClosed K] :
    (profiniteToProEtOf (Spec (.of K))).IsDenseSubsite
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of K))) := by
  have := (testFullyFaithful K).1
  have := (testFullyFaithful K).2
  have := testCoverDense K
  exact { functorPushforward_mem_iff := fun {_ _} ↦
    ⟨testTopologyReflect K, (testCoverPreserving K).cover_preserve⟩ }
end AlgebraicGeometry.ProEtale
