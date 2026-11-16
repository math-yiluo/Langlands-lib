import Langlands.GroupScheme.Dynamic.UnipotentGrading
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.CommutativeAlgebra.GradedEpimorphism

/-! # Monomorphisms on relative dynamic unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented.RelativeUnipotent

open AffineLine
open CommutativeAlgebra

variable {R : CommRingCat.{u}}
  {F F' : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B C : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {e' : (F' ⋙ forget GrpCat).CorepresentableBy C}

/-- The actual coordinate pullback of a homomorphism of corepresented groups. -/
def pullback (f : groupScheme F e ⟶ groupScheme F' e') : C →ₐ[R] B :=
  RingCoordinates.algHom f.hom.hom

theorem specMap_pullback (f : groupScheme F e ⟶ groupScheme F' e') :
    Spec.map (CommRingCat.ofHom (pullback f).toRingHom) = f.hom.hom.left :=
  specMap_pointRing f.hom.hom

variable (e) in
/-- The augmentation of a corepresented group over an arbitrary ring. -/
def augmentation : B →ₐ[R] R where
  __ := (counit e).hom
  commutes' r := by
    have h := algebraMap_comp_pointRing (1 : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F e).X)
    rw [Spec.preimage_id] at h
    exact congrArg (fun φ => φ.hom r) h

/-- Homomorphisms preserve augmentation. -/
theorem augmentation_pullback (f : groupScheme F e ⟶ groupScheme F' e') (b : C) :
    augmentation e (pullback f b) = augmentation e' b := by
  have h : CommRingCat.ofHom (pullback f).toRingHom ≫ counit e = counit e' := by
    apply Spec.map_injective
    rw [Spec.map_comp, specMap_pullback]
    change Spec.map (pointRing (1 : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F e).X)) ≫
      f.hom.hom.left = Spec.map (pointRing (1 : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F' e').X))
    rw [specMap_pointRing, specMap_pointRing]
    exact congrArg (fun x : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F' e').X => x.left)
      (MonObj.one_comp f.hom.hom)
  exact congrArg (fun g => g.hom b) h

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)
  (f : groupScheme F e ⟶ groupScheme F' e')

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate pullback intertwines the conjugation coactions. -/
theorem coaction_pullback :
    CommRingCat.ofHom (pullback f).toRingHom ≫ coaction χ =
      coaction (χ ≫ f) ≫ laurentCoeffMap (CommRingCat.ofHom (pullback f).toRingHom) := by
  change pointRing f.hom.hom ≫ coaction χ =
    coaction (χ ≫ f) ≫ laurentCoeffMap (pointRing f.hom.hom)
  apply Spec.map_injective
  rw [Spec.map_comp, specMap_coaction, specMap_pointRing]
  rw [← laurentPoint_comp_orbit_left (χ ≫ f) f.hom.hom]
  change (laurentPoint (structureMap e) ≫ Dynamic.orbit χ (universalPoint e)).left ≫
    f.hom.hom.left = (laurentPoint (structureMap e) ≫ Dynamic.orbit (χ ≫ f) f.hom.hom).left
  rw [← Over.comp_left]
  congr 1
  rw [Category.assoc, ← Dynamic.orbit_comp_hom]
  congr 2

/-- Components commute with pullback. -/
theorem coeff_coaction_pullback (b : C) (n : ℤ) :
    ((coaction χ).hom (pullback f b)).coeff n =
      pullback f (((coaction (χ ≫ f)).hom b).coeff n) := by
  have h := congrArg (fun g => (g.hom b).coeff n) (coaction_pullback χ f)
  change ((coaction χ).hom (pullback f b)).coeff n =
    (laurentCoeffMap (CommRingCat.ofHom (pullback f).toRingHom)
      ((coaction (χ ≫ f)).hom b)).coeff n at h
  exact h.trans (coeff_laurentCoeffMap _ _ _)

/-- The counit descends to the actual quotient algebra of the unipotent subgroup. -/
def unipotentAugmentation : B ⧸ unipotentIdeal χ →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (augmentation e) fun b hb =>
    (isAffineCutOutBy_unipotent χ R (𝟙 _) 1).1 (Subgroup.one_mem _) b hb

theorem unipotentAugmentation_mk (b : B) :
    unipotentAugmentation χ (unipQuot χ b) = augmentation e b :=
  Ideal.Quotient.lift_mk _ _ _

/-- The quotient's zero component is its augmentation scalar. -/
theorem unipCoaction_zero (a : B ⧸ unipotentIdeal χ) :
    GradedLine.comp (isGrading_unipCoaction χ) 0 a =
      algebraMap R _ (unipotentAugmentation χ a) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [GradedLine.comp_apply, coeff_unipCoaction_mk, unipotentAugmentation_mk]
  change unipQuot χ (((coaction χ).hom b).coeff 0) =
    unipQuot χ (algebraMap R B (counit e b))
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inr ⟨b, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The induced homomorphism on the actual relative dynamic unipotent groups. -/
def unipotentMap : unipotentScheme χ ⟶ unipotentScheme (χ ≫ f) :=
  (isRepresentedBy_unipotentHom (χ ≫ f)).factorHom (unipotentHom χ ≫ f) (by
    rintro T _ ⟨x, rfl⟩
    change x ≫ ((unipotentHom χ).hom.hom ≫ f.hom.hom) ∈
      (Dynamic.unipotent (χ ≫ f)).carrier T
    rw [← Category.assoc]
    exact Dynamic.unipotent_le_comap χ f T
      ((isRepresentedBy_unipotentHom χ).pointsEquiv T x).property)

theorem unipotentMap_comp :
    unipotentMap χ f ≫ unipotentHom (χ ≫ f) = unipotentHom χ ≫ f :=
  (isRepresentedBy_unipotentHom (χ ≫ f)).factorHom_comp _ _

/-- The coordinate map of the induced unipotent homomorphism. -/
def unipotentPullback : C ⧸ unipotentIdeal (χ ≫ f) →ₐ[R] B ⧸ unipotentIdeal χ :=
  RingCoordinates.algHom (unipotentMap χ f).hom.hom

theorem specMap_unipotentPullback :
    Spec.map (CommRingCat.ofHom (unipotentPullback χ f).toRingHom) =
      (unipotentMap χ f).hom.hom.left :=
  specMap_pointRing (unipotentMap χ f).hom.hom

set_option backward.isDefEq.respectTransparency false in
/-- The induced coordinate map commutes with the ambient quotient maps. -/
theorem unipotentPullback_mk (b : C) :
    unipotentPullback χ f (unipQuot (χ ≫ f) b) = unipQuot χ (pullback f b) := by
  have h :
      CommRingCat.ofHom (unipQuot (χ ≫ f)) ≫
          CommRingCat.ofHom (unipotentPullback χ f).toRingHom =
        CommRingCat.ofHom (pullback f).toRingHom ≫ CommRingCat.ofHom (unipQuot χ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, specMap_unipotentPullback, specMap_pullback]
    simpa only [Grp.comp_hom_hom, Over.comp_left, cutHom_left] using
      congrArg (fun g : unipotentScheme χ ⟶ groupScheme F' e' => g.hom.hom.left)
        (unipotentMap_comp χ f)
  exact congrArg (fun g => g.hom b) h

/-- The induced coordinate map preserves augmentation. -/
theorem unipotentAugmentation_pullback (a : C ⧸ unipotentIdeal (χ ≫ f)) :
    unipotentAugmentation χ (unipotentPullback χ f a) =
      unipotentAugmentation (χ ≫ f) a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [unipotentPullback_mk, unipotentAugmentation_mk, unipotentAugmentation_mk,
    augmentation_pullback]

/-- Every grading component commutes with the induced coordinate map. -/
theorem unipCoaction_coeff_pullback (a : C ⧸ unipotentIdeal (χ ≫ f)) (n : ℤ) :
    (unipCoaction χ (unipotentPullback χ f a)).coeff n =
      unipotentPullback χ f ((unipCoaction (χ ≫ f) a).coeff n) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [unipotentPullback_mk, coeff_unipCoaction_mk, coeff_unipCoaction_mk,
    unipotentPullback_mk, coeff_coaction_pullback]

/-- The induced coordinate map preserves each homogeneous submodule. -/
theorem unipotentPullback_homogeneous (n : ℤ)
    (a : C ⧸ unipotentIdeal (χ ≫ f))
    (ha : a ∈ GradedLine.homog (isGrading_unipCoaction (χ ≫ f)) n) :
    unipotentPullback χ f a ∈ GradedLine.homog (isGrading_unipCoaction χ) n := by
  rw [GradedLine.mem_homog] at ha ⊢
  ext m
  rw [unipCoaction_coeff_pullback, ha, AddMonoidAlgebra.coeff_single,
    AddMonoidAlgebra.coeff_single]
  by_cases h : n = m
  · simp [h]
  · simp [h]

instance mono_unipotentMap [Mono f.hom.hom] :
    Mono (unipotentMap χ f).hom.hom := by
  have h := congrArg (fun g : unipotentScheme χ ⟶ groupScheme F' e' => g.hom.hom)
    (unipotentMap_comp χ f)
  change (unipotentMap χ f).hom.hom ≫ (unipotentHom (χ ≫ f)).hom.hom =
    (unipotentHom χ).hom.hom ≫ f.hom.hom at h
  exact mono_of_mono_fac h

/-- A monomorphism of affine groups induces a closed immersion on their relative
dynamic unipotent subgroups, over any commutative base ring. -/
theorem isClosedImmersion_unipotentMap [Mono f.hom.hom] :
    IsClosedImmersion (unipotentMap χ f).hom.hom.left := by
  let : Mono (unipotentMap χ f).hom.hom := mono_unipotentMap χ f
  have : Mono (Spec.map (CommRingCat.ofHom (unipotentPullback χ f).toRingHom)) := by
    rw [specMap_unipotentPullback]
    exact Over.mono_left_of_mono _
  have h := GradedLine.isClosedImmersion_specMap_of_mono
    (isGrading_unipCoaction χ) (isGrading_unipCoaction (χ ≫ f))
    (unipotentPullback χ f) (unipotentAugmentation χ)
    (fun a n hn => unipCoaction_coeff_neg χ a hn) (unipCoaction_zero χ)
    (fun a n hn => unipCoaction_coeff_neg (χ ≫ f) a hn)
    (fun a => by rw [unipCoaction_zero, unipotentAugmentation_pullback])
    (unipotentPullback_homogeneous χ f)
  rwa [specMap_unipotentPullback] at h

end Langlands.GroupScheme.Corepresented.RelativeUnipotent
