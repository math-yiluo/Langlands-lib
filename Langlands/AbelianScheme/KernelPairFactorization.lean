import Langlands.AbelianScheme.KernelCharacterIndependence
import Langlands.AbelianScheme.IsogenySpecialization

/-! # Pairs with equal composite along a homomorphism family map -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.Scheme.Modules

/-- Equal pairs of maps give equal transported automorphisms. -/
lemma equalCompositeUnitAut_congr {U X Y : Scheme.{u}} (p : X ⟶ Y) {a a' b b' : U ⟶ X}
    (ha : a = a') (hb : b = b') (h : a ≫ p = b ≫ p) (h' : a' ≫ p = b' ≫ p) {M : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    equalCompositeUnitAut p a b h α = equalCompositeUnitAut p a' b' h' α := by
  subst ha hb
  rfl

end Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)

/-- The family map `T ×_S A ⟶ T ×_S B` is the base change of `f` along `T ×_S B ⟶ B`. -/
lemma homFamilySpaceMap_isPullback (T : Over S) :
    IsPullback ((homFamilySpaceMap f).app T) (pullback.snd T.hom A.X.hom)
      (pullback.snd T.hom B.X.hom) (hom f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst T.hom B.X.hom) (h₂₂ := B.X.hom)
    (v₁₃ := T.hom) ?_ (homFamilySpaceMap_snd f T) (IsPullback.of_hasPullback _ _)
  have hw : hom f ≫ B.X.hom = A.X.hom := (groupHom f).hom.hom.w
  rw [homFamilySpaceMap_fst, hw]
  exact IsPullback.of_hasPullback _ _

variable {f}

lemma isFinite_homFamilySpaceMap (hf : IsIsogeny f) (T : Over S) :
    IsFinite ((homFamilySpaceMap f).app T) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (homFamilySpaceMap_isPullback f T).flip hf.1

lemma flat_homFamilySpaceMap (hf : IsIsogeny f) (T : Over S) :
    Flat ((homFamilySpaceMap f).app T) :=
  MorphismProperty.of_isPullback (P := @Flat) (homFamilySpaceMap_isPullback f T).flip hf.2.1

lemma surjective_homFamilySpaceMap (hf : IsIsogeny f) (T : Over S) :
    Surjective ((homFamilySpaceMap f).app T) :=
  MorphismProperty.of_isPullback (P := @Surjective) (homFamilySpaceMap_isPullback f T).flip
    hf.2.2

variable (f) {T : Over S} {U : Scheme.{u}}

/-- The parameter of a map into the source family, as a scheme over `T.left`. -/
abbrev pairParameter (a : U ⟶ (relativeSpace A.X.hom).obj T) : Over T.left :=
  Over.mk (a ≫ pullback.fst T.hom A.X.hom)

/-- The source point of a map into the family, over the parameter of a second map with the
same parameter. -/
def pairPoint (a c : U ⟶ (relativeSpace A.X.hom).obj T)
    (hc : c ≫ pullback.fst T.hom A.X.hom = a ≫ pullback.fst T.hom A.X.hom) :
    (Over.map T.hom).obj (pairParameter a) ⟶ A.X :=
  Over.homMk (c ≫ pullback.snd T.hom A.X.hom) (by
    simp only [Over.map_obj_hom, Over.mk_hom, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, hc, Category.assoc])

lemma pair_fst_eq (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) :
    b ≫ pullback.fst T.hom A.X.hom = a ≫ pullback.fst T.hom A.X.hom := by
  have := congrArg (· ≫ pullback.fst T.hom B.X.hom) h
  simpa only [Category.assoc, homFamilySpaceMap_fst] using this.symm

lemma pair_snd_hom (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) :
    pairPoint a b (pair_fst_eq f a b h) ≫ (groupHom f).hom.hom =
      pairPoint a a rfl ≫ (groupHom f).hom.hom := by
  ext
  have := congrArg (· ≫ pullback.snd T.hom B.X.hom) h
  simp only [Category.assoc, homFamilySpaceMap_snd] at this
  simpa [pairPoint] using this.symm

/-- The kernel point carrying the first map of an equal-composite pair to the second. -/
def pairKernelPoint (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) :
    (Over.map T.hom).obj (pairParameter a) ⟶ (GroupScheme.kernel (groupHom f)).X :=
  (GroupScheme.kernelPointsEquiv (groupHom f) _).symm
    ⟨pairPoint a b (pair_fst_eq f a b h) * (pairPoint a a rfl)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change pairPoint a b (pair_fst_eq f a b h) ≫ (groupHom f).hom.hom *
        (pairPoint a a rfl ≫ (groupHom f).hom.hom)⁻¹ = 1
      rw [pair_snd_hom f a b h, mul_inv_cancel]⟩

lemma pairKernelPoint_ι (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) :
    pairKernelPoint f a b h ≫ (GroupScheme.kernelι (groupHom f)).hom.hom =
      pairPoint a b (pair_fst_eq f a b h) * (pairPoint a a rfl)⁻¹ := by
  rw [← GroupScheme.kernelPointsEquiv_val, pairKernelPoint, MulEquiv.apply_symm_apply]

/-- The section `U ⟶ U ×_S A` given by the identity and the second component of `a`. -/
def pairSection (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    U ⟶ (relativeSpace A.X.hom).obj ((Over.map T.hom).obj (pairParameter a)) :=
  pullback.lift (𝟙 U) (a ≫ pullback.snd T.hom A.X.hom) (by
    simp only [Over.map_obj_hom, Over.mk_hom, Category.id_comp, Category.assoc,
      pullback.condition])

@[reassoc (attr := simp)]
lemma pairSection_fst (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    pairSection a ≫ pullback.fst _ A.X.hom = 𝟙 U :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairSection_snd (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    pairSection a ≫ pullback.snd _ A.X.hom = a ≫ pullback.snd T.hom A.X.hom :=
  pullback.lift_snd _ _ _

/-- The section recovers the first map through the ordinary change of parameter. -/
lemma pairSection_map (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    pairSection a ≫ (relativeSpace A.X.hom).map (kernelCharacterParameter (pairParameter a)) =
      a := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeSpace_map_fst, pairSection_fst_assoc]
    rfl
  · rw [Category.assoc, relativeSpace_map_snd, pairSection_snd]

/-- The section as a morphism over `S`. -/
def pairSectionOver (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    (Over.map T.hom).obj (pairParameter a) ⟶
      relativeOver A ((Over.map T.hom).obj (pairParameter a)) :=
  Over.homMk (pairSection a) (by
    simp only [Over.mk_hom, ← Category.assoc, pairSection_fst, Category.id_comp])

lemma pairSectionOver_fst (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    pairSectionOver a ≫ relativeFst A _ = 𝟙 _ := by
  ext
  exact pairSection_fst a

lemma pairSectionOver_snd (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    pairSectionOver a ≫ relativeSnd A _ = pairPoint a a rfl := by
  ext
  exact pairSection_snd a

/-- The section carries the kernel translation by the pair's kernel point to the second map. -/
lemma pairSection_kernelShear (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) :
    pairSection a ≫ kernelShear f (kernelCharacterParameter (pairParameter a))
      (pairKernelPoint f a b h) = b := by
  apply pullback.hom_ext
  · rw [Category.assoc, kernelShear_fst, pairSection_fst_assoc]
    exact (pair_fst_eq f a b h).symm
  · rw [Category.assoc, kernelShear, shear_snd]
    change (pairSectionOver a ≫ ((relativeFst A _ ≫ pairKernelPoint f a b h ≫
      (GroupScheme.kernelι (groupHom f)).hom.hom) * relativeSnd A _)).left = _
    rw [MonObj.comp_mul, reassoc_of% pairSectionOver_fst, pairSectionOver_snd,
      pairKernelPoint_ι, inv_mul_cancel_right]
    rfl

/-- Every comparison scalar along `f_T` is the pullback of a kernel-translation scalar. -/
lemma structureAutScalar_equalCompositeUnitAut_eq {M : ((relativeSpace B.X.hom).obj T).Modules}
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
      structureModule ((relativeSpace A.X.hom).obj T))
    (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) :
    structureAutScalar (equalCompositeUnitAut ((homFamilySpaceMap f).app T) a b h α) =
      Units.map (pairSection a).appTop.hom.toMonoidHom
        (kernelTranslationScalar f α (kernelCharacterParameter (pairParameter a))
          (pairKernelPoint f a b h)) := by
  let t := kernelCharacterParameter (pairParameter a)
  let k := pairKernelPoint f a b h
  have h' : (pairSection a ≫ (relativeSpace A.X.hom).map t) ≫ (homFamilySpaceMap f).app T =
      (pairSection a ≫ kernelShear f t k) ≫ (homFamilySpaceMap f).app T := by
    rw [pairSection_map, pairSection_kernelShear]
    exact h
  rw [equalCompositeUnitAut_congr _ (pairSection_map a).symm
    (pairSection_kernelShear f a b h).symm h h',
    equalCompositeUnitAut_precomp _ _ _ α (pairSection a)
      (kernelShear_homFamilySpaceMap f t k).symm h']
  exact structureAutScalar_pullback (pairSection a) (kernelTranslationAut f α t k)

end Langlands.AbelianScheme
