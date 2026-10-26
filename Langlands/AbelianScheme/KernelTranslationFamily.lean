import Langlands.AlgebraicGeometry.Picard.PoincareSquare
import Langlands.AlgebraicGeometry.Picard.HomFamilyPullback

/-! # Translation of relative families by actual kernel points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- A shear map, regarded as a morphism of schemes over the original base. -/
def shearOver (A : AbelianScheme S) {U T : Over S} (a : U ⟶ T) (c : U ⟶ A.X) :
    relativeOver A U ⟶ relativeOver A T :=
  Over.homMk (shear A a c) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, shear_fst, Category.assoc, Over.w])

@[reassoc (attr := simp)]
lemma shearOver_fst (A : AbelianScheme S) {U T : Over S}
    (a : U ⟶ T) (c : U ⟶ A.X) :
    shearOver A a c ≫ relativeFst A T = relativeFst A U ≫ a := by
  ext
  exact shear_fst A a c

@[reassoc (attr := simp)]
lemma shearOver_snd (A : AbelianScheme S) {U T : Over S}
    (a : U ⟶ T) (c : U ⟶ A.X) :
    shearOver A a c ≫ relativeSnd A T =
      (relativeFst A U ≫ c) * relativeSnd A U := by
  ext
  exact shear_snd A a c

/-- Composition of shears is multiplication of their translation parameters. -/
lemma shear_comp (A : AbelianScheme S) {V U T : Over S}
    (a : V ⟶ U) (b : U ⟶ T) (c : V ⟶ A.X) (d : U ⟶ A.X) :
    shear A a c ≫ shear A b d = shear A (a ≫ b) ((a ≫ d) * c) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, shear_fst, shear_fst_assoc, Over.comp_left]
  · rw [Category.assoc, shear_snd, shear_snd]
    change (shearOver A a c ≫ ((relativeFst A U ≫ d) * relativeSnd A U)).left = _
    rw [MonObj.comp_mul, shearOver_fst_assoc, shearOver_snd,
      MonObj.comp_mul, ← Category.assoc]
    rw [mul_assoc]

/-- Translation of a relative family commutes with a homomorphism. -/
lemma shear_homFamilySpaceMap (f : A ⟶ B) {U T : Over S}
    (a : U ⟶ T) (c : U ⟶ A.X) :
    shear A a c ≫ (homFamilySpaceMap f).app T =
      (homFamilySpaceMap f).app U ≫ shear B a (c ≫ (groupHom f).hom.hom) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, homFamilySpaceMap_fst, shear_fst,
      homFamilySpaceMap_fst_assoc]
  · rw [Category.assoc, homFamilySpaceMap_snd, shear_snd_assoc,
      Category.assoc, shear_snd]
    let m : relativeOver A U ⟶ relativeOver B U :=
      Over.homMk ((homFamilySpaceMap f).app U) (by
        simp only [Over.mk_hom]
        rw [homFamilySpaceMap_fst_assoc])
    have hm₁ : m ≫ relativeFst B U = relativeFst A U := by
      ext
      exact homFamilySpaceMap_fst f U
    have hm₂ : m ≫ relativeSnd B U = relativeSnd A U ≫ (groupHom f).hom.hom := by
      ext
      exact homFamilySpaceMap_snd f U
    change (((relativeFst A U ≫ c) * relativeSnd A U) ≫
      (groupHom f).hom.hom).left =
      (m ≫ ((relativeFst B U ≫ c ≫ (groupHom f).hom.hom) * relativeSnd B U)).left
    rw [MonObj.mul_comp, MonObj.comp_mul, reassoc_of% hm₁, hm₂, Category.assoc]

/-- The actual translation map on the source family by a point of the actual kernel. -/
def kernelShear (f : A ⟶ B) {U T : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    (relativeSpace A.X.hom).obj U ⟶ (relativeSpace A.X.hom).obj T :=
  shear A a (k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom)

/-- Kernel translation has the prescribed map on the parameter schemes. -/
@[reassoc (attr := simp)]
lemma kernelShear_fst (f : A ⟶ B) {U T : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelShear f a k ≫ pullback.fst T.hom A.X.hom =
      pullback.fst U.hom A.X.hom ≫ a.left :=
  shear_fst A a _

/-- The unit point acts by the ordinary change-of-parameter map. -/
@[simp]
lemma kernelShear_one (f : A ⟶ B) {U T : Over S} (a : U ⟶ T) :
    kernelShear f a 1 = (relativeSpace A.X.hom).map a := by
  simp only [kernelShear, MonObj.one_comp, shear_one]

/-- Kernel translation leaves the actual homomorphism pullback map unchanged. -/
lemma kernelShear_homFamilySpaceMap (f : A ⟶ B) {U T : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelShear f a k ≫ (homFamilySpaceMap f).app T =
      (relativeSpace A.X.hom).map a ≫ (homFamilySpaceMap f).app T := by
  rw [kernelShear, shear_homFamilySpaceMap]
  have hk : (k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom) ≫
      (groupHom f).hom.hom = 1 :=
    (GroupScheme.kernelPointsEquiv (groupHom f) U k).property
  rw [hk, shear_one]
  exact ((homFamilySpaceMap f).naturality a).symm

/-- Kernel translations are natural in a further parameter map. -/
lemma relativeSpace_map_kernelShear (f : A ⟶ B) {V U T : Over S}
    (h : V ⟶ U) (a : U ⟶ T) (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    (relativeSpace A.X.hom).map h ≫ kernelShear f a k =
      kernelShear f (h ≫ a) (h ≫ k) := by
  simpa only [kernelShear, Category.assoc] using
    relativeSpace_map_shear A h a (k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom)

/-- Composition of kernel translations is multiplication of kernel points. -/
lemma kernelShear_comp (f : A ⟶ B) {V U T : Over S}
    (a : V ⟶ U) (b : U ⟶ T)
    (k : V ⟶ (GroupScheme.kernel (groupHom f)).X)
    (l : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelShear f a k ≫ kernelShear f b l =
      kernelShear f (a ≫ b) ((a ≫ l) * k) := by
  simp only [kernelShear, shear_comp, MonObj.mul_comp, Category.assoc]

end Langlands.AbelianScheme
