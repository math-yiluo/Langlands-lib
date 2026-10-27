import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AbelianScheme.KernelTranslationFamily
import Langlands.AbelianScheme.RelativeGlobalUnits
import Langlands.AbelianScheme.TrivialHomPullbackFamilies

/-! # Intrinsic scalar of kernel translation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)
  {T : Over S} {M : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))

/-- Transport the canonical equal-composite comparison from ordinary pullback to
kernel translation through the actual trivialization. -/
def kernelTranslationAut {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    structureModule ((relativeSpace A.X.hom).obj U) ≅
      structureModule ((relativeSpace A.X.hom).obj U) :=
  equalCompositeUnitAut ((homFamilySpaceMap f).app T)
    ((relativeSpace A.X.hom).map a) (kernelShear f a k)
    (kernelShear_homFamilySpaceMap f a k).symm α

/-- The global unit by which the transported kernel action acts on the structure module. -/
def kernelTranslationScalar {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    Γ((relativeSpace A.X.hom).obj U, ⊤)ˣ :=
  structureAutScalar (kernelTranslationAut f α a k)

/-- The unique unit on the parameter scheme inducing the transported action. -/
def kernelTranslationUnit (h : UniversalGlobalFunctions A) {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) : Γ(U.left, ⊤)ˣ :=
  relativeUnitDescend A h U (kernelTranslationScalar f α a k)

/-- Evaluation of the descended unit recovers the actual transported action scalar. -/
@[simp]
lemma relativeUnitsPullback_kernelTranslationUnit (h : UniversalGlobalFunctions A)
    {U : Over S} (a : U ⟶ T) (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    relativeUnitsPullback A U (kernelTranslationUnit f α h a k) =
      kernelTranslationScalar f α a k :=
  relativeUnitsPullback_descend A h U _

@[simp]
lemma kernelTranslationAut_one {U : Over S} (a : U ⟶ T) :
    kernelTranslationAut f α a 1 = Iso.refl _ := by
  unfold kernelTranslationAut
  simpa only [kernelShear_one, structureModule] using
    equalCompositeUnitAut_refl ((homFamilySpaceMap f).app T)
      ((relativeSpace A.X.hom).map a) α rfl

@[simp]
lemma kernelTranslationScalar_one {U : Over S} (a : U ⟶ T) :
    kernelTranslationScalar f α a 1 = 1 := by
  simp [kernelTranslationScalar]

@[simp]
lemma kernelTranslationUnit_one (h : UniversalGlobalFunctions A)
    {U : Over S} (a : U ⟶ T) :
    kernelTranslationUnit f α h a 1 = 1 := by
  simp [kernelTranslationUnit]

/-- Naturality of the actual normalized automorphism in a further parameter map. -/
lemma kernelTranslationAut_precomp {V U : Over S} (b : V ⟶ U) (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationAut f α (b ≫ a) (b ≫ k) =
      structureAutPullback ((relativeSpace A.X.hom).map b)
        (kernelTranslationAut f α a k) := by
  unfold kernelTranslationAut structureAutPullback
  simpa only [← (relativeSpace A.X.hom).map_comp, relativeSpace_map_kernelShear] using
    equalCompositeUnitAut_precomp ((homFamilySpaceMap f).app T)
      ((relativeSpace A.X.hom).map a) (kernelShear f a k) α
      ((relativeSpace A.X.hom).map b) (kernelShear_homFamilySpaceMap f a k).symm
      (by simp only [Category.assoc, kernelShear_homFamilySpaceMap])

/-- Naturality of the global unit on the actual relative family. -/
lemma kernelTranslationScalar_precomp {V U : Over S} (b : V ⟶ U) (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationScalar f α (b ≫ a) (b ≫ k) =
      Units.map ((relativeSpace A.X.hom).map b).appTop.hom.toMonoidHom
        (kernelTranslationScalar f α a k) := by
  simp only [kernelTranslationScalar, kernelTranslationAut_precomp,
    structureAutScalar_pullback]

/-- Naturality of the descended unit in every further parameter map. -/
lemma kernelTranslationUnit_precomp (h : UniversalGlobalFunctions A)
    {V U : Over S} (b : V ⟶ U) (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f α h (b ≫ a) (b ≫ k) =
      Units.map b.left.appTop.hom.toMonoidHom (kernelTranslationUnit f α h a k) := by
  unfold kernelTranslationUnit
  rw [kernelTranslationScalar_precomp, relativeUnitDescend_naturality]

/-- The normalized automorphism satisfies the translation cocycle law. -/
lemma kernelTranslationAut_mul {U : Over S} (a : U ⟶ T)
    (k l : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationAut f α a (k * l) =
      kernelTranslationAut f α a k ≪≫
        structureAutPullback (kernelShear f (𝟙 U) k) (kernelTranslationAut f α a l) := by
  let p := (homFamilySpaceMap f).app T
  let r := kernelShear f (𝟙 U) k
  have hq : r ≫ (relativeSpace A.X.hom).map a = kernelShear f a k := by
    simpa only [r, kernelShear_one, Category.id_comp, MonObj.comp_one, one_mul] using
      kernelShear_comp f (𝟙 U) a k 1
  have hc : r ≫ kernelShear f a l = kernelShear f a (k * l) := by
    simpa only [r, Category.id_comp, mul_comm] using kernelShear_comp f (𝟙 U) a k l
  have hp :
      equalCompositeUnitAut p (kernelShear f a k) (kernelShear f a (k * l))
        ((kernelShear_homFamilySpaceMap f a k).trans
          (kernelShear_homFamilySpaceMap f a (k * l)).symm) α =
      structureAutPullback r (kernelTranslationAut f α a l) := by
    simpa only [hq, hc, kernelTranslationAut, structureAutPullback, p] using
      equalCompositeUnitAut_precomp p ((relativeSpace A.X.hom).map a)
        (kernelShear f a l) α r (kernelShear_homFamilySpaceMap f a l).symm
        (by dsimp only [p]; simp only [Category.assoc, kernelShear_homFamilySpaceMap])
  have ht := equalCompositeUnitAut_trans p ((relativeSpace A.X.hom).map a)
    (kernelShear f a k) (kernelShear f a (k * l)) α
    (kernelShear_homFamilySpaceMap f a k).symm
    ((kernelShear_homFamilySpaceMap f a k).trans
      (kernelShear_homFamilySpaceMap f a (k * l)).symm)
    (kernelShear_homFamilySpaceMap f a (k * l)).symm
  rw [hp] at ht
  exact ht.symm

/-- Multiplication of kernel points multiplies the units on the parameter scheme. -/
lemma kernelTranslationUnit_mul (h : UniversalGlobalFunctions A)
    {U : Over S} (a : U ⟶ T) (k l : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f α h a (k * l) =
      kernelTranslationUnit f α h a k * kernelTranslationUnit f α h a l := by
  unfold kernelTranslationUnit kernelTranslationScalar
  rw [kernelTranslationAut_mul, structureAutScalar_trans, map_mul,
    structureAutScalar_pullback, relativeUnitDescend_map A h (𝟙 U)
      (kernelShear f (𝟙 U) k) (kernelShear_fst f (𝟙 U) k)]
  rfl

end Langlands.AbelianScheme
