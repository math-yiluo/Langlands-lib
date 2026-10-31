import Langlands.AbelianScheme.IntrinsicKernelCharacter

/-! # Kernel translation units through restriction to points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)
  {T : Over S} {M : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))

/-- The point `(a, c)` of the source family `T ×_S A` determined by a parameter map and a
point of `A` on the same test scheme. -/
def familyPoint {U : Over S} (a : U ⟶ T) (c : U ⟶ A.X) :
    U.left ⟶ (relativeSpace A.X.hom).obj T :=
  pullback.lift a.left c.left (by rw [Over.w a, Over.w c])

/-- Restricting the kernel translation to the unit section gives the point `(a, k)`. -/
lemma relativeSection_kernelShear {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U ≫ kernelShear f a k =
      familyPoint a (k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom) :=
  relativeSection_shear A a _

/-- Restricting the change of parameter to the unit section gives the point `(a, 1)`. -/
lemma relativeSection_relativeSpace_map {U : Over S} (a : U ⟶ T) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U ≫
        (relativeSpace A.X.hom).map a =
      familyPoint a (1 : U ⟶ A.X) := by
  rw [← shear_one A a]
  exact relativeSection_shear A a 1

/-- The two points `(a, 1)` and `(a, k)` have the same image under `f × T`. -/
lemma familyPoint_kernel_homFamilySpaceMap {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    familyPoint a (1 : U ⟶ A.X) ≫ (homFamilySpaceMap f).app T =
      familyPoint a (k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom) ≫
        (homFamilySpaceMap f).app T := by
  rw [← relativeSection_kernelShear, ← relativeSection_relativeSpace_map, Category.assoc,
    Category.assoc, kernelShear_homFamilySpaceMap]

/-- The descended kernel-translation unit is the scalar comparing the trivialization `α`
at the points `(a, 1)` and `(a, k)` of the source family, which have the same image in the
target family. -/
theorem kernelTranslationUnit_eq_point_comparison (h : UniversalGlobalFunctions A)
    {U : Over S} (a : U ⟶ T) (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f α h a k =
      structureAutScalar (equalCompositeUnitAut ((homFamilySpaceMap f).app T)
        (familyPoint a (1 : U ⟶ A.X))
        (familyPoint a (k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom))
        (familyPoint_kernel_homFamilySpaceMap f a k) α) := by
  rw [kernelTranslationUnit, relativeUnitDescend_eq_section, kernelTranslationScalar,
    ← structureAutScalar_pullback]
  congr 1
  unfold structureAutPullback kernelTranslationAut
  have hq := equalCompositeUnitAut_precomp ((homFamilySpaceMap f).app T)
    ((relativeSpace A.X.hom).map a) (kernelShear f a k) α
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U)
    (kernelShear_homFamilySpaceMap f a k).symm
    (by rw [Category.assoc, Category.assoc, kernelShear_homFamilySpaceMap])
  refine hq.symm.trans ?_
  congr 1
  · exact relativeSection_relativeSpace_map a
  · exact relativeSection_kernelShear f a k

/-- The descended kernel-translation unit is the scalar of the comparison automorphism
restricted along the unit section of the source family over `U`. -/
theorem kernelTranslationUnit_eq_section_comparison (h : UniversalGlobalFunctions A)
    {U : Over S} (a : U ⟶ T) (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f α h a k =
      structureAutScalar (equalCompositeUnitAut ((homFamilySpaceMap f).app T)
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U ≫
          (relativeSpace A.X.hom).map a)
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U ≫
          kernelShear f a k)
        (by rw [Category.assoc, Category.assoc, kernelShear_homFamilySpaceMap]) α) := by
  rw [kernelTranslationUnit, relativeUnitDescend_eq_section, kernelTranslationScalar,
    ← structureAutScalar_pullback]
  congr 1
  unfold structureAutPullback kernelTranslationAut
  exact (equalCompositeUnitAut_precomp ((homFamilySpaceMap f).app T)
    ((relativeSpace A.X.hom).map a) (kernelShear f a k) α
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U)
    (kernelShear_homFamilySpaceMap f a k).symm
    (by rw [Category.assoc, Category.assoc, kernelShear_homFamilySpaceMap])).symm

/-- If the comparison automorphism along the unit section `e` of `T ×_S A` and its
translate `e ≫ kernelShear f (𝟙 T) k` is the identity, then the kernel-translation unit of
`k` at the identity parameter is `1`. -/
theorem kernelTranslationUnit_eq_one_of_section (h : UniversalGlobalFunctions A)
    (k : T ⟶ (GroupScheme.kernel (groupHom f)).X)
    (hk : equalCompositeUnitAut ((homFamilySpaceMap f).app T)
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear f (𝟙 T) k)
      (by rw [Category.assoc, kernelShear_homFamilySpaceMap, CategoryTheory.Functor.map_id,
        Category.id_comp]) α = Iso.refl _) :
    kernelTranslationUnit f α h (𝟙 T) k = 1 := by
  rw [kernelTranslationUnit_eq_section_comparison]
  have he : (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
      (relativeSpace A.X.hom).map (𝟙 T) =
        (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T := by
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hc : ∀ (b : T.left ⟶ (relativeSpace A.X.hom).obj T)
      (hb : b = (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
      (hh : b ≫ (homFamilySpaceMap f).app T =
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
          kernelShear f (𝟙 T) k) ≫ (homFamilySpaceMap f).app T),
      equalCompositeUnitAut ((homFamilySpaceMap f).app T) b
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
          kernelShear f (𝟙 T) k) hh α = Iso.refl _ := by
    intro b hb hh
    subst hb
    exact hk
  rw [hc _ he]
  exact structureAutScalar_refl

/-- A kernel point whose kernel-translation unit at the identity parameter is trivial is
evaluated to `1` by the intrinsic kernel character. -/
theorem characterEvaluation_intrinsicKernelCharacter_eq_one
    (h : UniversalGlobalFunctions A) (x : T ⟶ (kernelCommGroupScheme f).X)
    (hx : kernelTranslationUnit f α h (𝟙 T) x = 1) :
    Cartier.characterEvaluation (intrinsicKernelCharacter f α h) x = 1 := by
  apply (Gm.pointsEquiv S T).injective
  rw [← Cartier.characterEvaluation_section, characterHomEquiv_intrinsicKernelCharacter,
    intrinsicKernelCharacterHom_points]
  have hb : baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp
      (Over.mk (𝟙 T.left)) ((Cartier.sectionPointsEquiv (kernelCommGroupScheme f) T).symm x) =
        (Cartier.sectionBaseIso T).hom ≫ x := by
    rw [← Iso.inv_comp_eq]
    exact (Cartier.sectionPointsEquiv (kernelCommGroupScheme f) T).apply_symm_apply x
  have hp : kernelCharacterParameter (T := T) (Over.mk (𝟙 T.left)) =
      (Cartier.sectionBaseIso T).hom ≫ 𝟙 T := by
    ext
    simp [kernelCharacterParameter, Cartier.sectionBaseIso]
  rw [hb, hp, kernelTranslationUnit_precomp, hx, map_one, map_one]

end Langlands.AbelianScheme
