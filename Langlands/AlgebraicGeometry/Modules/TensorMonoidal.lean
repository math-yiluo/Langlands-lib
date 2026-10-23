import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Modules.TensorLocalizationProof
import Mathlib.CategoryTheory.Localization.Monoidal.Braided

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace Langlands.Scheme.Modules

variable (X : AlgebraicGeometry.Scheme.{u})

/-- The sectionwise tensor structure on scheme-module presheaves. -/
instance presheafTensorMonoidalCategory : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

/-- The sectionwise symmetry on scheme-module presheaves. -/
instance presheafTensorSymmetricCategory : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

abbrev tensorLocalEquivalences : MorphismProperty X.PresheafOfModules :=
  (Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

local instance : (sheafify X).IsLocalization (tensorLocalEquivalences X) :=
  inferInstanceAs ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
    ((Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)))

/-- The chosen structure sheaf is the sheafification of the presheaf tensor unit. -/
def sheafifyTensorUnitIso : (sheafify X).obj (𝟙_ X.PresheafOfModules) ≅ structureSheaf X :=
  (sheafifyForgetIso X).app (structureSheaf X)

local instance : (tensorLocalEquivalences X).IsMonoidal :=
  tensorLocalEquivalencesIsMonoidal X

/-- The monoidal structure on module sheaves obtained by sheafification localization. -/
instance tensorMonoidalCategory : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal (sheafify X)
    (tensorLocalEquivalences X) (sheafifyTensorUnitIso X)))


/-- Symmetry transported through monoidal localization. -/
instance tensorSymmetricCategory : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal (sheafify X)
    (tensorLocalEquivalences X) (sheafifyTensorUnitIso X)))


/-- Module sheafification is strong monoidal for the localized structure. -/
instance sheafifyMonoidal : (sheafify X).Monoidal :=
  inferInstanceAs ((CategoryTheory.Localization.Monoidal.toMonoidalCategory (sheafify X)
    (tensorLocalEquivalences X) (sheafifyTensorUnitIso X)).Monoidal)


/-- Module sheafification preserves the braiding for the localized structure. -/
instance sheafifyBraided : (sheafify X).Braided :=
  inferInstanceAs ((CategoryTheory.Localization.Monoidal.toMonoidalCategory (sheafify X)
    (tensorLocalEquivalences X) (sheafifyTensorUnitIso X)).Braided)

/-- The localized tensor agrees with the explicitly sheafified tensor. -/
def localizedTensorIso (M N : X.Modules) : M ⊗ N ≅ tensorObj M N :=
  tensorIso ((sheafifyForgetIso X).app M).symm ((sheafifyForgetIso X).app N).symm ≪≫
    CategoryTheory.Localization.Monoidal.μ (sheafify X) (tensorLocalEquivalences X)
      (sheafifyTensorUnitIso X) M.val N.val

/-- The comparison with the explicit tensor is natural in both factors. -/
def localizedTensorNatIso : tensor X.Modules ≅ tensorFunctor X :=
  Functor.isoWhiskerRight
      (NatIso.prod (sheafifyForgetIso X).symm (sheafifyForgetIso X).symm) (tensor X.Modules) ≪≫
    Functor.isoWhiskerLeft
      ((AlgebraicGeometry.Scheme.Modules.toPresheafOfModules X).prod
        (AlgebraicGeometry.Scheme.Modules.toPresheafOfModules X))
      (Functor.Monoidal.μNatIso (sheafify X))

end Langlands.Scheme.Modules
