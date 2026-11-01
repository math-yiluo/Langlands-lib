import Langlands.AbelianScheme.PolarizedFiniteLevel.Base
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-! # The canonical integer-localization base of ordinary level moduli -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

namespace LevelBase

variable {n : ℕ}

/-- Any two morphisms to `Spec ℤ[1/n]` coincide, on an arbitrary actual scheme. -/
theorem localization_hom_ext {S : Scheme.{0}}
    (f g : S ⟶ Spec (CommRingCat.of (Localization.Away (n : ℤ)))) : f = g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (n : ℤ))
  exact Subsingleton.elim _ _

/-- The ring map from `ℤ[1/n]` to the global functions on an ordinary level base. -/
def localizationToGlobalSections (S : LevelBase n) :
    Localization.Away (n : ℤ) →+* Γ(S.obj, ⊤) :=
  IsLocalization.Away.lift (n : ℤ)
    (g := Int.castRingHom Γ(S.obj, ⊤)) (by simpa using S.level_isUnit)

/-- The canonical structure map to the integer localization. -/
def toLocalizationSpec (S : LevelBase n) :
    S.obj ⟶ Spec (CommRingCat.of (Localization.Away (n : ℤ))) :=
  S.obj.toSpecΓ ≫ Spec.map (CommRingCat.ofHom S.localizationToGlobalSections)

/-- Every supplied structure map to this base is the canonical one. -/
theorem eq_toLocalizationSpec (S : LevelBase n)
    (f : S.obj ⟶ Spec (CommRingCat.of (Localization.Away (n : ℤ)))) :
    f = S.toLocalizationSpec :=
  localization_hom_ext f S.toLocalizationSpec

/-- Every actual morphism between ordinary level bases respects the canonical base. -/
@[reassoc (attr := simp)]
theorem toLocalizationSpec_naturality {S T : LevelBase n} (f : S.obj ⟶ T.obj) :
    f ≫ T.toLocalizationSpec = S.toLocalizationSpec :=
  localization_hom_ext _ _

/-- The affine integer localization is itself an object of the full test category. -/
def localizationSpec (n : ℕ) : LevelBase n :=
  ofScheme (Spec (CommRingCat.of (Localization.Away (n : ℤ)))) (by
    simpa using
      (IsLocalization.Away.algebraMap_isUnit (n : ℤ) (S := Localization.Away (n : ℤ))).map
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (n : ℤ)))).inv.hom)

/-- The test category has `Spec ℤ[1/n]` as a terminal object. -/
def localizationSpecIsTerminal (n : ℕ) : IsTerminal (localizationSpec n) :=
  IsTerminal.ofUniqueHom (fun S => homMk S.toLocalizationSpec) (fun S f => by
    apply (homEquiv S (localizationSpec n)).injective
    exact localization_hom_ext _ _)

/-- Regard an ordinary level base as an actual scheme over `Spec ℤ[1/n]`. -/
def toOverLocalization (n : ℕ) :
    LevelBase n ⥤ Over (Spec (CommRingCat.of (Localization.Away (n : ℤ)))) where
  obj S := Over.mk S.toLocalizationSpec
  map f := Over.homMk f.hom (toLocalizationSpec_naturality f.hom)

/-- Imposing the canonical structure maps removes no morphisms. -/
def overHomEquiv (S T : LevelBase n) :
    ((toOverLocalization n).obj S ⟶ (toOverLocalization n).obj T) ≃ (S ⟶ T) where
  toFun f := homMk f.left
  invFun f := (toOverLocalization n).map f
  left_inv f := by
    ext
    rfl
  right_inv f := rfl

end LevelBase

end Langlands.AbelianScheme.PolarizedFiniteLevel
