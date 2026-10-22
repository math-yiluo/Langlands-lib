import Langlands.Geometry.EtaleAutomorphism
import Langlands.Geometry.EtaleDerivedSections
import Langlands.Cohomology.TranslationAction
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Group actions on étale cohomology through automorphisms of the scheme

A group acting on a scheme `Y` by automorphisms acts on the small étale site of
`Y` and on its étale module sheaves by translation. For an equivariant étale
module sheaf, the group acts on its étale cohomology in every degree. This is
the general form of the action of a Galois group on the étale cohomology of a
base change to a separable closure.
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry.EtaleAutomorphism Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]

/-- Sections over the terminal object of the small étale site. -/
abbrev sectionsTop : EtaleDerivedSections.ModuleSheaf Y R ⥤ ModuleCat.{u} R :=
  (sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Y.Etale))

variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The automorphism of `Y` attached to a group element. The action on the
site is contravariant in the automorphism, so a homomorphism into the opposite
of the automorphism group gives a left action on cohomology. -/
abbrev aut (g : G) : Y ≅ Y := (ρ g).unop

theorem aut_mul (g h : G) : aut ρ (g * h) = aut ρ g ≪≫ aut ρ h := by
  simp only [aut, map_mul, MulOpposite.unop_mul]
  rfl

theorem aut_one : aut ρ 1 = Iso.refl Y := by
  simp only [aut, map_one, MulOpposite.unop_one]
  rfl

/-- The translation functor of a group element on étale module sheaves. -/
abbrev translateBy (g : G) :
    EtaleDerivedSections.ModuleSheaf Y R ⥤ EtaleDerivedSections.ModuleSheaf Y R :=
  translate (ModuleCat.{u} R) (aut ρ g)

instance : (sectionsTop (Y := Y) R).Additive where
  map_add := rfl

/-- Translating by `h` and then by `g` is translating by `g * h`. -/
def compIso (g h : G) : translateBy R ρ h ⋙ translateBy R ρ g ≅ translateBy R ρ (g * h) :=
  translateComp (ModuleCat.{u} R) (aut ρ h) (aut ρ g) ≪≫
    translateCongr (ModuleCat.{u} R) (aut_mul ρ g h).symm

/-- Translating by `1` is the identity. -/
def oneIso : translateBy R ρ 1 ≅ 𝟭 (EtaleDerivedSections.ModuleSheaf Y R) :=
  translateCongr (ModuleCat.{u} R) (aut_one ρ) ≪≫ translateId (ModuleCat.{u} R)

theorem sections_compIso (g h : G) (X : EtaleDerivedSections.ModuleSheaf Y R) :
    (sectionsIso (ModuleCat.{u} R) (aut ρ g)).hom.app ((translateBy R ρ h).obj X) ≫
        (sectionsIso (ModuleCat.{u} R) (aut ρ h)).hom.app X =
      (sectionsTop R).map ((compIso R ρ g h).hom.app X) ≫
        (sectionsIso (ModuleCat.{u} R) (aut ρ (g * h))).hom.app X := by
  rw [sectionsIso_comp, sectionsIso_congr (ModuleCat.{u} R) (aut_mul ρ g h).symm]
  simp only [compIso, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]

theorem sections_oneIso (X : EtaleDerivedSections.ModuleSheaf Y R) :
    (sectionsIso (ModuleCat.{u} R) (aut ρ 1)).hom.app X =
      (sectionsTop R).map ((oneIso R ρ).hom.app X) := by
  rw [sectionsIso_congr (ModuleCat.{u} R) (aut_one ρ), sectionsIso_id]
  simp only [oneIso, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp]

/-- The translation data of the action. -/
def data : TranslationAction.Data (sectionsTop (Y := Y) R) (translateBy R ρ) where
  sections g := sectionsIso (ModuleCat.{u} R) (aut ρ g)
  comp := compIso R ρ
  one := oneIso R ρ
  sections_comp := sections_compIso R ρ
  sections_one := sections_oneIso R ρ

/-- An étale module sheaf with compatible structure maps from its translates
under the action of `G`. -/
abbrev EquivariantSheaf := TranslationAction.Equivariant (data R ρ)

/-- The action of `G` on degree `n` étale cohomology of an equivariant étale
module sheaf, computed with the chosen injective resolution. -/
def cohomologyRep (F : EquivariantSheaf R ρ) (n : ℕ) : Rep.{u} R G :=
  (Rep.ActionToRep R G).obj
    (TranslationAction.cohomologyAction (sectionsTop R) F (injectiveResolution F.obj) n)

/-- The module underlying the action is the published étale cohomology
`EtaleDerivedSections.cohomology Y R n` of the underlying sheaf. -/
def cohomologyIso (F : EquivariantSheaf R ρ) (n : ℕ) :
    (TranslationAction.cohomologyAction (sectionsTop R) F (injectiveResolution F.obj) n).V ≅
      (EtaleDerivedSections.cohomology Y R n).obj F.obj :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((NatIso.mapHomologicalComplex (EtaleDerivedSections.sectionsIso Y R) _).app
        (injectiveResolution F.obj).cocomplex).symm ≪≫
    (EtaleDerivedSections.cohomologyIso Y R F.obj n).symm

end Langlands.Geometry.EtaleCohomologyAction
