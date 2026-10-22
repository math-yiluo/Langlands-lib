import Langlands.Geometry.EtaleCohomologyAction
import Langlands.Cohomology.TranslationCoaction

/-!
# Group actions on étale cohomology with constant coefficients

A group acting on a scheme by automorphisms acts on the étale cohomology of
constant module sheaves. The constant sheaf carries canonical structure maps
into its translates: under the constant-sheaf adjunction they correspond to
the unit followed by the comparison of sections of a translate with sections.
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry.EtaleAutomorphism Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The constant étale module sheaf. -/
abbrev constant (M : ModuleCat.{u} R) : EtaleDerivedSections.ModuleSheaf Y R :=
  (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M

/-- Mathlib's adjunction between constant sheaves and sections over the
terminal object. -/
abbrev constantAdj :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R) ⊣ sectionsTop (Y := Y) R :=
  constantSheafAdj _ _ terminalIsTerminal

/-- The canonical structure map of the constant sheaf into its translate by
`g`. -/
def constantCoact (M : ModuleCat.{u} R) (g : G) :
    constant (Y := Y) R M ⟶ (translateBy R ρ g).obj (constant R M) :=
  ((constantAdj R).homEquiv _ _).symm
    ((constantAdj R).unit.app M ≫ ((data R ρ).sections g).inv.app (constant R M))

@[reassoc]
theorem unit_comp_map_constantCoact (M : ModuleCat.{u} R) (g : G) :
    (constantAdj (Y := Y) R).unit.app M ≫ (sectionsTop R).map (constantCoact R ρ M g) =
      (constantAdj R).unit.app M ≫ ((data R ρ).sections g).inv.app (constant R M) := by
  exact ((constantAdj R).homEquiv_unit _ _ (constantCoact R ρ M g)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The constant sheaf with its canonical structure maps. -/
def constantCoequivariant (M : ModuleCat.{u} R) : TranslationAction.Coequivariant (data R ρ) where
  obj := constant R M
  coact := constantCoact R ρ M
  coact_one := by
    apply ((constantAdj R).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, unit_comp_map_constantCoact,
      TranslationAction.sections_one_inv]
  coact_mul g h := by
    apply ((constantAdj R).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, unit_comp_map_constantCoact]
    simp only [Functor.map_comp]
    rw [unit_comp_map_constantCoact_assoc]
    have n1 := ((data R ρ).sections g).inv.naturality (constantCoact R ρ M h)
    simp only [Functor.comp_map] at n1
    rw [← Category.assoc (((data R ρ).sections g).inv.app _)]
    erw [← n1]
    rw [← Category.assoc, ← Category.assoc, unit_comp_map_constantCoact, Category.assoc,
      Category.assoc]
    rw [← Category.assoc (((data R ρ).sections h).inv.app _),
      TranslationAction.sections_comp_inv, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]

/-- The action of `G` on degree `n` étale cohomology with constant
coefficients `M`, computed with the chosen injective resolution. -/
def constantCohomologyRep (M : ModuleCat.{u} R) (n : ℕ) : Rep.{u} R G :=
  (Rep.ActionToRep R G).obj
    (TranslationAction.coCohomologyAction (sectionsTop R) (constantCoequivariant R ρ M)
      (injectiveResolution (constant R M)) n)

/-- The module underlying the action is the published étale cohomology with
constant coefficients. -/
def constantCohomologyIso (M : ModuleCat.{u} R) (n : ℕ) :
    (TranslationAction.coCohomologyAction (sectionsTop R) (constantCoequivariant R ρ M)
      (injectiveResolution (constant (Y := Y) R M)) n).V ≅
      (EtaleDerivedSections.constantCohomology Y R n).obj M :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((NatIso.mapHomologicalComplex (EtaleDerivedSections.sectionsIso Y R) _).app
        (injectiveResolution (constant R M)).cocomplex).symm ≪≫
    (EtaleDerivedSections.cohomologyIso Y R (constant R M) n).symm

end Langlands.Geometry.EtaleCohomologyAction
