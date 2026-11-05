import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange

/-! # Constructing the relative identity subgroup from an open relative identity set -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- A geometrically connected test scheme with a section mapping to the unit
has image in every fibre identity component. -/
theorem inRelativeIdentityComponent_of_geometricallyConnected
    {T : Over S} [GeometricallyConnected T.hom]
    (x : T ⟶ G.X) (a : 𝟙_ (Over S) ⟶ T) (ha : a ≫ x = η[G.X]) :
    InRelativeIdentityComponent G x := by
  intro s
  let F := Over.pullback (S.fromSpecResidueField s)
  have : ConnectedSpace (F.obj T).left :=
    inferInstanceAs (ConnectedSpace (T.hom.fiber s))
  apply IdentityComponent.range_subset_identitySet (residueFiber G s) (F.map x)
    (Functor.LaxMonoidal.ε F ≫ F.map a)
  rw [Category.assoc, ← Functor.map_comp, ha]
  rfl

variable (hopen : IsOpen (underlyingSet G))

/-- The open subset consisting of the identity components of the residue fibres. -/
def identityOpen : G.X.left.Opens := ⟨underlyingSet G, hopen⟩

/-- The open restriction of the ambient scheme, with its structure map to the base. -/
abbrev identityOver : Over S := Over.mk ((identityOpen G hopen).ι ≫ G.X.hom)

/-- The inclusion of the open restriction, as a morphism over the base. -/
abbrev inclusionOver : identityOver G hopen ⟶ G.X :=
  Over.homMk (identityOpen G hopen).ι

instance : IsOpenImmersion (inclusionOver G hopen).left :=
  inferInstanceAs (IsOpenImmersion (identityOpen G hopen).ι)

instance : Mono (inclusionOver G hopen) := Over.mono_of_mono_left _

/-- The open restriction has exactly the prescribed underlying relative identity set. -/
theorem range_inclusionOver :
    Set.range (inclusionOver G hopen).left = underlyingSet G :=
  Scheme.Opens.range_ι _

/-- The unit of the ambient group lands in the open restriction. -/
theorem one_range_subset :
    Set.range η[G.X].left ⊆ Set.range (inclusionOver G hopen).left := by
  have : GeometricallyConnected (𝟙_ (Over S)).hom := by
    change GeometricallyConnected (𝟙 S)
    refine ⟨?_⟩
    intro K _ y Z fst snd h
    have : IsIso snd := h.isIso_snd_of_isIso
    exact snd.homeomorph.connectedSpace_iff.mpr inferInstance
  rw [range_inclusionOver]
  apply (inRelativeIdentityComponent_iff_range_subset G _).mp
  apply inRelativeIdentityComponent_of_geometricallyConnected G _ (𝟙 _)
  exact Category.id_comp _

/-- The unit section with codomain restricted to the open subscheme. -/
def openOne : 𝟙_ (Over S) ⟶ identityOver G hopen :=
  liftOver (inclusionOver G hopen) η[G.X] (one_range_subset G hopen)

@[reassoc (attr := simp)]
theorem openOne_fac : openOne G hopen ≫ inclusionOver G hopen = η[G.X] :=
  liftOver_fac _ _ _

instance [Smooth G.X.hom] : Smooth (identityOver G hopen).hom :=
  inferInstanceAs (Smooth ((identityOpen G hopen).ι ≫ G.X.hom))

variable [Smooth G.X.hom] [GeometricallyConnected (identityOver G hopen).hom]

instance : GeometricallyConnected (identityOver G hopen ⊗ identityOver G hopen).hom := by
  change GeometricallyConnected
    (pullback.fst (identityOver G hopen).hom (identityOver G hopen).hom ≫
      (identityOver G hopen).hom)
  exact GeometricallyConnected.comp _ _

/-- Multiplication of two points of the open restriction lands in that restriction. -/
theorem mul_range_subset :
    Set.range (((inclusionOver G hopen ⊗ₘ inclusionOver G hopen) ≫ μ[G.X]).left) ⊆
      Set.range (inclusionOver G hopen).left := by
  rw [range_inclusionOver]
  apply (inRelativeIdentityComponent_iff_range_subset G _).mp
  apply inRelativeIdentityComponent_of_geometricallyConnected G _
    (lift (openOne G hopen) (openOne G hopen))
  rw [lift_map_assoc, openOne_fac]
  have h := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over S))) η[G.X]
  simp only [Category.id_comp] at h
  exact h

/-- The actual restricted multiplication. -/
def openMul : identityOver G hopen ⊗ identityOver G hopen ⟶ identityOver G hopen :=
  liftOver (inclusionOver G hopen)
    ((inclusionOver G hopen ⊗ₘ inclusionOver G hopen) ≫ μ[G.X])
    (mul_range_subset G hopen)

@[reassoc (attr := simp)]
theorem openMul_fac : openMul G hopen ≫ inclusionOver G hopen =
    (inclusionOver G hopen ⊗ₘ inclusionOver G hopen) ≫ μ[G.X] :=
  liftOver_fac _ _ _

omit [Smooth G.X.hom] in
/-- Inversion preserves the open restriction. -/
theorem inv_range_subset :
    Set.range ((inclusionOver G hopen ≫ ι[G.X]).left) ⊆
      Set.range (inclusionOver G hopen).left := by
  rw [range_inclusionOver]
  apply (inRelativeIdentityComponent_iff_range_subset G _).mp
  apply inRelativeIdentityComponent_of_geometricallyConnected G _ (openOne G hopen)
  rw [openOne_fac_assoc, GrpObj.one_inv]

/-- The actual restricted inverse. -/
def openInv : identityOver G hopen ⟶ identityOver G hopen :=
  liftOver (inclusionOver G hopen) (inclusionOver G hopen ≫ ι[G.X])
    (inv_range_subset G hopen)

omit [Smooth G.X.hom] in
@[reassoc (attr := simp)]
theorem openInv_fac : openInv G hopen ≫ inclusionOver G hopen =
    inclusionOver G hopen ≫ ι[G.X] :=
  liftOver_fac _ _ _

instance openGrpObj : GrpObj (identityOver G hopen) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusionOver G hopen) (openOne G hopen) (openMul G hopen) (openInv G hopen)
    (openOne_fac G hopen) (openMul_fac G hopen) (openInv_fac G hopen)

instance : IsMonHom (inclusionOver G hopen) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (inclusionOver G hopen) (openOne G hopen) (openMul G hopen) (openInv G hopen)
    (openOne_fac G hopen) (openMul_fac G hopen) (openInv_fac G hopen)

/-- The actual open subgroup scheme on the relative identity set. -/
def groupOfIsOpen : GroupScheme S := { X := identityOver G hopen }

/-- The actual group-scheme inclusion of the constructed subgroup. -/
def inclusionOfIsOpen : groupOfIsOpen G hopen ⟶ G :=
  Grp.homMk (inclusionOver G hopen)

instance : IsOpenImmersion (inclusionOfIsOpen G hopen).hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (inclusionOver G hopen).left)

instance : Smooth (groupOfIsOpen G hopen).X.hom :=
  inferInstanceAs (Smooth (identityOver G hopen).hom)

instance : GeometricallyConnected (groupOfIsOpen G hopen).X.hom :=
  inferInstanceAs (GeometricallyConnected (identityOver G hopen).hom)

/-- The constructed inclusion represents the published criterion on every test scheme. -/
theorem isRelativeIdentityComponent_inclusionOfIsOpen :
    IsRelativeIdentityComponent G (inclusionOfIsOpen G hopen) :=
  IsRelativeIdentityComponent.of_range_eq_underlyingSet (range_inclusionOver G hopen)

include hopen in
/-- Openness and geometric connectedness of the open restriction supply the
existence conclusion for this smooth group scheme. -/
theorem exists_of_isOpen :
    ∃ (H : GroupScheme S) (i : H ⟶ G),
      IsRelativeIdentityComponent G i ∧
        Smooth H.X.hom ∧ GeometricallyConnected H.X.hom :=
  ⟨groupOfIsOpen G hopen, inclusionOfIsOpen G hopen,
    isRelativeIdentityComponent_inclusionOfIsOpen G hopen, inferInstance, inferInstance⟩

end Langlands.GroupScheme.RelativeIdentityComponent
