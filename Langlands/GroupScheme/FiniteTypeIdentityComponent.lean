import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry

/-! # Identity components of affine finite-type group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteTypeIdentityComponent

open Langlands.GroupScheme.IdentityComponent
  (basePoint identityPoint identitySet unit_left_apply range_subset_identitySet
    hom_ext_of_isOpenImmersion)
open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]

/-- The existing geometric component theorem applies to finite-type group schemes
without a smoothness hypothesis. -/
theorem exists_isOpenImmersion_geometricallyConnected :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ H.X.left), IsOpenImmersion i ∧ IsClosedImmersion i ∧
      GeometricallyIrreducible (i ≫ H.X.hom) ∧ GeometricallyConnected (i ≫ H.X.hom) ∧
      Set.range i = identitySet H := by
  let : GrpObj (Over.mk H.X.hom) := H.grp
  obtain ⟨G₀, i, -, hi, hc, -, hgi, hg, hr, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k (GoodReductionJacobian.relativeGroupLawOfGrpObj k H.X.hom)
  refine ⟨G₀, i, hi, hc, hgi, hg, hr.trans ?_⟩
  rw [GoodReductionJacobian.relativeGroupLawOfGrpObj_one]
  change connectedComponent
    ((toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ η[H.X]).left (basePoint k)) = _
  rw [Over.comp_left, Scheme.Hom.comp_apply, unit_left_apply]

/-- The connected component of the identity point is open and closed. -/
theorem isClopen_identitySet : IsClopen (identitySet H) := by
  obtain ⟨G₀, i, _, _, -, -, hr⟩ := exists_isOpenImmersion_geometricallyConnected H
  rw [← hr]
  exact ⟨i.isClosedEmbedding.isClosed_range, IsOpenImmersion.isOpen_range i⟩

/-- The open subscheme of `H` on the connected component of the identity point. -/
def identityOpen : H.X.left.Opens :=
  ⟨identitySet H, (isClopen_identitySet H).isOpen⟩

instance : IsClosedImmersion (identityOpen H).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (isClopen_identitySet H).isClosed)

/-- The identity component as a scheme over `k`. -/
abbrev identityComponentOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk ((identityOpen H).ι ≫ H.X.hom)

/-- The inclusion of the identity component, over `k`. -/
abbrev inclusionOver : identityComponentOver H ⟶ H.X :=
  Over.homMk (identityOpen H).ι

instance : IsOpenImmersion (inclusionOver H).left :=
  inferInstanceAs (IsOpenImmersion (identityOpen H).ι)

instance : IsClosedImmersion (inclusionOver H).left :=
  inferInstanceAs (IsClosedImmersion (identityOpen H).ι)

instance : Mono (inclusionOver H) := Over.mono_of_mono_left _

theorem range_inclusionOver : Set.range (inclusionOver H).left = identitySet H :=
  Scheme.Opens.range_ι _

instance connectedSpace_identityComponentOver : ConnectedSpace (identityComponentOver H).left :=
  Subtype.connectedSpace (isConnected_connectedComponent (x := identityPoint H))

/-- A property of morphisms respecting isomorphisms which holds for `i ≫ H.X.hom`, for some open
immersion `i` onto the connected component of the identity point, holds for the structure
morphism of the identity component. -/
theorem of_range_eq (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {G₀ : Scheme.{u}}
    (i : G₀ ⟶ H.X.left) [IsOpenImmersion i] (hr : Set.range i = identitySet H)
    (hP : P (i ≫ H.X.hom)) : P (identityComponentOver H).hom := by
  have e : Set.range i = Set.range (identityOpen H).ι := by
    rw [hr, Scheme.Opens.range_ι]
    rfl
  have hfac : i ≫ H.X.hom = (IsOpenImmersion.isoOfRangeEq i (identityOpen H).ι e).hom ≫
      ((identityOpen H).ι ≫ H.X.hom) := by
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  rw [hfac] at hP
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mp hP

instance geometricallyConnected_identityComponentOver :
    GeometricallyConnected (identityComponentOver H).hom := by
  obtain ⟨G₀, i, _, _, -, hg, hr⟩ := exists_isOpenImmersion_geometricallyConnected H
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact of_range_eq H @GeometricallyConnected.{u} i hr hg

instance geometricallyIrreducible_identityComponentOver :
    GeometricallyIrreducible (identityComponentOver H).hom := by
  obtain ⟨G₀, i, _, _, hgi, -, hr⟩ := exists_isOpenImmersion_geometricallyConnected H
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact of_range_eq H @GeometricallyIrreducible.{u} i hr hgi

instance irreducibleSpace_identityComponentOver :
    IrreducibleSpace (identityComponentOver H).left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := (identityComponentOver H).hom)

instance isAffineHom_identityComponentOver : IsAffineHom (identityComponentOver H).hom :=
  inferInstanceAs (IsAffineHom ((identityOpen H).ι ≫ H.X.hom))

instance locallyOfFiniteType_identityComponentOver :
    LocallyOfFiniteType (identityComponentOver H).hom :=
  inferInstanceAs (LocallyOfFiniteType ((identityOpen H).ι ≫ H.X.hom))

instance : UniversallyOpen (identityComponentOver H).hom :=
  UniversallyOpen.of_flat _

instance : ConnectedSpace (identityComponentOver H ⊗ identityComponentOver H).left :=
  inferInstanceAs
    (ConnectedSpace ↥(Limits.pullback (identityComponentOver H).hom
      (identityComponentOver H).hom : Scheme.{u}))

/-! ### The restricted group law -/

theorem one_range_subset :
    Set.range η[H.X].left ⊆ Set.range (inclusionOver H).left := by
  have : ConnectedSpace (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of k)))
  rw [range_inclusionOver]
  exact range_subset_identitySet H η[H.X] (𝟙 _) (Category.id_comp _)

/-- The unit of the identity component. -/
def one : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ identityComponentOver H :=
  liftOver (inclusionOver H) η[H.X] (one_range_subset H)

@[reassoc (attr := simp)]
theorem one_fac : one H ≫ inclusionOver H = η[H.X] :=
  liftOver_fac _ _ _

theorem mul_range_subset :
    Set.range (((inclusionOver H ⊗ₘ inclusionOver H) ≫ μ[H.X]).left) ⊆
      Set.range (inclusionOver H).left := by
  rw [range_inclusionOver]
  refine range_subset_identitySet H _ (lift (one H) (one H)) ?_
  rw [lift_map_assoc, one_fac]
  simpa using MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Spec (CommRingCat.of k))))) η[H.X]

/-- The multiplication of the identity component: the restriction of the multiplication
of `H`. -/
def mul : identityComponentOver H ⊗ identityComponentOver H ⟶ identityComponentOver H :=
  liftOver (inclusionOver H) ((inclusionOver H ⊗ₘ inclusionOver H) ≫ μ[H.X])
    (mul_range_subset H)

@[reassoc (attr := simp)]
theorem mul_fac : mul H ≫ inclusionOver H =
    (inclusionOver H ⊗ₘ inclusionOver H) ≫ μ[H.X] :=
  liftOver_fac _ _ _

theorem inv_range_subset :
    Set.range ((inclusionOver H ≫ ι[H.X]).left) ⊆ Set.range (inclusionOver H).left := by
  rw [range_inclusionOver]
  refine range_subset_identitySet H _ (one H) ?_
  rw [one_fac_assoc, GrpObj.one_inv]

/-- The inverse of the identity component: the restriction of the inverse of `H`. -/
def inv : identityComponentOver H ⟶ identityComponentOver H :=
  liftOver (inclusionOver H) (inclusionOver H ≫ ι[H.X]) (inv_range_subset H)

@[reassoc (attr := simp)]
theorem inv_fac : inv H ≫ inclusionOver H = inclusionOver H ≫ ι[H.X] :=
  liftOver_fac _ _ _

instance grpObj_identityComponentOver : GrpObj (identityComponentOver H) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusionOver H) (one H) (mul H) (inv H) (one_fac H) (mul_fac H) (inv_fac H)

instance : IsMonHom (inclusionOver H) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (inclusionOver H) (one H) (mul H) (inv H) (one_fac H) (mul_fac H) (inv_fac H)

/-! ### The finite-type identity component and its inclusion -/

/-- The identity component `H⁰` of an affine group scheme of finite type over a field. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  { X := identityComponentOver H }

/-- The inclusion `H⁰ ⟶ H`. -/
def inclusion : groupScheme H ⟶ H :=
  Grp.homMk (inclusionOver H)

@[simp]
theorem identityComponentι_hom_hom : (inclusion H).hom.hom = inclusionOver H :=
  rfl

/-- The unit of `H⁰` is the restricted unit `one H`. -/
theorem one_identityComponent : η[(groupScheme H).X] = one H :=
  rfl

/-- The multiplication of `H⁰` is the restricted multiplication `mul H`. -/
theorem mul_identityComponent : μ[(groupScheme H).X] = mul H :=
  rfl

/-- The inverse of `H⁰` is the restricted inverse `inv H`. -/
theorem inv_identityComponent : ι[(groupScheme H).X] = inv H :=
  rfl

instance isOpenImmersion_identityComponentι :
    IsOpenImmersion (inclusion H).hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (inclusionOver H).left)

instance isClosedImmersion_identityComponentι :
    IsClosedImmersion (inclusion H).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver H).left)

theorem isClosedSubgroup_identityComponentι : IsClosedSubgroup (inclusion H) :=
  inferInstanceAs (IsClosedImmersion (inclusionOver H).left)

/-- The topological range of the inclusion is the connected component of the identity point. -/
theorem range_identityComponentι :
    Set.range (inclusion H).hom.hom.left = connectedComponent (identityPoint H) :=
  range_inclusionOver H

instance isAffineHom_identityComponent : IsAffineHom (groupScheme H).X.hom :=
  isAffineHom_identityComponentOver H

instance connectedSpace_identityComponent : ConnectedSpace (groupScheme H).X.left :=
  connectedSpace_identityComponentOver H

instance geometricallyConnected_identityComponent :
    GeometricallyConnected (groupScheme H).X.hom :=
  geometricallyConnected_identityComponentOver H

instance geometricallyIrreducible_identityComponent :
    GeometricallyIrreducible (groupScheme H).X.hom :=
  geometricallyIrreducible_identityComponentOver H

instance irreducibleSpace_identityComponent : IrreducibleSpace (groupScheme H).X.left :=
  irreducibleSpace_identityComponentOver H

instance mono_identityComponentι : Mono (inclusion H) where
  right_cancellation _ _ h := hom_ext_of_isOpenImmersion _ h

instance locallyOfFiniteType_groupScheme : LocallyOfFiniteType (groupScheme H).X.hom :=
  inferInstanceAs (LocallyOfFiniteType ((identityOpen H).ι ≫ H.X.hom))

/-- Restricting a flat homomorphism to the full identity component preserves
faithful flatness when the target is connected and affine of finite type. -/
theorem inclusion_comp_flat_surjective
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (q : H ⟶ G) [Flat q.hom.hom.left] :
    Flat (inclusion H ≫ q).hom.hom.left ∧
      Surjective (inclusion H ≫ q).hom.hom.left := by
  let f := inclusion H ≫ q
  have : Flat f.hom.hom.left :=
    inferInstanceAs (Flat ((inclusion H).hom.hom.left ≫ q.hom.hom.left))
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ G.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom.hom.left G.X.hom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : LocallyOfFinitePresentation f.hom.hom.left := inferInstance
  obtain ⟨I, proj, inc, _, _, hinc, hfac, hquot⟩ := affineHomImage k _ _ f
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Surjective proj.hom.hom.left := hquot.2.1
  have hrange : Set.range f.hom.hom.left = Set.range inc.hom.hom.left := by
    calc
      _ = Set.range (proj ≫ inc).hom.hom.left :=
        congrArg (fun g => Set.range g.hom.hom.left) hfac.symm
      _ = _ := by
        rw [Grp.comp_hom_hom, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp,
          Set.range_comp, Set.range_eq_univ.mpr proj.hom.hom.left.surjective,
          Set.image_univ]
  have hclosed : IsClosed (Set.range f.hom.hom.left) := by
    rw [hrange]
    exact inc.hom.hom.left.isClosedEmbedding.isClosed_range
  have hopen : IsOpen (Set.range f.hom.hom.left) := f.hom.hom.left.isOpenMap.isOpen_range
  have huniv : Set.range f.hom.hom.left = Set.univ :=
    (show IsClopen (Set.range f.hom.hom.left) from ⟨hclosed, hopen⟩).eq_univ
      ⟨f.hom.hom.left (identityPoint (groupScheme H)), Set.mem_range_self _⟩
  exact ⟨inferInstance, ⟨Set.range_eq_univ.mp huniv⟩⟩

end Langlands.GroupScheme.FiniteTypeIdentityComponent

/-! # Identity components without a smoothness hypothesis -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent.FiniteType

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
  [LocallyOfFiniteType H.X.hom]

local instance : IsLocallyNoetherian H.X.left :=
  LocallyOfFiniteType.isLocallyNoetherian H.X.hom

/-- Local finite type over a field makes the actual identity component open and closed. -/
theorem isClopen_identitySet : IsClopen (identitySet H) :=
  ⟨isClosed_connectedComponent,
    Langlands.AlgebraicGeometry.locallyNoetherianConnectedComponentOpen_proof
      H.X.left (identityPoint H)⟩

/-- The open subscheme of `H` on the connected component of the identity point. -/
def identityOpen : H.X.left.Opens :=
  ⟨identitySet H, (isClopen_identitySet H).isOpen⟩

instance : IsClosedImmersion (identityOpen H).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (isClopen_identitySet H).isClosed)

/-- The identity component as a scheme over `k`. -/
abbrev identityComponentOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk ((identityOpen H).ι ≫ H.X.hom)

/-- The inclusion of the identity component, over `k`. -/
abbrev inclusionOver : identityComponentOver H ⟶ H.X :=
  Over.homMk (identityOpen H).ι

instance : IsOpenImmersion (inclusionOver H).left :=
  inferInstanceAs (IsOpenImmersion (identityOpen H).ι)

instance : IsClosedImmersion (inclusionOver H).left :=
  inferInstanceAs (IsClosedImmersion (identityOpen H).ι)

instance : Mono (inclusionOver H) := Over.mono_of_mono_left _

theorem range_inclusionOver : Set.range (inclusionOver H).left = identitySet H :=
  Scheme.Opens.range_ι _

instance connectedSpace_identityComponentOver : ConnectedSpace (identityComponentOver H).left :=
  Subtype.connectedSpace (isConnected_connectedComponent (x := identityPoint H))

instance geometricallyConnected_identityComponentOver :
    GeometricallyConnected (identityComponentOver H).hom := by
  exact Langlands.AlgebraicGeometry.geometricallyConnected_connectedComponentOpen
    H.X.hom η[H.X].left η[H.X].w

instance locallyOfFiniteType_identityComponentOver :
    LocallyOfFiniteType (identityComponentOver H).hom :=
  inferInstanceAs (LocallyOfFiniteType ((identityOpen H).ι ≫ H.X.hom))

instance isAffineHom_identityComponentOver [IsAffineHom H.X.hom] :
    IsAffineHom (identityComponentOver H).hom :=
  inferInstanceAs (IsAffineHom ((identityOpen H).ι ≫ H.X.hom))

instance : UniversallyOpen (identityComponentOver H).hom :=
  UniversallyOpen.of_flat _

instance : ConnectedSpace (identityComponentOver H ⊗ identityComponentOver H).left :=
  inferInstanceAs
    (ConnectedSpace ↥(Limits.pullback (identityComponentOver H).hom
      (identityComponentOver H).hom : Scheme.{u}))

/-! ### The restricted group law -/

theorem one_range_subset :
    Set.range η[H.X].left ⊆ Set.range (inclusionOver H).left := by
  have : ConnectedSpace (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of k)))
  rw [range_inclusionOver]
  exact range_subset_identitySet H η[H.X] (𝟙 _) (Category.id_comp _)

/-- The unit of the identity component. -/
def one : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ identityComponentOver H :=
  liftOver (inclusionOver H) η[H.X] (one_range_subset H)

@[reassoc (attr := simp)]
theorem one_fac : one H ≫ inclusionOver H = η[H.X] :=
  liftOver_fac _ _ _

theorem mul_range_subset :
    Set.range (((inclusionOver H ⊗ₘ inclusionOver H) ≫ μ[H.X]).left) ⊆
      Set.range (inclusionOver H).left := by
  rw [range_inclusionOver]
  refine range_subset_identitySet H _ (lift (one H) (one H)) ?_
  rw [lift_map_assoc, one_fac]
  simpa using MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Spec (CommRingCat.of k))))) η[H.X]

/-- The multiplication of the identity component: the restriction of the multiplication
of `H`. -/
def mul : identityComponentOver H ⊗ identityComponentOver H ⟶ identityComponentOver H :=
  liftOver (inclusionOver H) ((inclusionOver H ⊗ₘ inclusionOver H) ≫ μ[H.X])
    (mul_range_subset H)

@[reassoc (attr := simp)]
theorem mul_fac : mul H ≫ inclusionOver H =
    (inclusionOver H ⊗ₘ inclusionOver H) ≫ μ[H.X] :=
  liftOver_fac _ _ _

theorem inv_range_subset :
    Set.range ((inclusionOver H ≫ ι[H.X]).left) ⊆ Set.range (inclusionOver H).left := by
  rw [range_inclusionOver]
  refine range_subset_identitySet H _ (one H) ?_
  rw [one_fac_assoc, GrpObj.one_inv]

/-- The inverse of the identity component: the restriction of the inverse of `H`. -/
def inv : identityComponentOver H ⟶ identityComponentOver H :=
  liftOver (inclusionOver H) (inclusionOver H ≫ ι[H.X]) (inv_range_subset H)

@[reassoc (attr := simp)]
theorem inv_fac : inv H ≫ inclusionOver H = inclusionOver H ≫ ι[H.X] :=
  liftOver_fac _ _ _

instance grpObj_identityComponentOver : GrpObj (identityComponentOver H) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusionOver H) (one H) (mul H) (inv H) (one_fac H) (mul_fac H) (inv_fac H)

instance : IsMonHom (inclusionOver H) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (inclusionOver H) (one H) (mul H) (inv H) (one_fac H) (mul_fac H) (inv_fac H)

/-! ### The identity component and its inclusion -/

/-- The identity component of a group scheme locally of finite type over a field. -/
abbrev _root_.Langlands.GroupScheme.finiteTypeIdentityComponent : GroupScheme (Spec (CommRingCat.of k)) :=
  { X := identityComponentOver H }

/-- The inclusion `H⁰ ⟶ H`. -/
def _root_.Langlands.GroupScheme.finiteTypeIdentityComponentι : finiteTypeIdentityComponent H ⟶ H :=
  Grp.homMk (inclusionOver H)

@[simp]
theorem finiteTypeIdentityComponentι_hom_hom : (finiteTypeIdentityComponentι H).hom.hom = inclusionOver H :=
  rfl

/-- The unit of `H⁰` is the restricted unit `one H`. -/
theorem one_identityComponent : η[(finiteTypeIdentityComponent H).X] = one H :=
  rfl

/-- The multiplication of `H⁰` is the restricted multiplication `mul H`. -/
theorem mul_identityComponent : μ[(finiteTypeIdentityComponent H).X] = mul H :=
  rfl

/-- The inverse of `H⁰` is the restricted inverse `inv H`. -/
theorem inv_identityComponent : ι[(finiteTypeIdentityComponent H).X] = inv H :=
  rfl

instance isOpenImmersion_finiteTypeIdentityComponentι :
    IsOpenImmersion (finiteTypeIdentityComponentι H).hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (inclusionOver H).left)

instance isClosedImmersion_finiteTypeIdentityComponentι :
    IsClosedImmersion (finiteTypeIdentityComponentι H).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver H).left)

theorem isClosedSubgroup_finiteTypeIdentityComponentι : IsClosedSubgroup (finiteTypeIdentityComponentι H) :=
  inferInstanceAs (IsClosedImmersion (inclusionOver H).left)

/-- The topological range of the inclusion is the connected component of the identity point. -/
theorem range_finiteTypeIdentityComponentι :
    Set.range (finiteTypeIdentityComponentι H).hom.hom.left = connectedComponent (identityPoint H) :=
  range_inclusionOver H

instance locallyOfFiniteType_identityComponent :
    LocallyOfFiniteType (finiteTypeIdentityComponent H).X.hom :=
  locallyOfFiniteType_identityComponentOver H

instance isAffineHom_identityComponent [IsAffineHom H.X.hom] :
    IsAffineHom (finiteTypeIdentityComponent H).X.hom :=
  isAffineHom_identityComponentOver H

instance connectedSpace_identityComponent : ConnectedSpace (finiteTypeIdentityComponent H).X.left :=
  connectedSpace_identityComponentOver H

instance geometricallyConnected_identityComponent :
    GeometricallyConnected (finiteTypeIdentityComponent H).X.hom :=
  geometricallyConnected_identityComponentOver H

instance mono_finiteTypeIdentityComponentι : Mono (finiteTypeIdentityComponentι H) where
  right_cancellation _ _ h := hom_ext_of_isOpenImmersion _ h

/-! ### Normality -/

/-- The conjugation map `(g, x) ↦ g x g⁻¹` from `H ×_k H⁰` to `H`. -/
def conjOver : H.X ⊗ identityComponentOver H ⟶ H.X :=
  (H.X ◁ inclusionOver H) ≫ GrpObj.conj H.X

theorem lift_conjOver {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ H.X)
    (y : T ⟶ identityComponentOver H) :
    lift g y ≫ conjOver H = g * (y ≫ inclusionOver H) * g⁻¹ := by
  rw [conjOver, lift_whiskerLeft_assoc, GrpObj.lift_conj_eq_mul_mul_inv]

/-- Conjugation by an arbitrary point of `H` maps `H⁰` into the connected component of the
identity: each fibre of the projection `H ×_k H⁰ ⟶ H` is connected and contains a point sent
to the identity point. -/
theorem range_conjOver_subset : Set.range (conjOver H).left ⊆ identitySet H := by
  rintro _ ⟨z, rfl⟩
  let p : (H.X ⊗ identityComponentOver H).left ⟶ H.X.left :=
    pullback.fst H.X.hom (identityComponentOver H).hom
  let s : H.X ⟶ H.X ⊗ identityComponentOver H := lift (𝟙 _) (toUnit _ ≫ one H)
  have hF : _root_.IsConnected (p ⁻¹' {p z}) :=
    Scheme.Hom.isConnected_preimage_singleton p (p z)
  have hs : s ≫ conjOver H = toUnit _ ≫ η[H.X] := by
    rw [lift_conjOver, Category.assoc, one_fac, ← CategoryTheory.Hom.one_def]
    simp
  have hsz : s.left (p z) ∈ p ⁻¹' {p z} := by
    change (s ≫ fst _ _).left (p z) = p z
    rw [lift_fst]
    rfl
  have hconn : _root_.IsConnected ((conjOver H).left '' (p ⁻¹' {p z})) :=
    hF.image _ (conjOver H).left.continuous.continuousOn
  refine hconn.isPreconnected.subset_connectedComponent ⟨_, hsz, ?_⟩
    ⟨z, rfl, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs, Over.comp_left, Scheme.Hom.comp_apply,
    unit_left_apply]

/-- The range subgroup functor of `H⁰ ⟶ H` is normal, with the all-test meaning: conjugation by
every point of `H` over every test scheme preserves the points of `H⁰`. -/
theorem isNormal_range_finiteTypeIdentityComponentι :
    (SubgroupFunctor.range (finiteTypeIdentityComponentι H)).IsNormal := by
  intro T g x _ hx
  rw [SubgroupFunctor.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨liftOver (inclusionOver H) (lift g y ≫ conjOver H) ?_, ?_⟩
  · rw [range_inclusionOver]
    rintro _ ⟨t, rfl⟩
    exact range_conjOver_subset H ⟨(lift g y).left t, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rw [finiteTypeIdentityComponentι_hom_hom, liftOver_fac, lift_conjOver]

/-! ### Factorization of homomorphisms from connected group schemes -/

section Factor

variable {K : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace K.X.left] (f : K ⟶ H)

theorem range_subset_range_finiteTypeIdentityComponentι :
    Set.range f.hom.hom.left ⊆ Set.range (finiteTypeIdentityComponentι H).hom.hom.left := by
  rw [range_finiteTypeIdentityComponentι]
  exact range_subset_identitySet H f.hom.hom η[K.X] (IsMonHom.one_hom _)

/-- The factorization through `H⁰` of a homomorphism from a connected group scheme. -/
def factor : K ⟶ finiteTypeIdentityComponent H :=
  liftHom (finiteTypeIdentityComponentι H) f (range_subset_range_finiteTypeIdentityComponentι H f)

@[reassoc (attr := simp)]
theorem factor_finiteTypeIdentityComponentι : factor H f ≫ finiteTypeIdentityComponentι H = f :=
  liftHom_fac _ _ _

theorem eq_factor (g : K ⟶ finiteTypeIdentityComponent H) (hg : g ≫ finiteTypeIdentityComponentι H = f) :
    g = factor H f :=
  hom_ext_of_isOpenImmersion (finiteTypeIdentityComponentι H) (hg.trans (factor_finiteTypeIdentityComponentι H f).symm)

theorem existsUnique_factor : ∃! g : K ⟶ finiteTypeIdentityComponent H, g ≫ finiteTypeIdentityComponentι H = f :=
  ⟨factor H f, factor_finiteTypeIdentityComponentι H f, eq_factor H f⟩

/-- Homomorphisms from a connected group scheme into `H⁰` are the homomorphisms into `H`. -/
def homEquiv : (K ⟶ finiteTypeIdentityComponent H) ≃ (K ⟶ H) where
  toFun g := g ≫ finiteTypeIdentityComponentι H
  invFun f := factor H f
  left_inv g := (eq_factor H _ g rfl).symm
  right_inv f := factor_finiteTypeIdentityComponentι H f

end Factor

/-! ### Characterization as the connected open and closed subgroup -/

section Characterization

variable {P : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace P.X.left] (j : P ⟶ H)
  [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]

omit [LocallyOfFiniteType H.X.hom] in
/-- The range of a homomorphism from a connected group scheme which is an open and closed
immersion is the connected component of the identity point. -/
theorem range_eq_identitySet : Set.range j.hom.hom.left = identitySet H := by
  apply subset_antisymm
  · exact range_subset_identitySet H j.hom.hom η[P.X] (IsMonHom.one_hom _)
  · apply IsClopen.connectedComponent_subset
      ⟨j.hom.hom.left.isClosedEmbedding.isClosed_range, IsOpenImmersion.isOpen_range _⟩
    refine ⟨η[P.X].left (basePoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
    rfl

/-- A connected group scheme with a homomorphism to `H` that is an open and closed immersion is
canonically isomorphic to `H⁰`, compatibly with the inclusions. -/
def isoOfIsOpenImmersion : P ≅ finiteTypeIdentityComponent H where
  hom := factor H j
  inv := liftHom j (finiteTypeIdentityComponentι H) (by
    rw [range_finiteTypeIdentityComponentι, range_eq_identitySet])
  hom_inv_id := hom_ext_of_isOpenImmersion j (by simp)
  inv_hom_id := hom_ext_of_isOpenImmersion (finiteTypeIdentityComponentι H) (by simp)

@[reassoc (attr := simp)]
theorem isoOfIsOpenImmersion_hom_finiteTypeIdentityComponentι :
    (isoOfIsOpenImmersion H j).hom ≫ finiteTypeIdentityComponentι H = j :=
  factor_finiteTypeIdentityComponentι H j

@[reassoc (attr := simp)]
theorem isoOfIsOpenImmersion_inv_comp :
    (isoOfIsOpenImmersion H j).inv ≫ j = finiteTypeIdentityComponentι H :=
  liftHom_fac _ _ _

end Characterization

/-! ### Compatibility with extension of the ground field -/

section BaseChange

variable {L : Type u} [Field L] (φ : k →+* L)

/-- The morphism `Spec L ⟶ Spec k` induced by a field embedding `k →+* L`. -/
abbrev specMap : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom φ)

instance locallyOfFiniteType_baseChange :
    LocallyOfFiniteType ((GroupScheme.baseChange (specMap φ)).obj H).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd H.X.hom (specMap φ)))

instance : IsOpenImmersion
    ((GroupScheme.baseChange (specMap φ)).map (finiteTypeIdentityComponentι H)).hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (specMap φ) (inclusionOver H)
    (inferInstanceAs (IsOpenImmersion (inclusionOver H).left))

instance : IsClosedImmersion
    ((GroupScheme.baseChange (specMap φ)).map (finiteTypeIdentityComponentι H)).hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (specMap φ) (inclusionOver H)
    (inferInstanceAs (IsClosedImmersion (inclusionOver H).left))

instance : ConnectedSpace
    ((GroupScheme.baseChange (specMap φ)).obj (finiteTypeIdentityComponent H)).X.left :=
  @GeometricallyConnected.connectedSpace_of_subsingleton _ _
    (pullback.snd (identityComponentOver H).hom (specMap φ))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @GeometricallyConnected.{u})
      (IsPullback.of_hasPullback _ _) (geometricallyConnected_identityComponentOver H)) _ _

/-- Formation of the identity component commutes with extension of the ground field: the base
change of `H⁰` along `Spec L ⟶ Spec k` is the identity component of the base change of `H`. -/
def baseChangeIso :
    (GroupScheme.baseChange (specMap φ)).obj (finiteTypeIdentityComponent H) ≅
      finiteTypeIdentityComponent ((GroupScheme.baseChange (specMap φ)).obj H) :=
  isoOfIsOpenImmersion _ ((GroupScheme.baseChange (specMap φ)).map (finiteTypeIdentityComponentι H))

/-- The comparison isomorphism identifies the two inclusions into the base change of `H`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_finiteTypeIdentityComponentι :
    (baseChangeIso H φ).hom ≫ finiteTypeIdentityComponentι ((GroupScheme.baseChange (specMap φ)).obj H) =
      (GroupScheme.baseChange (specMap φ)).map (finiteTypeIdentityComponentι H) :=
  isoOfIsOpenImmersion_hom_finiteTypeIdentityComponentι _ _

@[reassoc (attr := simp)]
theorem baseChangeIso_inv_comp :
    (baseChangeIso H φ).inv ≫ (GroupScheme.baseChange (specMap φ)).map (finiteTypeIdentityComponentι H) =
      finiteTypeIdentityComponentι ((GroupScheme.baseChange (specMap φ)).obj H) :=
  isoOfIsOpenImmersion_inv_comp _ _

end BaseChange

end Langlands.GroupScheme.IdentityComponent.FiniteType
