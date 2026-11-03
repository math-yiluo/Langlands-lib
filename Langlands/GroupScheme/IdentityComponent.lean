import Langlands.AbelianScheme.GroupScheme
import Langlands.CategoryTheory.GroupObjectDescent
import Langlands.GroupScheme.FiniteEtaleImage
import Langlands.GroupScheme.SubgroupFunctor
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent

/-! # Identity components of smooth affine group schemes over a field

For a smooth affine group scheme `H` over a field `k`, the identity component `H⁰` is the open
subscheme of `H` on the connected component of the identity point, with the restricted group law.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

/-! ### Lifting homomorphisms through open immersions -/

section Lift

variable {S : Scheme.{u}} {P Q R : GroupScheme S} (j : P ⟶ Q) [IsOpenImmersion j.hom.hom.left]

instance mono_hom_hom : Mono j.hom.hom := Over.mono_of_mono_left _

/-- Homomorphisms into `P` are determined by their composites with `j`. -/
theorem hom_ext_of_isOpenImmersion {a b : R ⟶ P} (h : a ≫ j = b ≫ j) : a = b :=
  Grp.hom_ext _ _ ((cancel_mono j.hom.hom).mp (congrArg (fun x => x.hom.hom) h))

variable (g : R ⟶ Q) (h : Set.range g.hom.hom.left ⊆ Set.range j.hom.hom.left)

/-- The factorization over the base of `g` through the open immersion `j`. -/
def liftHomOver : R.X ⟶ P.X := liftOver j.hom.hom g.hom.hom h

@[reassoc (attr := simp)]
theorem liftHomOver_fac : liftHomOver j g h ≫ j.hom.hom = g.hom.hom :=
  liftOver_fac _ _ _

instance : IsMonHom (liftHomOver j g h) where
  one_hom := by
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, liftHomOver_fac, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, liftHomOver_fac, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, liftHomOver_fac]

/-- The factorization of the homomorphism `g` through the open immersion `j`, as a
homomorphism of group schemes. -/
def liftHom : R ⟶ P := Grp.homMk (liftHomOver j g h)

@[reassoc (attr := simp)]
theorem liftHom_fac : liftHom j g h ≫ j = g :=
  Grp.hom_ext _ _ (liftHomOver_fac j g h)

end Lift

/-! ### The identity point and its connected component -/

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))

variable (k) in
/-- The unique point of `Spec k`, as a point of the underlying scheme of the monoidal unit of
schemes over `k`. -/
def basePoint : (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
  IsLocalRing.closedPoint k

/-- The identity point of `H`: the image of the unique point of `Spec k` under the unit
section. -/
def identityPoint : H.X.left :=
  η[H.X].left (basePoint k)

/-- The unit section sends every point of `Spec k` to the identity point. -/
theorem unit_left_apply (x : (𝟙_ (Over (Spec (CommRingCat.of k)))).left) :
    η[H.X].left x = identityPoint H :=
  congrArg η[H.X].left (@Subsingleton.elim (Spec (CommRingCat.of k)) _ x _)

/-- The underlying set of the identity component: the connected component of the identity
point. -/
abbrev identitySet : Set H.X.left :=
  connectedComponent (identityPoint H)

/-- A map from a connected scheme over `k` sending some `k`-point to the identity point lands
in the connected component of the identity point. -/
theorem range_subset_identitySet {P : Over (Spec (CommRingCat.of k))} [ConnectedSpace P.left]
    (g : P ⟶ H.X) (a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P) (ha : a ≫ g = η[H.X]) :
    Set.range g.left ⊆ identitySet H := by
  refine (isConnected_range g.left.continuous).isPreconnected.subset_connectedComponent ?_
  refine ⟨a.left (basePoint k), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ha]
  rfl

section Smooth

variable [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The geometric input: there is an open and closed immersion onto the connected component of
the identity point whose composite to `Spec k` is geometrically irreducible and geometrically
connected. This is the ported Anthropic FLT theorem applied to the group law of `H`. -/
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

instance smooth_identityComponentOver : Smooth (identityComponentOver H).hom :=
  inferInstanceAs (Smooth ((identityOpen H).ι ≫ H.X.hom))

instance isAffineHom_identityComponentOver : IsAffineHom (identityComponentOver H).hom :=
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

/-- The identity component `H⁰` of a smooth affine group scheme `H` over a field. -/
abbrev _root_.Langlands.GroupScheme.identityComponent : GroupScheme (Spec (CommRingCat.of k)) :=
  { X := identityComponentOver H }

/-- The inclusion `H⁰ ⟶ H`. -/
def _root_.Langlands.GroupScheme.identityComponentι : identityComponent H ⟶ H :=
  Grp.homMk (inclusionOver H)

@[simp]
theorem identityComponentι_hom_hom : (identityComponentι H).hom.hom = inclusionOver H :=
  rfl

/-- The unit of `H⁰` is the restricted unit `one H`. -/
theorem one_identityComponent : η[(identityComponent H).X] = one H :=
  rfl

/-- The multiplication of `H⁰` is the restricted multiplication `mul H`. -/
theorem mul_identityComponent : μ[(identityComponent H).X] = mul H :=
  rfl

/-- The inverse of `H⁰` is the restricted inverse `inv H`. -/
theorem inv_identityComponent : ι[(identityComponent H).X] = inv H :=
  rfl

instance isOpenImmersion_identityComponentι :
    IsOpenImmersion (identityComponentι H).hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (inclusionOver H).left)

instance isClosedImmersion_identityComponentι :
    IsClosedImmersion (identityComponentι H).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver H).left)

theorem isClosedSubgroup_identityComponentι : IsClosedSubgroup (identityComponentι H) :=
  inferInstanceAs (IsClosedImmersion (inclusionOver H).left)

/-- The topological range of the inclusion is the connected component of the identity point. -/
theorem range_identityComponentι :
    Set.range (identityComponentι H).hom.hom.left = connectedComponent (identityPoint H) :=
  range_inclusionOver H

instance smooth_identityComponent : Smooth (identityComponent H).X.hom :=
  smooth_identityComponentOver H

instance isAffineHom_identityComponent : IsAffineHom (identityComponent H).X.hom :=
  isAffineHom_identityComponentOver H

instance connectedSpace_identityComponent : ConnectedSpace (identityComponent H).X.left :=
  connectedSpace_identityComponentOver H

instance geometricallyConnected_identityComponent :
    GeometricallyConnected (identityComponent H).X.hom :=
  geometricallyConnected_identityComponentOver H

instance geometricallyIrreducible_identityComponent :
    GeometricallyIrreducible (identityComponent H).X.hom :=
  geometricallyIrreducible_identityComponentOver H

instance irreducibleSpace_identityComponent : IrreducibleSpace (identityComponent H).X.left :=
  irreducibleSpace_identityComponentOver H

instance mono_identityComponentι : Mono (identityComponentι H) where
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
theorem isNormal_range_identityComponentι :
    (SubgroupFunctor.range (identityComponentι H)).IsNormal := by
  intro T g x _ hx
  rw [SubgroupFunctor.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨liftOver (inclusionOver H) (lift g y ≫ conjOver H) ?_, ?_⟩
  · rw [range_inclusionOver]
    rintro _ ⟨t, rfl⟩
    exact range_conjOver_subset H ⟨(lift g y).left t, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rw [identityComponentι_hom_hom, liftOver_fac, lift_conjOver]

/-! ### Factorization of homomorphisms from connected group schemes -/

section Factor

variable {K : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace K.X.left] (f : K ⟶ H)

theorem range_subset_range_identityComponentι :
    Set.range f.hom.hom.left ⊆ Set.range (identityComponentι H).hom.hom.left := by
  rw [range_identityComponentι]
  exact range_subset_identitySet H f.hom.hom η[K.X] (IsMonHom.one_hom _)

/-- The factorization through `H⁰` of a homomorphism from a connected group scheme. -/
def factor : K ⟶ identityComponent H :=
  liftHom (identityComponentι H) f (range_subset_range_identityComponentι H f)

@[reassoc (attr := simp)]
theorem factor_identityComponentι : factor H f ≫ identityComponentι H = f :=
  liftHom_fac _ _ _

theorem eq_factor (g : K ⟶ identityComponent H) (hg : g ≫ identityComponentι H = f) :
    g = factor H f :=
  hom_ext_of_isOpenImmersion (identityComponentι H) (hg.trans (factor_identityComponentι H f).symm)

theorem existsUnique_factor : ∃! g : K ⟶ identityComponent H, g ≫ identityComponentι H = f :=
  ⟨factor H f, factor_identityComponentι H f, eq_factor H f⟩

/-- Homomorphisms from a connected group scheme into `H⁰` are the homomorphisms into `H`. -/
def homEquiv : (K ⟶ identityComponent H) ≃ (K ⟶ H) where
  toFun g := g ≫ identityComponentι H
  invFun f := factor H f
  left_inv g := (eq_factor H _ g rfl).symm
  right_inv f := factor_identityComponentι H f

end Factor

/-- Split tori over `k` are connected, so homomorphisms from them factor through `H⁰`. -/
instance connectedSpace_splitTorus (I : Type u) [Finite I] :
    ConnectedSpace (splitTorus (Spec (CommRingCat.of k)) I).X.left :=
  IsSplitTorus.connectedSpace ⟨I, inferInstance, ⟨Iso.refl _⟩⟩

/-- A homomorphism from a group scheme which is a split torus factors uniquely through `H⁰`. -/
theorem existsUnique_factor_of_isSplitTorus {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T) (f : T ⟶ H) :
    ∃! g : T ⟶ identityComponent H, g ≫ identityComponentι H = f :=
  haveI := hT.connectedSpace
  existsUnique_factor H f

/-! ### Characterization as the connected open and closed subgroup -/

section Characterization

variable {P : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace P.X.left] (j : P ⟶ H)
  [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]

omit [Smooth H.X.hom] [IsAffineHom H.X.hom] in
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
def isoOfIsOpenImmersion : P ≅ identityComponent H where
  hom := factor H j
  inv := liftHom j (identityComponentι H) (by
    rw [range_identityComponentι, range_eq_identitySet])
  hom_inv_id := hom_ext_of_isOpenImmersion j (by simp)
  inv_hom_id := hom_ext_of_isOpenImmersion (identityComponentι H) (by simp)

@[reassoc (attr := simp)]
theorem isoOfIsOpenImmersion_hom_identityComponentι :
    (isoOfIsOpenImmersion H j).hom ≫ identityComponentι H = j :=
  factor_identityComponentι H j

@[reassoc (attr := simp)]
theorem isoOfIsOpenImmersion_inv_comp :
    (isoOfIsOpenImmersion H j).inv ≫ j = identityComponentι H :=
  liftHom_fac _ _ _

end Characterization

/-! ### Compatibility with extension of the ground field -/

section BaseChange

variable {L : Type u} [Field L] (φ : k →+* L)

/-- The morphism `Spec L ⟶ Spec k` induced by a field embedding `k →+* L`. -/
abbrev specMap : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom φ)

instance smooth_baseChange : Smooth ((GroupScheme.baseChange (specMap φ)).obj H).X.hom :=
  inferInstanceAs (Smooth (pullback.snd H.X.hom (specMap φ)))

instance isAffineHom_baseChange :
    IsAffineHom ((GroupScheme.baseChange (specMap φ)).obj H).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (specMap φ)))

instance : IsOpenImmersion
    ((GroupScheme.baseChange (specMap φ)).map (identityComponentι H)).hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (specMap φ) (inclusionOver H)
    (inferInstanceAs (IsOpenImmersion (inclusionOver H).left))

instance : IsClosedImmersion
    ((GroupScheme.baseChange (specMap φ)).map (identityComponentι H)).hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (specMap φ) (inclusionOver H)
    (inferInstanceAs (IsClosedImmersion (inclusionOver H).left))

instance : ConnectedSpace
    ((GroupScheme.baseChange (specMap φ)).obj (identityComponent H)).X.left :=
  @GeometricallyConnected.connectedSpace_of_subsingleton _ _
    (pullback.snd (identityComponentOver H).hom (specMap φ))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @GeometricallyConnected.{u})
      (IsPullback.of_hasPullback _ _) (geometricallyConnected_identityComponentOver H)) _ _

/-- Formation of the identity component commutes with extension of the ground field: the base
change of `H⁰` along `Spec L ⟶ Spec k` is the identity component of the base change of `H`. -/
def baseChangeIso :
    (GroupScheme.baseChange (specMap φ)).obj (identityComponent H) ≅
      identityComponent ((GroupScheme.baseChange (specMap φ)).obj H) :=
  isoOfIsOpenImmersion _ ((GroupScheme.baseChange (specMap φ)).map (identityComponentι H))

/-- The comparison isomorphism identifies the two inclusions into the base change of `H`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_identityComponentι :
    (baseChangeIso H φ).hom ≫ identityComponentι ((GroupScheme.baseChange (specMap φ)).obj H) =
      (GroupScheme.baseChange (specMap φ)).map (identityComponentι H) :=
  isoOfIsOpenImmersion_hom_identityComponentι _ _

@[reassoc (attr := simp)]
theorem baseChangeIso_inv_comp :
    (baseChangeIso H φ).inv ≫ (GroupScheme.baseChange (specMap φ)).map (identityComponentι H) =
      identityComponentι ((GroupScheme.baseChange (specMap φ)).obj H) :=
  isoOfIsOpenImmersion_inv_comp _ _

end BaseChange

end Smooth

end Langlands.GroupScheme.IdentityComponent
