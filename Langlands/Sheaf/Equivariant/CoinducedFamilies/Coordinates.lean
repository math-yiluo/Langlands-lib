import Langlands.Sheaf.Equivariant.Coinduction
import Langlands.Sheaf.Equivariant.Godement.Zero

/-!
# Coordinates for coinduction of arbitrary stalk families
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.CoinducedFamilies

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable (F : TopologicalSheaf G X (ModuleCat.{u} R))

/-- The coefficient family of the underlying sheaf. -/
abbrev Coefficients (y : X) :=
  (((toSheaf G X (ModuleCat.{u} R)).obj F).presheaf.stalk y)

/-- Families indexed by a group element and a point it moves into the open. -/
abbrev Sections (U : ActionOpens G X) :=
  ∀ (g : G) (y : {y : X // g • y ∈ U.openSet}), Coefficients F y.1

/-- The ordinary sheaf of arbitrary stalk families. -/
abbrev ordinaryZero :=
  (toSheaf G X (ModuleCat.{u} R)).obj (Godement.zeroSheaf F.obj)

/-- The actual published coinduction of that ordinary sheaf. -/
abbrev coinducedZero :=
  (coinduction G X (ModuleCat.{u} R)).obj (ordinaryZero F)

/-- The inverse image of an open under a group translation. -/
def coordinateOpen (U : ActionOpens G X) (g : G) : Opens X :=
  ⟨{y | g • y ∈ U.openSet},
    U.openSet.isOpen.preimage (continuous_const_smul g)⟩

/-- The full translated open carries the coordinate with label `g`. -/
def coordinateArrow (U : ActionOpens G X) (g : G) :
    (ActionOpens.inclusion G X).obj (coordinateOpen U g) ⟶ U :=
  ⟨g, fun _ hy => hy⟩

omit [ContinuousConstSMul G X] in
/-- Equal group labels give the same coordinate, including its membership proof. -/
theorem sections_congr (U : ActionOpens G X) (s : Sections F U)
    {g h : G} (e : g = h) (y : X)
    (hg : g • y ∈ U.openSet) (hh : h • y ∈ U.openSet) :
    s g ⟨y, hg⟩ = s h ⟨y, hh⟩ := by
  subst h
  rfl

/-- The component of the explicit cone at a labelled ordinary open. -/
def familyComponent (U : ActionOpens G X)
    (d : StructuredArrow (op U) (ActionOpens.inclusion G X).op) :
    ModuleCat.of R (Sections F U) ⟶ (ordinaryZero F).obj.obj d.right :=
  ModuleCat.ofHom
    { toFun s y := s d.hom.unop.label ⟨y.1, d.hom.unop.mapsTo y.1 y.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- Arbitrary two-index families form a cone for the pointwise Kan diagram. -/
def familyCone (U : ActionOpens G X) :
    Cone (StructuredArrow.proj (op U) (ActionOpens.inclusion G X).op ⋙
      (ordinaryZero F).obj) where
  pt := ModuleCat.of R (Sections F U)
  π :=
    { app := familyComponent F U
      naturality := by
        intro d e f
        ext s
        funext y
        symm
        change
          Godement.stalkPull F.obj 1 y.1 ((1 : G) • y.1) rfl
              (familyComponent F U d s ⟨_, _⟩) =
            familyComponent F U e s y
        refine (Godement.stalkPull_one_section F.obj d.right.unop
          (familyComponent F U d s) y.1 _ (f.right.unop.le y.2) _ rfl).trans ?_
        apply sections_congr F U s
        have h := congrArg (fun a => a.unop.label) (StructuredArrow.w f)
        change d.hom.unop.label * (1 : G) = e.hom.unop.label at h
        simpa only [mul_one] using h }

/-- Every cone determines its family by evaluating on each full translated open. -/
def familyConeLift (U : ActionOpens G X)
    (c : Cone (StructuredArrow.proj (op U) (ActionOpens.inclusion G X).op ⋙
      (ordinaryZero F).obj)) : c.pt ⟶ (familyCone F U).pt :=
  ModuleCat.ofHom
    { toFun s g y :=
        c.π.app (StructuredArrow.mk (coordinateArrow U g).op) s ⟨y.1, y.2⟩
      map_add' s t := by
        funext g y
        exact congrFun (map_add (c.π.app (StructuredArrow.mk (coordinateArrow U g).op)).hom s t) ⟨y.1, y.2⟩
      map_smul' r s := by
        funext g y
        exact congrFun (map_smul (c.π.app (StructuredArrow.mk (coordinateArrow U g).op)).hom r s) ⟨y.1, y.2⟩ }

/-- The coordinate labelled by an arbitrary arrow restricts to its source open. -/
def coordinateFactor (U : ActionOpens G X)
    (d : StructuredArrow (op U) (ActionOpens.inclusion G X).op) :
    StructuredArrow.mk (coordinateArrow U d.hom.unop.label).op ⟶ d :=
  StructuredArrow.homMk
    (homOfLE (show d.right.unop ≤ coordinateOpen U d.hom.unop.label from
      d.hom.unop.mapsTo)).op (by
      apply Quiver.Hom.unop_inj
      apply ActionOpens.Hom.ext
      exact mul_one _)

/-- The explicit coordinate cone has the actual limit universal property. -/
def familyConeIsLimit (U : ActionOpens G X) : IsLimit (familyCone F U) where
  lift := familyConeLift F U
  fac c d := by
    ext s
    funext y
    have h := congrArg (fun a => a s) (c.w (coordinateFactor U d))
    change
      (ordinaryZero F).obj.map (coordinateFactor U d).right
          (c.π.app (StructuredArrow.mk (coordinateArrow U d.hom.unop.label).op) s) =
        c.π.app d s at h
    have h' := congrFun h y
    change
      Godement.stalkPull F.obj 1 y.1 ((1 : G) • y.1) rfl
          (c.π.app (StructuredArrow.mk (coordinateArrow U d.hom.unop.label).op) s
            ⟨_, _⟩) =
        c.π.app d s y at h'
    exact (Godement.stalkPull_one_section F.obj (coordinateOpen U d.hom.unop.label)
      (c.π.app (StructuredArrow.mk (coordinateArrow U d.hom.unop.label).op) s)
      y.1 _ (d.hom.unop.mapsTo _ y.2) _ rfl).symm.trans h'
  uniq c m hm := by
    ext s
    funext g y
    have h := congrArg (fun a => a s) (hm (StructuredArrow.mk (coordinateArrow U g).op))
    exact congrFun h ⟨y.1, y.2⟩

/-- The actual coinduction has the explicit family coordinates. -/
def coordinateIso (U : ActionOpens G X) :
    (coinducedZero F).obj.obj (op U) ≅ ModuleCat.of R (Sections F U) :=
  ((ActionOpens.inclusion G X).op.isPointwiseRightKanExtensionRanCounit
    (ordinaryZero F).obj (op U)).conePointUniqueUpToIso (familyConeIsLimit F U)

/-- Linear coordinates on the sections of the published coinduction. -/
def read (U : ActionOpens G X) :
    (coinducedZero F).obj.obj (op U) ≃ₗ[R] Sections F U :=
  (coordinateIso F U).toLinearEquiv

/-- A coordinate can be evaluated on any ordinary source open with its label. -/
theorem read_arrow (U : ActionOpens G X) (W : Opens X)
    (k : (ActionOpens.inclusion G X).obj W ⟶ U)
    (s : (coinducedZero F).obj.obj (op U)) (y : W) :
    read F U s k.label ⟨y.1, k.mapsTo y.1 y.2⟩ =
      ((ActionOpens.inclusion G X).op.ranCounit.app (ordinaryZero F).obj).app (op W)
        ((coinducedZero F).obj.map k.op s) y := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    ((ActionOpens.inclusion G X).op.isPointwiseRightKanExtensionRanCounit
      (ordinaryZero F).obj (op U)) (familyConeIsLimit F U)
    (StructuredArrow.mk k.op)
  exact congrFun (congrArg (fun a => a s) h) y

/-- Transport changes the label by left multiplication and keeps the stalk point. -/
theorem read_map {U V : ActionOpens G X} (f : U ⟶ V)
    (s : (coinducedZero F).obj.obj (op V)) (g : G) (y : X)
    (hy : g • y ∈ U.openSet) :
    read F U ((coinducedZero F).obj.map f.op s) g ⟨y, hy⟩ =
      read F V s (f.label * g)
        ⟨y, by simpa only [mul_smul] using f.mapsTo (g • y) hy⟩ := by
  have h₁ := read_arrow F U (coordinateOpen U g) (coordinateArrow U g)
    ((coinducedZero F).obj.map f.op s) ⟨y, hy⟩
  have h₂ := read_arrow F V (coordinateOpen U g) (coordinateArrow U g ≫ f)
    s ⟨y, hy⟩
  have he := congrArg
    (fun a =>
      ((ActionOpens.inclusion G X).op.ranCounit.app (ordinaryZero F).obj).app
        (op (coordinateOpen U g)) (a s) ⟨y, hy⟩)
    ((coinducedZero F).obj.map_comp f.op (coordinateArrow U g).op)
  exact h₁.trans (he.symm.trans h₂.symm)

end Langlands.Sheaf.Equivariant.CoinducedFamilies
