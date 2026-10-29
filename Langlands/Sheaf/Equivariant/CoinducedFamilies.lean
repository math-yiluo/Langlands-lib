import Langlands.Sheaf.Equivariant.FamilySections
import Langlands.Sheaf.Equivariant.CoinducedFamilies.Coordinates

/-!
# The equivariant sheaf of indexed coefficient families

For a family of modules `A y` indexed by the points of `X`, the sections over a
transport object `U` are the families `(s g y)` indexed by a group element `g`
and a point `y` with `g • y ∈ U`. A transport arrow multiplies the group index
on the left. For the stalk family of an equivariant sheaf this is the published
coinduction of the ordinary sheaf of arbitrary stalk families.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.CoinducedFamilies

open Langlands.Cohomology.CompactSoft (FamilySections)

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X]

section FamilySections

variable (A : X → ModuleCat.{u} R)

variable {A} in
/-- Equal group labels give the same entry, including its membership proof. -/
theorem families_congr {U : ActionOpens G X} (s : FamilySections A U)
    {g h : G} (e : g = h) (y : X)
    (hg : g • y ∈ U.openSet) (hh : h • y ∈ U.openSet) :
    s g ⟨y, hg⟩ = s h ⟨y, hh⟩ := by
  subst h
  rfl

/-- Pull back a family along a transport arrow by multiplying its label on the left. -/
def familyPull {U V : ActionOpens G X} (f : U ⟶ V) : FamilySections A V →ₗ[R] FamilySections A U where
  toFun s g y := s (f.label * g) ⟨y.1, by simpa only [mul_smul] using f.mapsTo (g • y.1) y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The transport presheaf of indexed coefficient families. -/
def presheaf : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (FamilySections A U.unop)
  map f := ModuleCat.ofHom (familyPull A f.unop)
  map_id U := by
    ext s g y
    exact families_congr s (one_mul g) y.1 _ y.2
  map_comp f k := by
    ext s g y
    exact families_congr s (mul_assoc _ _ _) y.1 _ _

/-- Coordinate evaluation along an arbitrary transport arrow. -/
theorem presheaf_map_apply {U V : ActionOpens G X} (f : U ⟶ V)
    (s : FamilySections A V) (g : G) (y : X) (hy : g • y ∈ U.openSet) :
    (presheaf A).map f.op s g ⟨y, hy⟩ =
      s (f.label * g) ⟨y, by simpa only [mul_smul] using f.mapsTo (g • y) hy⟩ :=
  rfl

/-- A label-one inclusion drops the entries outside the smaller open. -/
theorem presheaf_map_inclusionHom_apply {U V : ActionOpens G X}
    (h : U.openSet ≤ V.openSet) (s : FamilySections A V) (g : G) (y : X)
    (hy : g • y ∈ U.openSet) :
    (presheaf A).map (ActionOpens.inclusionHom h).op s g ⟨y, hy⟩ = s g ⟨y, h hy⟩ :=
  families_congr s (one_mul g) y _ _

/-- Ordinary restriction of the underlying presheaf drops entries. -/
theorem underlying_map_apply {V W : Opens X} (i : V ⟶ W)
    (s : FamilySections A ((ActionOpens.inclusion G X).obj W)) (g : G) (y : X) (hy : g • y ∈ V) :
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (presheaf A)).map i.op s g ⟨y, hy⟩ =
      s g ⟨y, i.le hy⟩ :=
  families_congr s (one_mul g) y _ _

/-- Indexed families satisfy the ordinary sheaf condition. -/
theorem isSheaf : sheafProperty G X (ModuleCat.{u} R) (presheaf A) := by
  change ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (presheaf A)).IsSheaf
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hmem : ∀ (g : G) (y : {y : X // g • y ∈ (iSup U : Opens X)}), ∃ i, g • y.1 ∈ U i :=
    fun g y => Opens.mem_iSup.1 y.2
  choose idx hidx using hmem
  have hcompat : ∀ (i j : ι) (g : G) (y : X) (hi : g • y ∈ U i) (hj : g • y ∈ U j),
      sf i g ⟨y, hi⟩ = sf j g ⟨y, hj⟩ := by
    intro i j g y hi hj
    have hij : g • y ∈ U i ⊓ U j := ⟨hi, hj⟩
    have h := congrArg
      (fun t : FamilySections A ((ActionOpens.inclusion G X).obj (U i ⊓ U j)) => t g ⟨y, hij⟩)
      (hsf i j)
    exact (underlying_map_apply A (Opens.infLELeft (U i) (U j)) (sf i) g y hij).symm.trans
      (h.trans (underlying_map_apply A (Opens.infLERight (U i) (U j)) (sf j) g y hij))
  let s : FamilySections A ((ActionOpens.inclusion G X).obj (iSup U)) :=
    fun g y => sf (idx g y) g ⟨y.1, hidx g y⟩
  refine ⟨s, fun i => ?_, fun t ht => ?_⟩
  · funext g y
    exact (underlying_map_apply A _ s g y.1 y.2).trans (hcompat _ _ _ _ _ _)
  · funext g y
    have h := congrArg
      (fun t : FamilySections A ((ActionOpens.inclusion G X).obj (U (idx g y))) =>
        t g ⟨y.1, hidx g y⟩)
      (ht (idx g y))
    exact (underlying_map_apply A _ t g y.1 (hidx g y)).symm.trans h

/-- The equivariant module sheaf of indexed coefficient families. -/
def sheaf : TopologicalSheaf G X (ModuleCat.{u} R) :=
  ⟨presheaf A, isSheaf A⟩

end FamilySections

section Comparison

variable [ContinuousConstSMul G X]
variable (F : TopologicalSheaf G X (ModuleCat.{u} R))

/-- The coordinates of the published coinduction are natural in all transport arrows. -/
def coinducedZeroPresheafIso : (coinducedZero F).obj ≅ presheaf (Coefficients F) :=
  NatIso.ofComponents (fun U => coordinateIso F U.unop) (by
    intro U V f
    ext s
    funext g y
    exact read_map F f.unop s g y.1 y.2)

/-- The published coinduction of the ordinary Godement sheaf is the sheaf of
indexed stalk families. -/
def coinducedZeroIso : coinducedZero F ≅ sheaf (Coefficients F) :=
  ObjectProperty.isoMk _ (coinducedZeroPresheafIso F)

/-- The comparison reads a section through the published coordinates. -/
theorem coinducedZeroIso_hom_apply (U : ActionOpens G X)
    (s : (coinducedZero F).obj.obj (op U)) :
    (coinducedZeroIso F).hom.hom.app (op U) s = read F U s :=
  rfl

/-- The inverse comparison is the inverse of the published coordinates. -/
theorem coinducedZeroIso_inv_apply (U : ActionOpens G X)
    (s : FamilySections (Coefficients F) U) :
    (coinducedZeroIso F).inv.hom.app (op U) s = (read F U).symm s :=
  rfl

end Comparison

end Langlands.Sheaf.Equivariant.CoinducedFamilies
