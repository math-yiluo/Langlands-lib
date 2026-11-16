import Langlands.GroupScheme.Reductive.RankOneRingCalculus
import Langlands.GroupScheme.Reductive.RankOneRootCellWeyl

/-! # Unit coordinates near an actual residue reflection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace RingRootCell

variable {k : Type u} [Field k]

/-- View ring cell data over a field in the field cell calculus. -/
def CellData.toFieldCellData (D : CellData k) : RankOneRootCellRelation.CellData k where
  G := D.G
  T := D.T
  i := D.i
  xp := D.xp
  xm := D.xm
  α := D.α
  hxp := D.hxp
  hxm := D.hxm
  open_cell := D.open_cell

/-- The field and ring scalar points have the same coordinate. -/
theorem field_gpt_eq {Z : Over (Spec (CommRingCat.of k))} (x : Γ(Z.left, ⊤)) :
    RankOneRootCellRelation.gpt x = gpt (k := k) x := by
  apply VectorGroup.points_ext
  intro j
  rw [RankOneRootCellRelation.coordinates_gpt, coordinates_gpt]

/-- On a field, any actual reflection normalizer with torus square in an
irreducible group has unit coordinates after multiplication by `xp(1)`. -/
theorem CellData.exists_unitFieldCellCoordinates (D : CellData k)
    (h : cocharacterLattice D.T)
    (hh : h ≫ D.α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k))))
    (pair : latticePairing D.T D.α h = 2)
    (n : base k ⟶ D.G.X)
    (hn : IsNormalizingPoint D.i n (reflectionIso D.α h hh))
    (hn2 : ∃ z : base k ⟶ D.T.X, n * n = z ≫ D.i.hom.hom)
    (hirr : IrreducibleSpace D.G.X.left) :
    ∃ β : Γ((base k).left, ⊤), ∃ t : base k ⟶ D.T.X,
      ∃ δ : Γ((base k).left, ⊤),
        IsUnit β ∧ IsUnit δ ∧ D.A 1 * n = D.cellPt β t δ := by
  have he : latticeReflectionIso D.α h pair = reflectionIso D.α h hh := by
    apply Iso.ext
    rfl
  let E : RankOneRootCellRelation.WeylData k :=
    { D.toFieldCellData with
      h := h, pair := pair, n := n, hn := he.symm ▸ hn, hn2 := hn2, irreducible := hirr }
  refine ⟨E.cβ, E.ct, E.cδ, E.cβ_isUnit, E.cδ_isUnit, ?_⟩
  have hE := E.A_one_mul_N_base
  simpa only [RankOneRootCellRelation.WeylData.N,
    GroupScheme.constantPoint_self, RankOneRootCellRelation.CellData.A,
    RankOneRootCellRelation.CellData.B, RankOneRootCellRelation.CellData.I,
    RankOneRootCellRelation.CellData.cellPt, CellData.A, CellData.B,
    CellData.I, CellData.cellPt, field_gpt_eq, E, CellData.toFieldCellData] using hE

end RingRootCell

namespace LocalRankOneUnitCell

/-- A section whose unit locus contains the image of a scheme map pulls
back to a global unit. -/
theorem isUnit_appTop_of_range_subset_basicOpen {X Y : Scheme.{u}}
    (b : Y ⟶ X) (f : Γ(X, ⊤))
    (hf : Set.range b ⊆ X.basicOpen f) : IsUnit (b.appTop f) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ (b.appTop f)
  intro y hy
  apply (Y.mem_basicOpen (b.appTop f) y hy).mp
  rw [← Scheme.preimage_basicOpen_top]
  exact hf ⟨y, rfl⟩

/-- An affine open neighbourhood on which two specified functions are units,
with exact recovery of the supplied field point. -/
structure AffineUnitRestrictionData {X : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ X) (f g : Γ(X, ⊤)) where
  ring : CommRingCat.{u}
  inclusion : Spec ring ⟶ X
  openImmersion : IsOpenImmersion inclusion
  point : Spec (CommRingCat.of k) ⟶ Spec ring
  point_comp : point ≫ inclusion = b
  unit_left : IsUnit (inclusion.appTop f)
  unit_right : IsUnit (inclusion.appTop g)

/-- Functions which are units at a supplied field point become units on an
affine open neighbourhood retaining that exact field point. -/
def affineUnitRestriction {X : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ X) (f g : Γ(X, ⊤))
    (hf : IsUnit (b.appTop f)) (hg : IsUnit (b.appTop g)) :
    AffineUnitRestrictionData b f g := Classical.choice <| by
  have hbf : b default ∈ X.basicOpen f := by
    have h := (Spec (CommRingCat.of k)).basicOpen_of_isUnit hf
    rw [← Scheme.preimage_basicOpen_top] at h
    exact (congrArg (fun U : (Spec (CommRingCat.of k)).Opens => default ∈ U) h).mpr trivial
  have hbg : b default ∈ X.basicOpen g := by
    have h := (Spec (CommRingCat.of k)).basicOpen_of_isUnit hg
    rw [← Scheme.preimage_basicOpen_top] at h
    exact (congrArg (fun U : (Spec (CommRingCat.of k)).Opens => default ∈ U) h).mpr trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show b default ∈ X.basicOpen f ⊓ X.basicOpen g from ⟨hbf, hbg⟩)
  have hrange : Set.range b ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [show x = default from Subsingleton.elim _ _]
    exact hxU
  refine ⟨{ ring := Γ(X, U), inclusion := hU.fromSpec, openImmersion := inferInstance
            point := IsOpenImmersion.lift hU.fromSpec b hrange
            point_comp := IsOpenImmersion.lift_fac ..
            unit_left := ?_, unit_right := ?_ }⟩
  · apply isUnit_appTop_of_range_subset_basicOpen
    rw [hU.range_fromSpec]
    exact fun x hx => (hUV hx).1
  · apply isUnit_appTop_of_range_subset_basicOpen
    rw [hU.range_fromSpec]
    exact fun x hx => (hUV hx).2

end LocalRankOneUnitCell

end Langlands.GroupScheme
