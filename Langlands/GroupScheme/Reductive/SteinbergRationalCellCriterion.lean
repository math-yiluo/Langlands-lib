import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Rational-point detection of coordinate principal opens inside open cells -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- A coordinate evaluates to a global unit exactly when the entire image of
the test scheme lies in its principal open. No reducedness or affineness of
the test scheme is needed. -/
theorem isUnit_pointAlgebraHom_iff_range_subset_basicOpen
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (d : algebra G) :
    IsUnit (pointAlgebraHom G T g d) ↔
      Set.range g.left ⊆ (G.X.left.basicOpen (globalAlgHom G d) : Set G.X.left) := by
  rw [pointAlgebraHom_apply_eq]
  constructor
  · intro hd
    have hpre : g.left ⁻¹ᵁ G.X.left.basicOpen (globalAlgHom G d) = ⊤ := by
      rw [Scheme.preimage_basicOpen_top, T.left.basicOpen_of_isUnit hd]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ g.left ⁻¹ᵁ G.X.left.basicOpen (globalAlgHom G d) := by
      rw [hpre]
      trivial
    exact hx
  · intro hr
    apply T.left.toRingedSpace.isUnit_of_isUnit_germ ⊤ _
    intro x _
    apply (T.left.mem_basicOpen_top _ x).mp
    rw [← Scheme.preimage_basicOpen_top]
    exact hr ⟨x, rfl⟩

section AlgebraicallyClosed

variable [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]

/-- Containment of a coordinate principal open in another open can be checked
on the rational points where the coordinate is a unit. -/
theorem basicOpen_le_open_of_rational_units (d : algebra G) (V : G.X.left.Opens)
    (hV : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsUnit (pointAlgebraHom G _ g d) →
        g.left (IsLocalRing.closedPoint k) ∈ V) :
    G.X.left.basicOpen (globalAlgHom G d) ≤ V := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  intro x hx
  by_contra hxV
  let O := G.X.left.basicOpen (globalAlgHom G d)
  obtain ⟨c, hc, hcc⟩ := nonempty_inter_closedPoints
    (Z := (O : Set G.X.left) ∩ (V : Set G.X.left)ᶜ) ⟨x, hx, hxV⟩
    (O.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  have hclosed : IsClosed {c} := hcc
  let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom c hclosed)
      (pointOfClosedPoint_comp G.X.hom c hclosed)
  have ha : IsUnit (pointAlgebraHom G _ a d) := by
    apply (isUnit_pointAlgebraHom_iff_range_subset_basicOpen G a d).mpr
    rintro _ ⟨s, rfl⟩
    change pointOfClosedPoint G.X.hom c hclosed s ∈ O
    rw [pointOfClosedPoint_apply]
    exact hc.1
  have hav := hV a ha
  change pointOfClosedPoint G.X.hom c hclosed (IsLocalRing.closedPoint k) ∈ V at hav
  rw [pointOfClosedPoint_apply] at hav
  exact hc.2 hav

/-- Rational factorization on the unit locus detects containment of the entire
coordinate principal open in a supplied open multiplication cell. -/
theorem basicOpen_subset_cell_of_rational_factorization
    {U P : GroupScheme (Spec (CommRingCat.of k))} (iU : U ⟶ G) (iP : P ⟶ G)
    [IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left]
    (d : algebra G)
    (hcell : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsUnit (pointAlgebraHom G _ g d) →
        ∃ (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)
          (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X),
          g = (a ≫ iU.hom.hom) * (b ≫ iP.hom.hom)) :
    (G.X.left.basicOpen (globalAlgHom G d) : Set G.X.left) ⊆
      Set.range (SubgroupFunctor.cellMultiplication iU iP).left := by
  have h := basicOpen_le_open_of_rational_units G d
    (SubgroupFunctor.cellMultiplication iU iP).left.opensRange (by
      intro g hg
      obtain ⟨a, b, he⟩ := hcell g hg
      apply Scheme.Hom.mem_opensRange.mpr
      refine ⟨(lift a b).left (IsLocalRing.closedPoint k), ?_⟩
      have hl : lift a b ≫ SubgroupFunctor.cellMultiplication iU iP = g :=
        (SubgroupFunctor.lift_cellMultiplication iU iP a b).trans he.symm
      exact congrArg (fun z => z.left (IsLocalRing.closedPoint k)) hl)
  exact h

/-- Rational factorization on the unit locus forces every unit-valued
test-scheme point to have its entire image in the same open cell. -/
theorem range_point_subset_cell_of_rational_factorization
    {U P : GroupScheme (Spec (CommRingCat.of k))} (iU : U ⟶ G) (iP : P ⟶ G)
    [IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left]
    (d : algebra G)
    (hcell : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsUnit (pointAlgebraHom G _ g d) →
        ∃ (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)
          (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X),
          g = (a ≫ iU.hom.hom) * (b ≫ iP.hom.hom))
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X)
    (hd : IsUnit (pointAlgebraHom G T g d)) :
    Set.range g.left ⊆ Set.range (SubgroupFunctor.cellMultiplication iU iP).left :=
  ((isUnit_pointAlgebraHom_iff_range_subset_basicOpen G g d).mp hd).trans
    (basicOpen_subset_cell_of_rational_factorization G iU iP d hcell)

/-- An actual global lift into the open multiplication cell for every
unit-valued test point, constructed from the rational factorization criterion. -/
def unitPointCellLift
    {U P : GroupScheme (Spec (CommRingCat.of k))} (iU : U ⟶ G) (iP : P ⟶ G)
    [IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left]
    (d : algebra G)
    (hcell : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsUnit (pointAlgebraHom G _ g d) →
        ∃ (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)
          (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X),
          g = (a ≫ iU.hom.hom) * (b ≫ iP.hom.hom))
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X)
    (hd : IsUnit (pointAlgebraHom G T g d)) :
    T ⟶ U.X ⊗ P.X := by
  let f := SubgroupFunctor.cellMultiplication iU iP
  have hr := range_point_subset_cell_of_rational_factorization G iU iP d hcell g hd
  let l := IsOpenImmersion.lift f.left g.left hr
  have hl : l ≫ f.left = g.left := IsOpenImmersion.lift_fac f.left g.left hr
  exact Over.homMk l (by
    calc
      l ≫ (U.X ⊗ P.X).hom = l ≫ (f.left ≫ G.X.hom) := by rw [Over.w]
      _ = g.left ≫ G.X.hom := by rw [← Category.assoc, hl]
      _ = T.hom := g.w)

/-- Multiplication of the constructed unit-locus lift is the original point. -/
theorem unitPointCellLift_comp
    {U P : GroupScheme (Spec (CommRingCat.of k))} (iU : U ⟶ G) (iP : P ⟶ G)
    [IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left]
    (d : algebra G)
    (hcell : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsUnit (pointAlgebraHom G _ g d) →
        ∃ (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)
          (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X),
          g = (a ≫ iU.hom.hom) * (b ≫ iP.hom.hom))
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X)
    (hd : IsUnit (pointAlgebraHom G T g d)) :
    unitPointCellLift G iU iP d hcell g hd ≫
      SubgroupFunctor.cellMultiplication iU iP = g := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

end AlgebraicallyClosed

end Langlands.GroupScheme.AffineCoordinates
