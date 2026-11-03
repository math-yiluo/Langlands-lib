import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Homomorphisms from unipotent group schemes to split tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every homomorphism from a unipotent group scheme to a split torus sends every point
on every test scheme to the identity. -/
theorem IsUnipotent.comp_eq_one_of_isSplitTorus (hH : IsUnipotent H)
    (hG : IsSplitTorus G) (f : H ⟶ G) (T : Over (Spec (CommRingCat.of k)))
    (y : T ⟶ H.X) : y ≫ f.hom.hom = 1 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  apply ((isoPointsEquiv e T).trans (splitTorus.pointsEquiv I T)).injective
  rw [map_one]
  funext j
  apply Units.ext
  obtain ⟨v, hv0, hv⟩ := hH Unit (splitTorus.coordinateRepresentation (f ≫ e.hom) j)
  have h := congrFun (hv T y) ()
  rw [splitTorus.pointMatrix_coordinateRepresentation, GeneralLinear.coe_diagonalUnits,
    Matrix.mulVec_diagonal] at h
  have hv1 : v () ≠ 0 := fun h0 => hv0 (funext fun t => by cases t; exact h0)
  have hu : IsUnit (scalarMap T (v ())) := (Ne.isUnit hv1).map (scalarMap T)
  have h' := hu.mul_eq_right.1 (by simpa using h)
  simpa [Category.assoc] using h'

/-- The all-test-scheme image of a homomorphism from a unipotent group scheme to a split
 torus is the identity subgroup functor. -/
theorem IsUnipotent.range_eq_bot_of_isSplitTorus (hH : IsUnipotent H)
    (hG : IsSplitTorus G) (f : H ⟶ G) : SubgroupFunctor.range f = ⊥ := by
  ext T x
  constructor
  · rintro ⟨y, rfl⟩
    exact (Subgroup.mem_bot).2 (hH.comp_eq_one_of_isSplitTorus hG f T y)
  · intro hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    subst hx
    exact Subgroup.one_mem ((SubgroupFunctor.range f).carrier T)

/-- Every homomorphism from a unipotent group scheme to a split torus is the trivial
homomorphism. -/
theorem IsUnipotent.hom_eq_zero_of_isSplitTorus (hH : IsUnipotent H)
    (hG : IsSplitTorus G) (f : H ⟶ G) : f = 0 := by
  apply (Grp.forget _).map_injective
  change f.hom.hom = (1 : H.X ⟶ G.X)
  simpa only [Category.id_comp] using hH.comp_eq_one_of_isSplitTorus hG f H.X (𝟙 H.X)

/-- There is exactly one homomorphism from a unipotent group scheme to a split torus. -/
@[instance_reducible] def IsUnipotent.uniqueHomToSplitTorus (hH : IsUnipotent H) (hG : IsSplitTorus G) :
    Unique (H ⟶ G) where
  default := 0
  uniq f := hH.hom_eq_zero_of_isSplitTorus hG f

/-- A homomorphism factoring through a split torus from a unipotent group scheme is
trivial. -/
theorem IsUnipotent.comp_eq_zero_of_isSplitTorus (hH : IsUnipotent H)
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T)
    (f : H ⟶ T) (i : T ⟶ G) : f ≫ i = 0 := by
  rw [hH.hom_eq_zero_of_isSplitTorus hT f, zero_comp]

/-- A monic subgroup of an ambient group that is both unipotent and contained in the
range of a monic split-torus inclusion is the identity subgroup on all test schemes. -/
theorem IsUnipotent.range_eq_bot_of_range_le_isSplitTorus (hH : IsUnipotent H)
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T)
    (f : H ⟶ G) (i : T ⟶ G) [Mono f.hom.hom] [Mono i.hom.hom]
    (h : SubgroupFunctor.range f ≤ SubgroupFunctor.range i) :
    SubgroupFunctor.range f = ⊥ := by
  let g := SubgroupFunctor.factorOfRangeLE h
  have hg : g ≫ i = f := SubgroupFunctor.factorOfRangeLE_comp h
  have hf : f = 0 := hg.symm.trans (hH.comp_eq_zero_of_isSplitTorus hT g i)
  ext U x
  constructor
  · rintro ⟨y, rfl⟩
    rw [hf]
    exact (Subgroup.mem_bot).2 (by
      change y ≫ (1 : H.X ⟶ G.X) = 1
      exact MonObj.comp_one y)
  · intro hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    subst hx
    exact Subgroup.one_mem ((SubgroupFunctor.range f).carrier U)

end Langlands.GroupScheme
