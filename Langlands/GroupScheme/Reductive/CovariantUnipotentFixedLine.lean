import Langlands.GroupScheme.Reductive.CovariantRegularFixedLine

/-! # Normalized covariant fixed vectors from unipotence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  {G H U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

namespace AffineCoordinates

/-- A covariant right-invariant coordinate vanishing at the identity vanishes
everywhere, when a supplied nonzerodivisor unit locus has the product form. -/
theorem eq_zero_of_covariant_rightInvariant_counit_eq_zero
    (i : H ⟶ G) (j : U ⟶ G) (χ : algebra H) {q f : algebra G}
    (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ) (hfU : f ∈ rightInvariantSubspace j)
    (hf1 : counit (corepresentation G) f = 0) :
    f = 0 := by
  apply eq_of_pointAlgebraHom_eq_on_unit_locus hq
  intro T g hg
  obtain ⟨a, u, rfl⟩ := hcell T g hg
  have he := pointAlgebraHom_leftCovariant i χ hf T a 1
  rw [mul_one, pointAlgebraHom_one_apply, hf1, map_zero, mul_zero] at he
  rw [hfU T u _, he, map_zero]

/-- On the supplied product cell, the counit is nonzero on every nonzero
right-invariant covariant coordinate. -/
theorem counit_ne_zero_of_covariant_rightInvariant
    (i : H ⟶ G) (j : U ⟶ G) (χ : algebra H) {q f : algebra G}
    (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ) (hfU : f ∈ rightInvariantSubspace j)
    (hf0 : f ≠ 0) :
    counit (corepresentation G) f ≠ 0 :=
  fun he => hf0 (eq_zero_of_covariant_rightInvariant_counit_eq_zero
    i j χ hq hcell hf hfU he)

end AffineCoordinates

namespace Chevalley

variable (G)
  (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (algebra G)) (w : algebra G),
      w ∈ V → rightAct f w ∈ V)

/-- Unipotence and the supplied product cell provide a normalized fixed
vector and identify the entire restricted fixed submodule. The nonzero
regular subspace is allowed to be the entire covariant space. -/
theorem affineRegularRepresentation_exists_normalized_fixedVector
    (i : H ⟶ G) (j : U ⟶ G) (hU : IsUnipotent U) (χ : algebra H)
    (hcov : V ≤ AffineCoordinates.leftCovariantSubspace i χ) (hV0 : V ≠ ⊥)
    {q : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom)) :
    ∃ v : Fin d → k,
      ((affineRegularRepresentation G V b hV).restrict j).IsFixedVector v ∧
      counit (corepresentation G) (affineRegularCoordinateMap G V b v) = 1 ∧
      ((affineRegularRepresentation G V b hV).restrict j).fixedSubmodule =
        Submodule.span k {v} := by
  let : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV0
  let : Nonempty (Fin d) := b.index_nonempty
  obtain ⟨w, hw0, hwfix⟩ := hU (Fin d)
    ((affineRegularRepresentation G V b hV).restrict j)
  have hwF : affineRegularCoordinateMap G V b w ≠ 0 := by
    intro hz
    apply hw0
    exact affineRegularCoordinateMap_injective G V b
      (hz.trans (map_zero (affineRegularCoordinateMap G V b)).symm)
  have hc0 := counit_ne_zero_of_covariant_rightInvariant i j χ hq hcell
    (hcov (affineRegularCoordinateMap_mem G V b w))
    (affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector G V b hV j hwfix) hwF
  let c := counit (corepresentation G) (affineRegularCoordinateMap G V b w)
  let v := c⁻¹ • w
  have hvfix : ((affineRegularRepresentation G V b hV).restrict j).IsFixedVector v :=
    ((affineRegularRepresentation G V b hV).restrict j).fixedSubmodule.smul_mem c⁻¹ hwfix
  have hv1 : counit (corepresentation G) (affineRegularCoordinateMap G V b v) = 1 := by
    change counit (corepresentation G)
      (affineRegularCoordinateMap G V b (c⁻¹ • w)) = 1
    rw [map_smul, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hc0
  exact ⟨v, hvfix, hv1,
    affineRegularRepresentation_fixedSubmodule_eq_span G V b hV
      i j χ hcov hq hcell v hvfix hv1⟩

/-- Every supplied normalized invariant covariant belongs to every nonzero
finite covariant regular subspace, and is represented by a fixed vector. -/
theorem affineRegularRepresentation_exists_fixedVector_of_normalized_covariant
    (i : H ⟶ G) (j : U ⟶ G) (hU : IsUnipotent U) (χ : algebra H)
    (hcov : V ≤ AffineCoordinates.leftCovariantSubspace i χ) (hV0 : V ≠ ⊥)
    {q f : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ) (hfU : f ∈ rightInvariantSubspace j)
    (hf1 : counit (corepresentation G) f = 1) :
    ∃ v : Fin d → k,
      affineRegularCoordinateMap G V b v = f ∧
      ((affineRegularRepresentation G V b hV).restrict j).IsFixedVector v ∧
      ((affineRegularRepresentation G V b hV).restrict j).fixedSubmodule =
        Submodule.span k {v} := by
  obtain ⟨v, hvfix, hv1, hvline⟩ :=
    affineRegularRepresentation_exists_normalized_fixedVector G V b hV
      i j hU χ hcov hV0 hq hcell
  refine ⟨v, ?_, hvfix, hvline⟩
  have he := eq_counit_smul_of_covariant_rightInvariant i j χ hq hcell
    (hcov (affineRegularCoordinateMap_mem G V b v))
    (affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector G V b hV j hvfix)
    hv1 hf hfU
  rw [hf1, one_smul] at he
  exact he.symm

section ChosenVector

variable (i : H ⟶ G) (j : U ⟶ G) (hU : IsUnipotent U) (χ : algebra H)
  (hcov : V ≤ AffineCoordinates.leftCovariantSubspace i χ) (hV0 : V ≠ ⊥)
  {q : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
  (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
    IsUnit (pointAlgebraHom G T g q) →
      ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
        g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))

/-- A chosen normalized fixed vector provided by unipotence and the supplied
nonzerodivisor product cell. -/
def affineRegularNormalizedFixedVector : Fin d → k :=
  Classical.choose (affineRegularRepresentation_exists_normalized_fixedVector G V b hV
    i j hU χ hcov hV0 hq hcell)

/-- The chosen vector is fixed on all tests, has coordinate counit one, and
spans the entire restricted fixed submodule. -/
theorem affineRegularNormalizedFixedVector_spec :
    let v := affineRegularNormalizedFixedVector G V b hV i j hU χ hcov hV0 hq hcell
    ((affineRegularRepresentation G V b hV).restrict j).IsFixedVector v ∧
      counit (corepresentation G) (affineRegularCoordinateMap G V b v) = 1 ∧
      ((affineRegularRepresentation G V b hV).restrict j).fixedSubmodule =
        Submodule.span k {v} :=
  Classical.choose_spec (affineRegularRepresentation_exists_normalized_fixedVector G V b hV
    i j hU χ hcov hV0 hq hcell)

end ChosenVector

end Chevalley

end Langlands.GroupScheme
