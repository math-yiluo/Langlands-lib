import Langlands.GroupScheme.Rational.CoordinateWeightDecompositionProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.KernelCentralizerTangent
import Langlands.GroupScheme.MultiplicativeLaurent
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Dynamic.ActionConjugation

/-! # A cocharacter with the fixed subgroup of a split torus -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- Finite-type actual coordinates admit finitely many eigenfunction generators. -/
theorem exists_finset_eigenfunction_generators [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G) :
    ∃ s : Finset (CharacterUnits.Coord G),
      Algebra.adjoin k (s : Set (CharacterUnits.Coord G)) = ⊤ ∧
        ∀ f ∈ s, ∃ χ, f ∈ weightSpace b χ := by
  classical
  let := (coordinateWeightDecomposition k G inferInstance S hS b).1.chooseDecomposition
  have : Algebra.FiniteType k (CharacterUnits.Coord G) := Lie.coordinateAlgebraFiniteType G
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := k) (A := CharacterUnits.Coord G)
  let J := Σ f : F, (DirectSum.decompose (weightSpace b) f.val).support
  let z (j : J) : CharacterUnits.Coord G :=
    (DirectSum.decompose (weightSpace b) j.1.val j.2.val).val
  refine ⟨Finset.univ.image z, ?_, ?_⟩
  · rw [← top_le_iff, ← hF, Algebra.adjoin_le_iff]
    intro f hf
    rw [← DirectSum.sum_support_decompose (weightSpace b) f]
    refine sum_mem fun χ hχ => Algebra.subset_adjoin ?_
    exact Finset.mem_image.mpr ⟨⟨⟨f, hf⟩, ⟨χ, hχ⟩⟩, Finset.mem_univ _, rfl⟩
  · intro f hf
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨j.2.val, (DirectSum.decompose (weightSpace b) j.1.val j.2.val).property⟩

/-- A character evaluated along a cocharacter is the corresponding integer power. -/
theorem characterValue_cocharacter {A : Type u} [CommRing A] [Algebra k A]
    (χ : characterLattice S) (ν : cocharacterLattice S)
    (t : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp A) :
    Lie.characterValue χ (t ≫ (CommGroupScheme.groupHom ν).hom.hom) =
      Gm.affinePointsEquiv _ t ^ latticePairing S χ ν := by
  rw [← Lie.characterValue_comp]
  unfold Lie.characterValue
  rw [eq_gmEndEquiv_zsmul k (ν ≫ χ), Gm.comp_zsmul_id, map_zpow]
  rfl

/-- A nonzero selected cocharacter weight vanishes at every fixed affine point. -/
theorem eigenfunction_eq_zero_of_cocharacter_fixed
    (b : AutomorphicAction S.toGrp G) (χ : characterLattice S)
    (ν : cocharacterLattice S) {f : CharacterUnits.Coord G}
    (hf : f ∈ weightSpace b χ) (hχ : latticePairing S χ ν ≠ 0)
    {A : Type u} [CommRing A] [Algebra k A] (x : Lie.AffinePoints G A)
    (hx : (b.restrict (CommGroupScheme.groupHom ν)).IsFixed x) :
    Lie.pointCoordinates G x f = 0 := by
  let C : A →ₐ[k] LaurentPolynomial A := IsScalarTower.toAlgHom k A (LaurentPolynomial A)
  let t : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp (LaurentPolynomial A) :=
    (Gm.affinePointsEquiv _).symm (Gm.relativeCoordUnit A)
  have ht : Gm.affinePointsEquiv _ t = Gm.relativeCoordUnit A :=
    (Gm.affinePointsEquiv _).apply_symm_apply _
  have he := hx _ ((algSpec _).map (CommAlgCat.ofHom C).op) t
  rw [AutomorphicAction.restrict_act] at he
  change b.act (t ≫ (CommGroupScheme.groupHom ν).hom.hom)
    (Lie.affineMap G C x) = Lie.affineMap G C x at he
  have hv := hf (LaurentPolynomial A) (t ≫ (CommGroupScheme.groupHom ν).hom.hom)
    (Lie.affineMap G C x)
  rw [he, Lie.pointCoordinates_naturality, AlgHom.comp_apply,
    characterValue_cocharacter, ht, Gm.relativeCoordUnit_zpow_val] at hv
  change LaurentPolynomial.C (Lie.pointCoordinates G x f) =
    LaurentPolynomial.T (latticePairing S χ ν) *
      LaurentPolynomial.C (Lie.pointCoordinates G x f) at hv
  rw [mul_comm, ← LaurentPolynomial.single_eq_C_mul_T] at hv
  have hc := congrArg (fun p : LaurentPolynomial A => p.coeff (latticePairing S χ ν)) hv
  simpa only [LaurentPolynomial.C_apply, ite_eq_right hχ, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same] using hc.symm

end CoordinateWeights

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A split-torus action on an affine finite-type group has a cocharacter
with the same fixed subgroup on all test schemes. -/
theorem exists_cocharacter_fixedSubgroup (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) :
    ∃ ν : cocharacterLattice S,
      (b.restrict (CommGroupScheme.groupHom ν)).fixedSubgroup = b.fixedSubgroup := by
  classical
  obtain ⟨s, hs, hw⟩ := CoordinateWeights.exists_finset_eigenfunction_generators hS b
  let w (f : s) : characterLattice S := (hw f.val f.property).choose
  let W : Finset (characterLattice S) := (Finset.univ.image w).filter (· ≠ 0)
  obtain ⟨ν, hν⟩ := hS.exists_pairings_ne_zero (W : Set _) W.finite_toSet
    (by intro χ hχ; exact (Finset.mem_filter.mp hχ).2)
  refine ⟨ν, le_antisymm ?_ ?_⟩
  · intro T g hg
    apply b.isFixed_of_affine g
    intro A a t
    have hg' : (b.restrict (CommGroupScheme.groupHom ν)).IsFixed (a ≫ g) :=
      (b.restrict (CommGroupScheme.groupHom ν)).fixedSubgroup.comp_mem a hg
    apply (Lie.pointCoordinates G).injective
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro f hf
    let χ := w ⟨f, hf⟩
    have hfχ : f ∈ CoordinateWeights.weightSpace b χ := (hw f hf).choose_spec
    rw [hfχ A t (a ≫ g)]
    by_cases hzero : χ = 0
    · rw [hzero, Lie.characterValue_zero, Units.val_one, one_mul]
    · have hpair : latticePairing S χ ν ≠ 0 := hν χ
        (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
          ⟨⟨f, hf⟩, Finset.mem_univ _, rfl⟩, hzero⟩)
      rw [CoordinateWeights.eigenfunction_eq_zero_of_cocharacter_fixed b χ ν
        hfχ hpair (a ≫ g) hg', mul_zero]
  · intro T g hg V a t
    rw [restrict_act]
    exact hg V a (t ≫ (CommGroupScheme.groupHom ν).hom.hom)

end AutomorphicAction

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Every split-torus homomorphism into an affine finite-type group admits a
cocharacter whose dynamic centralizer is the whole-torus centralizer. -/
theorem IsSplitTorus.exists_cocharacter_centralizer (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) :
    ∃ ν : cocharacterLattice S,
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i := by
  obtain ⟨ν, hν⟩ := AutomorphicAction.exists_cocharacter_fixedSubgroup hS
    (AutomorphicAction.conjugation i)
  refine ⟨ν, ?_⟩
  simpa only [AutomorphicAction.restrict_conjugation,
    AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer,
    torusCentralizer_gm_eq_dynamicCentralizer] using hν

/-- A cocharacter retaining the actual whole-split-torus centralizer. -/
def centralizingCocharacter (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) :
    cocharacterLattice S :=
  (hS.exists_cocharacter_centralizer i).choose

/-- The chosen cocharacter has exactly the original all-test centralizer. -/
theorem centralizingCocharacter_spec (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) :
    Dynamic.centralizer (CommGroupScheme.groupHom (centralizingCocharacter hS i) ≫ i) =
      torusCentralizer i :=
  (hS.exists_cocharacter_centralizer i).choose_spec

end Langlands.GroupScheme
