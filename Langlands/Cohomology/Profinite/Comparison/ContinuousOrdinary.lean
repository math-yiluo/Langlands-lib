import Langlands.Cohomology.Continuous.CochainComparisonLawsProof
import Langlands.Cohomology.Profinite.Comparison.Continuous
import Langlands.Cohomology.Profinite.Comparison.Discrete

/-!
# The two comparisons with Mathlib's continuous cohomology agree on cocycles

For a topological group `G` and a discrete topological representation `X`, there are two maps out of
Mathlib's continuous cohomology `continuousCohomology n X` (homogeneous continuous cochains):

* the foundations' isomorphism `isoContinuousCohomology X n` from the cochain model
  `cohomology (underlyingRep X) n` (locally constant inhomogeneous cochains), whose inverse sends a
  homogeneous cochain `σ` to `g ↦ σ (1, g₁, g₁g₂, …)`;
* the Library's comparison `Langlands.Continuous.continuousToOrdinary X n` to the cohomology of the
  abstract group `groupCohomology (Rep.of X.ρ.toRepresentation) n`, which evaluates a homogeneous
  cochain at the same tuple of partial products.

`isoContinuousCohomology_hom_comp_continuousToOrdinary` says that the composite is the map
`toGroupCohomology` induced by the inclusion of locally constant cochains into all cochains: on a
cocycle it does nothing. For a discrete group (`isoGroupCohomology`) this identifies the inverse of
the Library's comparison with the foundations' isomorphisms
(`isoContinuousCohomology_hom_continuousToOrdinary_inv`).
-/

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory TopRep

universe u

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The Library's evaluation of nested continuous cochains is the foundations' `nestedHomeomorph`
(the two are defined by the same recursion). -/
theorem nestedEval_eq_nestedHomeomorph (X : TopRep.{u} k G) (m : ℕ) (a : resolutionX X m)
    (x : Fin m → G) :
    Continuous.nestedEval X m a x = nestedHomeomorph X m a x := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _ _

variable (X : TopRep.{u} k G) [DiscreteTopology X] [IsSmoothRep (underlyingRep X)]

/-- On cochains, the foundations' comparison followed by the Library's comparison is the identity
on the underlying function of a locally constant cochain. -/
theorem continuousToOrdinaryCochains_homogeneousEquiv (n : ℕ)
    (φ : locallyConstantCochains (underlyingRep X) n) (x : Fin n → G) :
    ((Continuous.continuousToOrdinaryCochains X).f n).hom (homogeneousEquiv X n φ) x = φ.1 x := by
  rw [Continuous.continuousToOrdinaryCochains_apply, nestedEval_eq_nestedHomeomorph]
  change nestedHomeomorph X (n + 1) (ofInhomogeneous X n φ).1 (Fin.partialProd x) = _
  rw [nestedHomeomorph_ofInhomogeneous]
  simp only [homogeneousFun, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
  rfl

/-- On cochains, the foundations' comparison followed by the Library's comparison is the inclusion
of locally constant cochains into all inhomogeneous cochains. -/
theorem cochainsIsoHomogeneousCochains_hom_comp_continuousToOrdinaryCochains :
    (cochainsIsoHomogeneousCochains X).hom ≫ Continuous.continuousToOrdinaryCochains X =
      cochainsι (underlyingRep X) := by
  ext n φ : 3
  funext x
  exact continuousToOrdinaryCochains_homogeneousEquiv X n φ x

/-- The foundations' isomorphism with continuous cohomology followed by the Library's comparison
with the cohomology of the abstract group is `toGroupCohomology`. -/
theorem isoContinuousCohomology_hom_comp_continuousToOrdinary (n : ℕ) :
    (isoContinuousCohomology X n).hom ≫ Continuous.continuousToOrdinary X n =
      toGroupCohomology (underlyingRep X) n := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (cochainsIsoHomogeneousCochains_hom_comp_continuousToOrdinaryCochains X)
  simp only [HomologicalComplex.homologyMap_comp] at h
  let F := forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)
  let B : ((homogeneousCochains X).sc n |>.map F).homology ≅ F.obj (continuousCohomology n X) :=
    ((homogeneousCochains X).sc n).mapHomologyIso F
  let M : cohomology (underlyingRep X) n ⟶ ((homogeneousCochains X).sc n |>.map F).homology :=
    HomologicalComplex.homologyMap (cochainsIsoHomogeneousCochains X).hom n
  let C : ((homogeneousCochains X).sc n |>.map F).homology ⟶
      groupCohomology (Rep.of X.ρ.toRepresentation) n :=
    HomologicalComplex.homologyMap (Continuous.continuousToOrdinaryCochains X) n
  have e1 : (isoContinuousCohomology X n).hom = M ≫ B.hom := rfl
  have e2 : Continuous.continuousToOrdinary X n = B.inv ≫ C := rfl
  have e3 : M ≫ C = toGroupCohomology (underlyingRep X) n := h
  rw [e1, e2, Category.assoc, Iso.hom_inv_id_assoc, e3]

theorem continuousToOrdinary_isoContinuousCohomology_hom_apply (n : ℕ)
    (x : cohomology (underlyingRep X) n) :
    (Continuous.continuousToOrdinary X n).hom ((isoContinuousCohomology X n).hom.hom x) =
      (toGroupCohomology (underlyingRep X) n).hom x :=
  congrArg (fun f => f.hom x) (isoContinuousCohomology_hom_comp_continuousToOrdinary X n)

/-- For a discrete group the Library's comparison is invertible, and its inverse is the
foundations' isomorphism with continuous cohomology after `isoGroupCohomology⁻¹`. -/
theorem isoContinuousCohomology_hom_continuousToOrdinary_inv [DiscreteTopology G] (n : ℕ)
    (y : groupCohomology (underlyingRep X) n) :
    haveI := Continuous.continuousToOrdinary_isIso X n
    (inv (Continuous.continuousToOrdinary X n)).hom y =
      (isoContinuousCohomology X n).hom.hom ((isoGroupCohomology (underlyingRep X) n).inv.hom y) := by
  have := Continuous.continuousToOrdinary_isIso X n
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback
    (Continuous.continuousToOrdinary X n))
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply,
    continuousToOrdinary_isoContinuousCohomology_hom_apply, ← isoGroupCohomology_hom,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

end Langlands.ProfiniteCohomology
