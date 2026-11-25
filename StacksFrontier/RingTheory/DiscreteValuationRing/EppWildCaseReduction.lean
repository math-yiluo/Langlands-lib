module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppUnramifiedBaseChange
public import StacksFrontier.RingTheory.Henselian.Criteria
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Epp's unramified base change without a perfect residue field

Let `A → B` be a local homomorphism of discrete valuation rings satisfying Epp's condition
`Stacks.EppTheorem.EppCondition`. This file replaces the perfect core of `κ_B`, which is an
intermediate field of `κ_B / κ_A` only when `κ_A` is perfect, by the compositum
`κ_A(perfectCore κ_B p)`, and constructs the finite weakly unramified base change of `A` whose
residue field is this compositum, with no perfectness hypothesis on `κ_A`. It also shows that the
henselian hypothesis on `B` needed to embed the base change into `B` is supplied by completeness,
and that the base change is separable over the fraction field of `A`.

## Main definitions

* `perfectCoreCompositum K L p`: the compositum `K(perfectCore L p)` inside `L`, as an
  intermediate field of `L / K`.

## Main results

* `isSeparable_perfectCoreCompositum_iff`: the compositum is separable over `K` if and only if
  every element of the perfect core of `L` is separable over `K`.
* `perfectCoreCompositum_eq_perfectCoreIntermediateField`: over a perfect base the compositum is
  the perfect core.
* `Stacks.EppTheorem.exists_isWeaklyUnramified_residueField_algEquiv`: a finite weakly unramified
  extension of a discrete valuation ring realising a prescribed finite separable residue
  extension.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_residueField_algEquiv_compositum`: the
  finite weakly unramified base change with residue field the compositum.
* `Stacks.EppTheorem.exists_isWeaklyUnramified_residueField_algHom_fieldRange_eq`: the
  residue-field embedding with prescribed image.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum`:
  for a henselian `B`, the base change embeds into `B` with residue field mapped onto the
  compositum.
* `EppCondition.exists_isWeaklyUnramified_algebraMap_fieldRange_eq_compositum_of_complete`
  (namespace `Stacks.EppTheorem`): the same with `B` complete instead of henselian.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algHom_of_completion`: the base change
  embeds into a complete extension of `B` with the same residue field.
* `AdjoinRoot.separable_map_algebraMap_of_separable_map_residue`: a monic polynomial over a
  discrete valuation ring with separable irreducible reduction is separable over the fraction
  field.
* `AdjoinRoot.isSeparable_of_separable`: `K[X] ⧸ (q)` is separable over `K` for `q` monic,
  irreducible and separable.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09EJ](https://stacks.math.columbia.edu/tag/09EJ)
-/

@[expose] public section

open IsLocalRing Polynomial

/-! ### The compositum of the base field with the perfect core -/

section Compositum

variable (K L : Type*) [Field K] [Field L] [Algebra K L] (p : ℕ) [ExpChar L p]

variable {K L p}

end Compositum

/-! ### Epp's condition and the compositum -/

namespace Stacks.EppTheorem

section EppConditionCompositum

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]

end EppConditionCompositum

end Stacks.EppTheorem

/-! ### The finite unramified base change, for an arbitrary finite separable residue extension -/

namespace Stacks.EppTheorem

universe u v w

/-- Let `A` be a discrete valuation ring and let `E / κ_A` be a finite separable extension of its
residue field. Then there is a discrete valuation ring `A₁`, finite as an `A`-module, with
`A₁ / A` an extension of discrete valuation rings which is weakly unramified (`e = 1`), whose
residue field is `κ_A`-isomorphic to `E`. -/
theorem exists_isWeaklyUnramified_residueField_algEquiv {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (E : Type w) [Field E] [Algebra (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] [FiniteDimensional (ResidueField A) E] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        Nonempty (ResidueField A₁ ≃ₐ[ResidueField A] E) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) E
  have hint : IsIntegral (ResidueField A) α := IsIntegral.of_finite (ResidueField A) α
  obtain ⟨P, hP, hPmap⟩ := exists_monic_lift_map_residue_eq A (minpoly.monic hint)
  have hirr : Irreducible (P.map (residue A)) := hPmap ▸ minpoly.irreducible hint
  have hd : 0 < P.natDegree :=
    hP.natDegree_map (residue A) ▸ hPmap ▸ minpoly.natDegree_pos hint
  have hdeg := Polynomial.natDegree_pos_iff_degree_pos.mp hd
  have hlocal := AdjoinRoot.isLocalRing_of_irreducible_map_residue hP hirr
  have hdom := AdjoinRoot.isDomain_of_irreducible_map_residue hP hirr
  have hdvr := AdjoinRoot.isDiscreteValuationRing hP hirr hd
  have hext : IsDiscreteValuationRing.IsExtension A (AdjoinRoot P) :=
    { toFaithfulSMul := AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hP hdeg
      toIsLocalHom := AdjoinRoot.isLocalHom_of_monic_of_degree_pos (g := P) hP hdeg }
  exact ⟨AdjoinRoot P, inferInstance, hdom, hdvr, inferInstance, hP.finite_adjoinRoot, hext,
    AdjoinRoot.ramificationIdx_eq_one hP hirr hd,
    ⟨(AdjoinRoot.residueFieldAlgEquiv hP hirr hd).symm.trans
      ((AdjoinRoot.algEquivOfEq (ResidueField A) _ _ hPmap).trans
        (AdjoinRoot.algEquivOfPrimitiveElement hint hα))⟩⟩

end Stacks.EppTheorem

/-! ### The embedding into a henselian `B`, and its image -/

namespace Stacks.EppTheorem

universe u v w

end Stacks.EppTheorem

/-! ### Completeness supplies the henselian hypothesis -/

namespace Stacks.EppTheorem

universe u v w

section Completion

variable {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A] [IsLocalRing B]
  [IsLocalRing B'] [Algebra A B] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
  [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B B')] [IsLocalHom (algebraMap A B')]

end Completion

end Stacks.EppTheorem

/-! ### The base change is separable over the fraction field -/

namespace AdjoinRoot

end AdjoinRoot
