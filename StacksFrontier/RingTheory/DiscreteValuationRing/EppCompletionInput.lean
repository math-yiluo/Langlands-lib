module

public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWildCaseReduction
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.Krasner
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The completion of a discrete valuation ring, as input to the descent

The third step of the Stacks proof of Epp's theorem (Tag 09F9) reduces the existence of a weak
solution to the case of *complete* discrete valuation rings, and
`StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionDescent` supplies the transport back
down. Both halves of that step are stated over an abstract square
`A → A^`, `B → B^`, with completeness appearing only through hypotheses, so that neither half has
to know how `A^` is built.

This file discharges those hypotheses for the intended `A^`, namely
`AdicCompletion (maximalIdeal A) A`. Each fact is either a Mathlib instance or an existing theorem,
put in the one shape the descent's callers need, so that no statement carries a completeness or
henselian hypothesis that the completion already provides.

## Main results

* `IsDiscreteValuationRing.exists_isDomain_isDiscreteValuationRing_adicCompletion`: the completion
  of a discrete valuation ring is again one. This is the forward half of Tag 0AP1.
* `IsDiscreteValuationRing.ringKrullDim_adicCompletion_eq_one`: it has Krull dimension one.
* `IsDiscreteValuationRing.henselianLocalRing_adicCompletion`: **it is henselian, with no
  hypothesis at all.** Mathlib makes the completion of a Noetherian local ring local and adically
  complete by instance, and a complete local ring is henselian local by
  `henselianLocalRing_of_isAdicComplete_maximalIdeal`.
* `IsDiscreteValuationRing.exists_finite_separable_extension_tensorProduct_equiv_of_isDVR`: **Tag
  09EJ with its two completion hypotheses discharged.** The published statement asks for
  `[IsDomain (AdicCompletion (maximalIdeal A) A)]` and `ringKrullDim ... = 1` as hypotheses; for a
  discrete valuation ring both are theorems, so a caller in that situation supplies neither.
* `isDomain_adicCompletion`, `isDiscreteValuationRing_adicCompletion`,
  `faithfulSMul_adicCompletion`, `isExtension_adicCompletion`: the same facts as **instances**,
  pulled out of Tag 0AP1's existential by `Exists.elim` — legitimate because both are `Prop`s.
  This is what makes `FractionRing` of the completion available at all.
* `IsDiscreteValuationRing.AdicCompletionFractionField`,
  `isScalarTower_adicCompletionFractionField` and
  `exists_algebra_isScalarTower_adicCompletionFractionField`: **a canonical fraction field for
  `A^`, with the `K`-algebra structure and the tower `A → K → K^`.** Tag 09EJ manufactures its
  own `Algebra K K^` inside a statement-level `letI`, which is definitionally this one, so its
  conclusion is accepted against this instance with no transport.
* `IsDiscreteValuationRing.ramificationIdx_adicCompletion_eq_one` and
  `isWeaklyUnramified_adicCompletion`: **`A → A^` is weakly unramified.** A uniformizer of `A`
  stays a uniformizer of `A^` (`irreducible_algebraMap_adicCompletion`), and that valuation *is*
  the ramification index.
* `IsDiscreteValuationRing.isSeparableExtension_residueField_adicCompletion` and
  `formallySmoothNAdic_algebraMap_adicCompletion`: **`A → A^` is formally smooth in the adic
  sense**, by Tag 09E7 from the previous two. This is the hypothesis `hformal` of Tag 09EQ.

## The completion of `B`

That `AdicCompletion (maximalIdeal B) B` is a discrete valuation ring with residue field `κ_B` has
two halves: the ring-theory half is `isDiscreteValuationRing_iff_adicCompletion_maximalIdeal`
(`AdicCompletion/PermanenceOfProperties.lean`, tagged `0AP1`), and the residue-field half is
Mathlib's `AdicCompletion.residueField_map_bijective`. The three theorems above package the first
and `exists_isWeaklyUnramified_algHom_of_adicCompletion` below consumes the second, so the
henselian hypothesis of the per-factor package is discharged outright rather than traded for
completeness of `B`.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09EJ](https://stacks.math.columbia.edu/tag/09EJ)
* [The Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing

section Completion

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- **The completion of a discrete valuation ring is a discrete valuation ring.**

The forward half of Tag 0AP1, with the domain instance carried alongside because
`IsDiscreteValuationRing` does not imply it. -/
theorem exists_isDomain_isDiscreteValuationRing_adicCompletion :
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal A) A),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal A) A) :=
  isDiscreteValuationRing_iff_adicCompletion_maximalIdeal.mp ⟨inferInstance, inferInstance⟩

/-- The completion of a discrete valuation ring has Krull dimension one.

This is the second of the two hypotheses Tag 09EJ asks for, and it is what
`ringKrullDim_adicCompletion_maximalIdeal` gives once the base is known to have dimension one. -/
theorem ringKrullDim_adicCompletion_eq_one :
    ringKrullDim (AdicCompletion (maximalIdeal A) A) = 1 :=
  (ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm.trans (ringKrullDim_eq_one A)

/-! ### The completion as an extension, with instances

`exists_isDomain_isDiscreteValuationRing_adicCompletion` delivers its two facts inside an
existential, because Tag 0AP1 is stated as an `iff` between existentials. Both of them are
`Prop`s, so they can be pulled out by `Exists.elim` and registered as instances, which is what the
rest of this file and the descent need: with them in place `AdicCompletion (maximalIdeal A) A` is a
discrete valuation ring to instance search, so `FractionRing` of it is available and no caller has
to destructure anything. -/

/-- The `maximalIdeal A`-adic completion of a discrete valuation ring `A` is a domain. -/
instance isDomain_adicCompletion : IsDomain (AdicCompletion (maximalIdeal A) A) :=
  Exists.elim (exists_isDomain_isDiscreteValuationRing_adicCompletion A) fun h _ => h

/-- The `maximalIdeal A`-adic completion of a discrete valuation ring `A` is a discrete valuation
ring. -/
instance isDiscreteValuationRing_adicCompletion :
    IsDiscreteValuationRing (AdicCompletion (maximalIdeal A) A) :=
  Exists.elim (exists_isDomain_isDiscreteValuationRing_adicCompletion A) fun _ h => h

/-- `A` acts faithfully on its `maximalIdeal A`-adic completion: the map `A → A^` is injective. -/
instance faithfulSMul_adicCompletion : FaithfulSMul A (AdicCompletion (maximalIdeal A) A) :=
  (faithfulSMul_iff_algebraMap_injective A (AdicCompletion (maximalIdeal A) A)).mpr
    (AdicCompletion.of_injective (maximalIdeal A) A)

/-- The map from `A` to its `maximalIdeal A`-adic completion is an extension of discrete valuation
rings. -/
instance isExtension_adicCompletion : IsExtension A (AdicCompletion (maximalIdeal A) A) := ⟨⟩

/-- **A uniformizer of `A` stays a uniformizer in `A^`.**

`AdicCompletion.maximalIdeal_eq_map` says the maximal ideal of the completion is the image of the
maximal ideal, and the image of a span is the span of the image. -/
theorem irreducible_algebraMap_adicCompletion {π : A} (hπ : Irreducible π) :
    Irreducible (algebraMap A (AdicCompletion (maximalIdeal A) A) π) := by
  refine (irreducible_iff_uniformizer _).mpr ?_
  rw [AdicCompletion.maximalIdeal_eq_map, (irreducible_iff_uniformizer π).mp hπ, Ideal.map_span]
  simp

/-- **`A → A^` is weakly unramified**: its ramification index is one.

This is the ramification-theoretic content of completion, and the reason the weak solution for
`A → A^` below is available at all. A uniformizer of `A` maps to a uniformizer of `A^`, so the
valuation of its image is one, and that valuation *is* the ramification index. -/
theorem ramificationIdx_adicCompletion_eq_one :
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx A (AdicCompletion (maximalIdeal A) A)
      = 1 := by
  obtain ⟨π, hπprime⟩ := exists_prime A
  have hπ : Irreducible π := hπprime.irreducible
  have h := Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx A
    (AdicCompletion (maximalIdeal A) A) π hπ
  rw [addVal_uniformizer (irreducible_algebraMap_adicCompletion A hπ)] at h
  exact_mod_cast h.symm

/-- `A → A^` is weakly unramified, in the named form. -/
theorem isWeaklyUnramified_adicCompletion :
    IsWeaklyUnramified A (AdicCompletion (maximalIdeal A) A) :=
  ramificationIdx_adicCompletion_eq_one A

end Completion

section FractionField

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- **The canonical fraction field of the completion of a discrete valuation ring.**

Available only because `isDomain_adicCompletion` and `isDiscreteValuationRing_adicCompletion` are
instances: `FractionRing` needs a domain. Tag 09EJ manufactures its own `Algebra K Kc` inside a
statement-level `letI`; that one is definitionally the `algebraAdicCompletionFractionField` below,
so a caller may use either; this is the canonical choice, and the one to hand the descent.

The `A`-algebra structure on it is *already* an instance, from `Algebra A A^` composed with
`Algebra A^ (FractionRing A^)`, so it is deliberately not redeclared here. -/
abbrev AdicCompletionFractionField : Type _ :=
  FractionRing (AdicCompletion (maximalIdeal A) A)

/-- `A → K^` is injective: it is `A → A^` followed by `A^ → Frac A^`, and both are. -/
theorem injective_algebraMap_adicCompletionFractionField :
    Function.Injective (algebraMap A (AdicCompletionFractionField A)) := by
  rw [IsScalarTower.algebraMap_eq A (AdicCompletion (maximalIdeal A) A)
    (AdicCompletionFractionField A)]
  exact (IsFractionRing.injective (AdicCompletion (maximalIdeal A) A)
    (AdicCompletionFractionField A)).comp (AdicCompletion.of_injective (maximalIdeal A) A)

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- **The structure map `K → K^`.**

`K` is *a* fraction field of `A` and `K^` is the canonical one of `A^`; since `A → K^` is injective
and `K^` is a field, the map extends uniquely to `K`. This is not declared an instance: `K` is
arbitrary among fraction fields of `A`, so an instance would fire on unrelated fields. A caller
introduces it with `letI` — `exists_algebra_isScalarTower_adicCompletionFractionField` below
packages it with the tower, which is the form the descent consumes. -/
@[instance_reducible]
noncomputable def algebraAdicCompletionFractionField : Algebra K (AdicCompletionFractionField A) :=
  (IsFractionRing.lift (A := A) (K := K) (L := AdicCompletionFractionField A)
    (g := algebraMap A (AdicCompletionFractionField A))
    (injective_algebraMap_adicCompletionFractionField A)).toAlgebra

/-- **The tower `A → K → K^`.**

`K → K^` was built as the unique extension of `A → K^` along `A → K`, so the composite
`A → K → K^` is `A → K^` by `IsFractionRing.lift_algebraMap`. This is the form a caller that has
already introduced `algebraAdicCompletionFractionField` with `letI` needs; the existential below
packages the two together for a caller that has not. -/
theorem isScalarTower_adicCompletionFractionField :
    letI := algebraAdicCompletionFractionField A K
    IsScalarTower A K (AdicCompletionFractionField A) := by
  let _ := algebraAdicCompletionFractionField A K
  exact IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (A := A) (K := K)
      (injective_algebraMap_adicCompletionFractionField A) a).symm

end FractionField

section ResidueField

variable (B : Type*) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]

/-- The structure map on residue fields induced by `B → B^` **is** `ResidueField.map` of that map.

Both sides agree after `residue`, which is surjective. Mathlib states the bijectivity below for
`ResidueField.map`, and this identifies it with `algebraMap` between the two residue fields. -/
theorem algebraMap_residueField_adicCompletion_eq_map :
    (algebraMap (ResidueField B) (ResidueField (AdicCompletion (maximalIdeal B) B))) =
      ResidueField.map (algebraMap B (AdicCompletion (maximalIdeal B) B)) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨b, rfl⟩ := residue_surjective y
  rw [ResidueField.algebraMap_residue]
  exact (RingHom.congr_fun (ResidueField.map_comp_residue
    (algebraMap B (AdicCompletion (maximalIdeal B) B))) b).symm

/-- **Completion does not change the residue field**, in the form the per-factor package consumes.

This is Mathlib's `AdicCompletion.residueField_map_bijective` transported across
`algebraMap_residueField_adicCompletion_eq_map`, and surjectivity is exactly the hypothesis `hsurj`
of `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algHom_of_completion` — so passing to
the completion of `B` costs nothing on the residue side. -/
theorem surjective_algebraMap_residueField_adicCompletion :
    Function.Surjective
      (algebraMap (ResidueField B) (ResidueField (AdicCompletion (maximalIdeal B) B))) := by
  rw [algebraMap_residueField_adicCompletion_eq_map]
  exact (AdicCompletion.residueField_map_bijective B).surjective

/-- The exponential characteristic of the residue field is unchanged by completion.

A map of fields is injective, so this needs nothing about the completion beyond the algebra
structure; it is recorded because the per-factor package asks for `ExpChar` on both residue
fields separately. -/
theorem expChar_residueField_adicCompletion (p : ℕ) [ExpChar (ResidueField B) p] :
    ExpChar (ResidueField (AdicCompletion (maximalIdeal B) B)) p :=
  expChar_of_injective_algebraMap
    (algebraMap (ResidueField B)
      (ResidueField (AdicCompletion (maximalIdeal B) B))).injective p

end ResidueField

section FormallySmooth

universe u

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- **The residue extension of `A → A^` is separable**, because it is an isomorphism.

`surjective_algebraMap_residueField_adicCompletion` plus injectivity of a map of fields makes
`κ_A → κ_{A^}` bijective, so the extension is formally smooth by transport along the equivalence,
and formal smoothness of a field extension is separability. -/
theorem isSeparableExtension_residueField_adicCompletion :
    Algebra.StacksIsSeparableExtension (ResidueField A)
      (ResidueField (AdicCompletion (maximalIdeal A) A)) := by
  have hbij : Function.Bijective
      (algebraMap (ResidueField A) (ResidueField (AdicCompletion (maximalIdeal A) A))) :=
    ⟨(algebraMap (ResidueField A)
        (ResidueField (AdicCompletion (maximalIdeal A) A))).injective,
      surjective_algebraMap_residueField_adicCompletion A⟩
  have hfs : Algebra.FormallySmooth (ResidueField A)
      (ResidueField (AdicCompletion (maximalIdeal A) A)) :=
    Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective
      (Algebra.ofId (ResidueField A)
        (ResidueField (AdicCompletion (maximalIdeal A) A))) hbij)
  exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mp hfs

/-- **`A → A^` is formally smooth in the adic sense.**

This is Tag 09E7 applied to the completion: formal smoothness of an extension of discrete valuation
rings is exactly weak unramifiedness together with separability of the residue extension, and for
`A → A^` both hold — the first by `isWeaklyUnramified_adicCompletion`, the second because the
residue extension is an isomorphism.

This is the hypothesis `hformal` of Tag 09EQ
(`formallySmooth_localizations_after_finite_fraction_field_extension`), and therefore the input
from which the weak solution for `A → A^` along an arbitrary finite `K₁ / K` follows: 09EQ
propagates formal smoothness to the localizations of the base-changed closures, and Tag 09E7 read
backwards turns that into ramification index one at each maximal ideal, which is the definition of
a weak solution. -/
theorem formallySmoothNAdic_algebraMap_adicCompletion :
    RingHom.FormallySmoothNAdic.{u} (algebraMap A (AdicCompletion (maximalIdeal A) A))
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) :=
  (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A
      (AdicCompletion (maximalIdeal A) A)).mpr
    ⟨isWeaklyUnramified_adicCompletion A, isSeparableExtension_residueField_adicCompletion A⟩

end FormallySmooth

/-- **Tag 09EJ for a discrete valuation ring**: a finite separable extension of the fraction field
of the completion comes from one of the fraction field of the base.

This is `exists_finite_separable_extension_tensorProduct_equiv` with both of its completion
hypotheses discharged. That statement asks for `[IsDomain (AdicCompletion (maximalIdeal A) A)]` and
`ringKrullDim (AdicCompletion (maximalIdeal A) A) = 1`; for a discrete valuation ring these are
`exists_isDomain_isDiscreteValuationRing_adicCompletion` and
`ringKrullDim_adicCompletion_eq_one`, so a caller supplies neither.

This is the form in which the completion descent needs Tag 09EJ: the descent is handed a weak
solution `M / K^` upstairs and has to produce the finite extension `K₁ / K` downstairs whose base
change to `K^` is `M`, and it has no completeness hypothesis of its own to pay with. -/
theorem exists_finite_separable_extension_tensorProduct_equiv_of_isDVR
    {A K Khat M : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field Khat]
    [Algebra (AdicCompletion (maximalIdeal A) A) Khat]
    [IsFractionRing (AdicCompletion (maximalIdeal A) A) Khat]
    [Field M] [Algebra Khat M] [FiniteDimensional Khat M]
    [Algebra.IsSeparable Khat M] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    letI : Algebra A Khat :=
      ((algebraMap Ahat Khat).comp (algebraMap A Ahat)).toAlgebra
    letI : Algebra K Khat :=
      (IsFractionRing.lift (A := A) (K := K) (L := Khat) (g := algebraMap A Khat)
        ((IsFractionRing.injective Ahat Khat).comp
          (by
            dsimp only [Ahat]
            exact AdicCompletion.of_injective (maximalIdeal A) A))).toAlgebra
    ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        Nonempty (TensorProduct K Khat L ≃ₐ[Khat] M) := by
  exact Krasner.exists_finite_separable_extension_tensorProduct_equiv
    (ringKrullDim_adicCompletion_eq_one A)

end IsDiscreteValuationRing

namespace Stacks.EppTheorem

universe u v

open IsLocalRing

end Stacks.EppTheorem
