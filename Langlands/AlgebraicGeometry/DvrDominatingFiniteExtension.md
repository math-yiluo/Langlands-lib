# A DVR dominating a DVR inside a finite extension of its fraction field

Lean module: `Langlands.AlgebraicGeometry.DvrDominatingFiniteExtension`.

## Definition

`Langlands.AlgebraicGeometry.DvrDominatingFiniteExtension.dominatingValuationSubring R L`
takes a discrete valuation ring `R : Type u` and a finite-dimensional field extension
`L : Type u` of `FractionRing R`, the same inputs as the theorem below. It is a
`ValuationSubring L`. Give `L` the `R`-algebra structure `R → FractionRing R → L`. The
Library lemma
`Langlands.AlgebraicGeometry.NoetherianValuativeCriterion.exists_valuationSubring_dominates`
says that some valuation subring of `L` is a discrete valuation ring, contains the image of
`R`, and dominates `R`. The definition chooses one such subring with `Classical.choose`.

`dominatingValuationSubring_spec R L` records the chosen subring's properties, with the
algebra map written out as `R → FractionRing R → L`:

1. `dominatingValuationSubring R L` is a discrete valuation ring;
2. it contains the image of every `a : R`;
3. `a ∈ maximalIdeal R` if and only if the image of `a` is a nonunit of the subring.

## Statement

`Langlands.AlgebraicGeometry.DvrDominatingFiniteExtension.exists_dvr_of_finite_extension`
takes

- a discrete valuation ring `R : Type u` (`CommRing`, `IsDomain`, `IsDiscreteValuationRing`),
- a field `L : Type u` with an algebra structure over `FractionRing R` that is
  finite-dimensional.

It asserts that there are

- a ring `R' : Type u` in the same universe that is a domain and a discrete valuation ring,
- an `R`-algebra structure on `R'`,
- a ring homomorphism `σ : L →+* FractionRing R'`,

such that

1. `algebraMap R R'` is faithfully flat (`RingHom.FaithfullyFlat`);
2. `Spec.map (CommRingCat.ofHom (algebraMap R R'))` is a flat morphism of schemes;
3. the same morphism is surjective;
4. `σ ∘ (FractionRing R → L) ∘ (R → FractionRing R)` equals
   `(R' → FractionRing R') ∘ (R → R')`, i.e. `σ` is compatible with the two
   structure maps out of `R`.

The existential packages each instance with `letI`, in the same style as the target
statement `Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement`.

## Provenance and purpose

This is an internal helper for Task 7618, the proof of
`Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement`. It supplies the
DVR extension in the route the task context suggests as an alternative to
henselization. First a finite field extension `L` of the fraction field is found that
holds the coefficients of finitely many nilradical generators. Then `R'` is a DVR inside
`L` that dominates `R`, and `b = Spec.map (R → R')` is the flat surjective base change
the target asks for. The mathematical content is the standard Krull–Akizuki-type fact
that a DVR is dominated by a DVR in any finite extension of its fraction field. The
Library already proves this as
`Langlands.AlgebraicGeometry.NoetherianValuativeCriterion.exists_valuationSubring_dominates`.
This module chooses such a subring and repackages it with the flatness, surjectivity and
fraction-field data.

## Proof

1. Give `L` the `R`-algebra structure `R → FractionRing R → L`. Mathlib's
   `IsDiscreteValuationRing.ringKrullDim_eq_one` gives `ringKrullDim R = 1`, so
   `exists_valuationSubring_dominates` (with `A := R`, `K := FractionRing R`) applies.
   The proof takes `V := dominatingValuationSubring R L`, the subring this lemma provides.
   By `dominatingValuationSubring_spec`, `V` is a DVR, contains the image of `R`, and
   satisfies `a ∈ maximalIdeal R ↔ algebraMap R L a ∈ V.nonunits`.
2. Take `R' := V`, with the `R`-algebra structure given by corestricting
   `algebraMap R L` to `V`. It is injective because `R → FractionRing R` and the field
   map `FractionRing R → L` are injective.
3. The map `R → V` is a local homomorphism. If the image of `a` is a unit of `V` but `a`
   is not a unit, then `a` lies in the maximal ideal of `R`. By the domination property
   its image lies in `V.nonunits`, i.e. in the maximal ideal of `V`
   (`ValuationSubring.coe_mem_nonunits_iff`), which is a contradiction.
4. `V` is a torsion-free `R`-module (`Module.IsTorsionFree.of_smul_eq_zero`): `V` is a
   domain and `R → V` is injective. A DVR is a Dedekind domain, so Mathlib's instance
   makes torsion-free modules over it flat. Then
   `Module.FaithfullyFlat.of_flat_of_isLocalHom` gives faithful flatness, and
   `RingHom.faithfullyFlat_algebraMap_iff` turns it into the ring-hom form.
   `flat_and_surjective_SpecMap_iff` then gives that the spectrum map is flat and surjective.
5. `L` is a fraction field of `V` (Mathlib's `IsFractionRing` instance for valuation
   subrings), so `σ` is the ring homomorphism underlying
   `(FractionRing.algEquiv V L).symm : L ≃ₐ[V] FractionRing V`. Compatibility holds because
   this equivalence is `V`-linear (`AlgEquiv.commutes`).
