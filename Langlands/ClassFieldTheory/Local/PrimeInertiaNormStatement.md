# Prime-degree norm surjectivity over the actual inertia fixed field

`Langlands.LocalClassField.PrimeNormOverInertiaFixedField.{u}` is a
`Prop`-valued definition. This module states the target and does not
prove it. It also proves one generic algebraic theorem,
`Langlands.LocalClassField.finiteDimensional_sup_left`, which the
statement uses to install finite dimensionality.

## Exact statement

For every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{u} p`,
and every `D : FiniteIntermediateExtension F.Carrier` with
`[IsGalois F.Carrier D.field]`, put
`ell := Module.finrank F.Carrier D.field` and assume

1. `Nat.Prime ell`, and
2. `(D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
   ell * F.canonicalTopologicalData.ramificationIndex`.

Put

```lean
U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
V := U ⊔ D.field
```

with the `U`-algebra structure `(IntermediateField.inclusion le_sup_left).toAlgebra`
on `V` and the finite-dimensionality instance
`finiteDimensional_sup_left U D.field`. The conclusion is

```lean
Function.Surjective (normUnits U V)
```

That is, every nonzero element of `U` is the determinant norm of some
nonzero element of `V`. These are all the quantified data and
hypotheses. The universe `u` is arbitrary.

## Constructions

- `D.field` is an actual intermediate field of
  `AlgebraicClosure F.Carrier / F.Carrier` with its packaged finite
  dimensionality certificate. `D.asPadicField (p := p)` repackages the same
  field as a p-adic field, with scalar map from `Q_p` through `F.Carrier`.
  No new field operations or valuation data are introduced.
- Hypothesis 2 is the p-adic encoding of total ramification of `D/F`:
  both sides are canonical absolute ramification indices, and
  `v_D(p) = e(D/F) * v_F(p)`. With `[D : F] = ell` it says `e(D/F) = ell`.
  This is a derived encoding choice, not literal notation in Serre. A
  finite Galois extension of prime degree is cyclic, so no separate
  cyclicity certificate is assumed.
- `U` is the intermediate field of the same algebraic closure fixed
  pointwise by the existing absolute inertia subgroup
  `F.absoluteInertia F.canonicalTopologicalData`, the kernel of the
  residue action defined from the canonical topological data of `F`. No
  separately chosen or postulated maximal unramified field occurs.
- `V` is the literal supremum `U ⊔ D.field` in the lattice of intermediate
  fields of that closure. Its `U`-algebra structure is the inclusion
  `U ≤ U ⊔ D.field`, so `algebraMap U V` sends `u` to `u` itself.
- `normUnits U V`, from `Langlands.ClassFieldTheory.Local.Norms`, is
  `Units.map (Algebra.norm U)` on the full multiplicative groups `Vˣ → Uˣ`.
  It is not restricted to valuation-ring units, and elements of nonzero
  valuation are included.

## Finite dimensionality

`finiteDimensional_sup_left` states, for any field extension `L/K`,
intermediate fields `E` and `D` with `D` finite-dimensional over `K`,
that `E ⊔ D` is finite-dimensional over `E` for the inclusion algebra.
Its proof bounds the rank of `IntermediateField.adjoin E D` over `E` by the
rank of `D` over `K` (`IntermediateField.adjoin_rank_le_of_isAlgebraic_right`),
identifies the restriction of scalars of that adjunction with `E ⊔ D`
(`IntermediateField.restrictScalars_adjoin_eq_sup` and
`IntermediateField.adjoin_self`), and transports finite dimensionality along
the resulting identity-on-elements `E`-linear equivalence. The statement uses
this proved instance; finite dimensionality is neither an outer hypothesis
nor part of an opaque certificate. As `FiniteDimensional` is a proposition,
`normUnits U V` does not depend on which proof is supplied.

No linear disjointness of `U` and `D.field`, norm equation, alternative
maximal unramified extension, or arithmetic or cohomological proposition
is assumed.

## Original source and derived formulation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979, registered as
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
PDF page numbers count from one.

- Chapter V, section 4, setup, printed page 87 / PDF page 94: `K` complete
  under a discrete valuation with perfect residue field, `L/K` finite and
  totally ramified, and the base change `L' = L ⊗_K K'` along an unramified
  extension `K'/K`.
- Proposition 6 and its proof, printed page 88 / PDF page 95: for `L/K`
  cyclic of prime degree `l` and `x ∈ K^*`, some extension `K'/K` of
  degree at most `l` makes `x` a norm from `L'/K'`.
- The corollary `N(L_nr^*) = K_nr^*` and its proof, printed pages 88–89 /
  PDF pages 95–96. Serre notes that `L_nr = L ⊗_K K_nr`. The proof places
  `x ∈ K_nr^*` in a finite unramified `K_0/K` and applies Proposition 6
  to `L_0/K_0`.

This target is the corollary in the actual-inertia-fixed-field form.
Serre's `K`, `L` and `K_nr` correspond to `F.Carrier`, `D.field` and `U`.
His `L_nr` corresponds to the literal compositum `V = U ⊔ D.field`, and his
norm `L_nr^* → K_nr^*` to `normUnits U V`. The residue field of a p-adic
field is finite, hence perfect, as Serre requires. Identifying `K_nr` with
`U`, writing `L_nr` as a compositum in the chosen algebraic closure, and
expressing total ramification through canonical indices are derived
choices, not literal statements of the source. The subsequent Lemmas 6–7
and Proposition 7 (printed pages 89–90 / PDF pages 96–97) are distinct
assertions and are not stated here.

## Finite-stage passage

The intended proof follows the corollary. Given `x : Uˣ`:

1. Place `x` in a finite unramified Galois `K/F` inside `U`, using the
   finite unramified exhaustion of `U`.
2. Show that the compositum `D K` remains a totally ramified Galois
   extension of `K` of prime degree `ell`.
3. Apply the bounded prime norm theorem over the base `K` to `x`. This
   gives a finite unramified `K'/K` of degree at most `ell` and
   `y ∈ (D K')^*` whose norm to `K'` is `x`.
4. Show that `K'` is unramified over `F` and therefore contained in `U`,
   using the containment direction of the exhaustion and the fixed-field
   comparison.
5. Transport the norm equation from `D K' / K'` to `V/U`. This needs
   linear disjointness of `D K'` and `U` over `K'`, compatibility of all
   scalar structures with the inclusion algebra on `V`, and the identity
   `V = U ⊔ D K'`.

Applying the finite-base theorem once over `F` handles only elements of
`F`, not all elements of `U`. The base change in step 3 must be over a
finite stage depending on `x`.

## Missing arithmetic prerequisites

This file supplies none of the following. A proof needs:

- The bounded prime norm theorem over an arbitrary p-adic base field.
  The published target
  `Langlands.LocalClassField.PrimeNormAfterUnramifiedBaseChange` states it,
  and its proof is separate work.
- The exhaustion of `U` by finite unramified Galois subextensions and
  their containment in `U`. The published target
  `Langlands.PadicField.InertiaFixedFieldUnramifiedExhaustion` states this.
- Preservation of total ramification, prime degree and the Galois property
  under finite unramified base change. This includes linear disjointness
  of totally ramified and unramified extensions and the behaviour of
  canonical ramification indices in the compositum.
- Linear disjointness of `D.field` from the infinite field `U` over `F`,
  or of the finite-stage extension from `U` over that stage. Two published
  targets are related but do not state this. The first is
  `Langlands.PadicField.InertiaFixedFieldBaseChange`: the inertia fixed
  field of a finite extension is generated over it by the transported `U`.
  The second is `Langlands.PadicField.InertiaDisjointTotallyRamified`, the
  converse implication from linear disjointness with `U` to total
  ramification.
- Norm transport across the base change, for example via
  `Subalgebra.LinearDisjoint.norm_algebraMap` (whose left base may be
  infinite), `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right`,
  `Algebra.norm_eq_of_equiv_equiv` and `Units.ext`.

The statements of these published targets are not proofs of them. A
separate finite-compositum statement task (`7ef970ee-f3a3-4328-9aea-62e67c0ff666`,
proposed target `Langlands.LocalClassField.TotalUnramifiedCompositum`)
treats finite composita. It was not in the Library when this file was
written. That task excludes the infinite-base passage stated here.

## Scope

The target does not claim norm surjectivity for arbitrary finite
extensions of `U`. That is Serre's Proposition 7, with published target
`Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormSurjectivity`.
It also does not repeat the bounded finite-base norm theorem. It is the
step between those two results, before compatible descent and assembly
over solvable towers. No local reciprocity, class formation, Brauer
vanishing or inertia cohomology result is assumed. Acceptance of this
statement is not a proof of it. Existing published Lean and Markdown files
are unchanged.

Authored by Worker 298.
