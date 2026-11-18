# Harris's exact stabilizer for Mackey children

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerMackeyProof`,
namespace `Langlands.Global.Harris`.

`proposition48ExactStabilizerMackeyInheritance.{uF}` proves
`Proposition48ExactStabilizerMackeyInheritanceStatement.{uF}`. It upgrades the
given auxiliary validity of the Mackey child `R` at parity `c` to exact
stabilizer validity, using the parent's exact stabilizer at parity `b`.
The parities and the intermediate field `D` are arbitrary as in the
published statement.

## Implemented proof

Apply `PlaceDatum.exactWeilStabilizer_iff_global` separately to `Q` and `R`.
In each case the supplied normal closure of number fields is Galois.
Write `λ_Q(z)` for the finite component of `Q.ξ` at `Q.Ps.v'` evaluated on
`N_{Q.L/Q.E'}(z)`, and define `λ_R` using the corresponding data of `R`.
Parent exactness says an automorphism of `Q.L` over `Q.E` that preserves
`λ_Q` fixes `Q.E'`.

Let `A = a(Q.E')` and `C = D ⊔ A` inside `Q.L`. The Mackey-child datum
identifies `R.E` with `D` and `R.E'` with `C` and supplies the field embedding
`j : R.L →+* Q.L` over these identifications. In `mackeyUnitComponent`,
transport the child's places to `D` and `C` using the field isomorphisms.
The condition on `R.Ps.v` and transitivity of lying over put the transported
middle place above `Q.Ps.v`. The place of `A` transported from `Q.Ps.v'`
is likewise above `Q.Ps.v`. The parent's unique-place condition descends
to `A` and `C`, so the place of `C` lies over that place of `A` and is
unique above it. The formula for `R.ξ` now gives the child's finite
component on field units by transporting to `C`, taking `N_{C/A}`, and
transporting back to `Q.E'`.

Normalize the field inclusions by using `j` to regard `Q.L` as an extension
of `R.L`. Norm transitivity and transport of the determinant norm give,
for every `z : Q.Lˣ`,

```
λ_R(N_{Q.L/R.L}(z)) = λ_Q(a⁻¹(z)).
```

If `σ ∈ Gal(R.L/R.E)` preserves `λ_R`, lift it to an automorphism `τ` of
`Q.L` over `R.E`. The norm `N_{Q.L/R.L}` intertwines `τ` and `σ`, so `τ`
preserves the character on the right of the displayed identity. Therefore
`a⁻¹ ∘ τ ∘ a` preserves `λ_Q` and fixes `Q.E'`. Thus `τ` fixes `A`, and it
fixes `D` because it is over `R.E`. It fixes their compositum `C`, so `σ`
fixes `R.E'` by injectivity of `j`. Conversely, an automorphism that fixes
`R.E'` preserves the norm `N_{R.L/R.E'}` and hence `λ_R`.

The child comparison converts this equivalence to the required exact Weil
stabilizer. The theorem takes the other conjuncts directly from the child's
given auxiliary validity.

## Imported results

- `HarrisProposition48ExactStabilizerInheritanceStatement` supplies the
  exact target. Its imports give the validity predicates, Mackey-child
  data and the definitions of `conjugateField`, `mackeyField`,
  `conjugateCharacter` and `mackeyCharacter`.
- `HarrisProposition48StabilizerComparison` supplies the local-to-global
  stabilizer equivalence, finite place transport for lying over and the
  single-place norm formula on field units. The imported
  `finitePlacesAbove_subsingleton` descends the unique-place condition to
  each intermediate field.
- `HeckeCharacterTransport` supplies `HeckeCharacter.comap_finiteComponent`,
  which carries a component across a field isomorphism. Its completion
  transport formula gives the corresponding identity on embedded units.
- `RelativeWeilAssemblyCharacters` supplies
  `HeckeCharacter.normComp_finiteComponent`, which computes the component
  of a norm pullback via the local norm at a place above the base place.
- `FiniteArtinTransport.normUnits_map` transports field norms along
  commuting squares of field isomorphisms. It gives the norm identities
  for the child isomorphism, conjugation by `a⁻¹` and the lift of `σ`.
- `Mathlib.RingTheory.Norm.Transitivity` supplies `Algebra.norm_norm`.
  Mathlib's `Normal.tower_top_of_normal` and `AlgEquiv.liftNormal_commutes`
  give the lift and its restriction to the child. The fixing subgroup of
  `C` is the intersection of those of `D` and `A` by
  `IntermediateField.fixingSubgroup_sup`. The reverse stabilizer
  inclusion uses `Algebra.norm_eq_of_algEquiv`.

## Provenance

Harris gives condition (4.12) in the proof of Lemma 4.7, printed p. 204,
and uses Mackey constituents in the setting of Proposition 4.8, printed
pp. 201–203. See M. Harris, *The local Langlands conjecture for GL(n) over
a p-adic field, n < p*, Invent. Math. 134 (1998), 177–210, registered as
`harris-1998-local-langlands`.

The inheritance argument is derived in the operator's plan
`operator-external-inputs-plan-2026-11-16`, Section 4.8, item “The hypothesis”
(TeX lines 903–907). The Lean proof implements its lifting argument on
number fields, using the unique-place comparison to read the local
stabilizer on each side.
[HarrisProposition48ExactStabilizerInheritanceStatement.md](HarrisProposition48ExactStabilizerInheritanceStatement.md)
