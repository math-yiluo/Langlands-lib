# Universe transport of finite abelian local reciprocity

`Langlands.LocalClassField.NYLL.finiteAbelianReciprocityUniverseTransport`
proves the published target
`Langlands.LocalClassField.NYLL.FiniteAbelianReciprocityUniverseTransportStatement.{u, v}`
from [`UniverseTransportStatement`](UniverseTransportStatement.lean).
Its type is exactly that statement: the host proposition
`FiniteAbelianReciprocity.{0, 0}`, through its alias
`FiniteAbelianReciprocityTypeZeroStatement`, implies
`FiniteAbelianReciprocity.{u, v}` for independent universes `u` and `v`. The
proof adds no hypothesis. The statement and host files are unchanged.

## Model data

The proof uses the published model layer
[`UniverseZeroModel`](UniverseZeroModel.lean). Fix a prime `p`, fields
`F : PadicField.{u} p` and `E : PadicField.{v} p`, their supplied algebra,
scalar-tower, finite-dimension and abelian-Galois instances, and arbitrary
supplied data `TF` and `TE`.

1. Write `F₀ = universeZeroModel F` and `E₀ = universeZeroModel E`, with
   `eF = universeZeroEquiv F` and `eE = universeZeroEquiv E`. Install
   `universeZeroAlgebra F E` locally. Then
   `universeZeroAlgebra_isScalarTower`, `universeZeroAlgebra_finiteDimensional`
   and `universeZeroAlgebra_isAbelianGalois` give the instances needed by the
   Type 0 statement.
2. Apply the hypothesis to `p`, `F₀`, `E₀` and the canonical data
   `TF₀ = F₀.canonicalTopologicalData` and `TE₀ = E₀.canonicalTopologicalData`.
   This gives a quotient equivalence `r₀` with the geometric clause `hgeom` and
   the inertia clause `hiner`.
3. Let `Q = universeZeroNormQuotientEquiv F E TF₀ TF`. It identifies the
   model's norm quotient, with the topology of `TF₀`, with the actual quotient
   `F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range`,
   with the topology of `TF`. Let `G = universeZeroGaloisEquiv F E`. It
   identifies the actual Galois groups.
4. The witness is `Q.symm.trans (r₀.trans G)`. It is an isomorphism of
   topological groups between the actual host quotient and
   `Gal(E.Carrier/F.Carrier)`.

The proof uses three translations. Each holds for arbitrary supplied data,
including the convention at zero.

- `Q.symm` sends the class of `a : F.Carrierˣ` to the class of its model unit
  `a₀` (`universeZeroNormQuotientEquiv_symm_mk`).
- `TF₀.ord a₀ = TF.ord a` (`ord_eq_of_algEquiv`).
- `TE.discreteValuation (eE y) = TE₀.discreteValuation y`
  (`discreteValuation_eq_of_algEquiv`), and
  `TF.residueCardinality = TF₀.residueCardinality`
  (`residueCardinality_eq_of_algEquiv`).

## Geometric clause

Let `TF.ord a = 1` and `TE.discreteValuation x ≤ 1`. Then the model unit
`a₀` has order `1` for `TF₀`, and `eE.symm x` has valuation at most `1` for
`TE₀`. So `hgeom` applies to `a₀` and `eE.symm x`. The inverse automorphism
`(G σ).symm` is `eE ∘ σ.symm ∘ eE.symm` by definition, and `eE` is a ring map.
The host difference
`(r [a]).symm x - x ^ TF.residueCardinality` is therefore `eE` applied to the
model difference
`(r₀ [a₀]).symm (eE.symm x) - (eE.symm x) ^ TF₀.residueCardinality`.
The valuation comparison turns the model inequality into the host inequality.
The inverse automorphism of the host clause is thus kept.

## Inertia clause

For `σ : Gal(E.Carrier/F.Carrier)`, apply `hiner` to `G.symm σ`. Since
`eE ((G.symm σ) y) = σ (eE y)`, for every model element `y` we have
`TE.discreteValuation (σ (eE y) - eE y) = TE₀.discreteValuation ((G.symm σ) y - y)`.

- The right-hand sides correspond through `x = eE y`.
- From left to right: a host witness `a` with `TF.ord a = 0` and `r [a] = σ`
  gives the model witness `a₀`. It has `TF₀.ord a₀ = 0` and `r₀ [a₀] = G.symm σ`.
- From right to left: a model witness `a₀` gives the host witness `eF a₀`, as
  a unit. Its order is `0` by `ord_eq_of_algEquiv`. Its value is
  `G (r₀ [a₀]) = σ`, because the two unit maps are mutually inverse.

The full existential iff, for the same witness `r`, is therefore proved for
every `σ`.

## Scope

This proof transports the clauses from universe zero. It proves no Type 0
reciprocity and no uniqueness of reciprocity maps. It makes no comparison with
the cohomological construction and no claim about a Weil-group or common-closure
system.

## Provenance

This is an internal transport proof between the published Library propositions.
Worker 929 supplied the complete proof draft; Worker 125 checked it against the
published host and model interfaces and prepared this proof unit for submission.
It copies no external implementation and makes no additional claim about the
original NYLL reciprocity theorem.
