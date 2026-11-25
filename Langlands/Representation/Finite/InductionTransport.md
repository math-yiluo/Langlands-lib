# Induction along an isomorphism of the inducing group; the two rank-one representations

Module `Langlands.Representation.Finite.InductionTransport`, namespace `Langlands.FiniteRep`.
Two bridges used by the integrality proof of the finite Artin conductor
(`Langlands.LocalFactor.Ramification.FiniteIntegralityProof`): the Library's Brauer theory
induces from a subgroup `S ≤ G` along `S.subtype` and uses the `FDRep` `oneDimensional χ`, while
the induction formula for the conductor induces along `AlgEquiv.restrictScalarsHom` from the
Galois group of the fixed field and uses `Langlands.characterRepresentation χ`.

## Statements

**`indCongrEquiv`.** Let `k` be a commutative ring, `G`, `H`, `H'` groups and `V` a `k`-module.
Let `e : H' ≃* H`, `φ : H →* G`, `φ' : H' →* G` with `φ' h = φ (e h)` for all `h`, and let
`ρ`, `ρ'` be representations of `H`, `H'` on `V` with `ρ' h = ρ (e h)` for all `h`. Then the
induced representations of `G` are equivalent:

```lean
def Langlands.FiniteRep.indCongrEquiv.{uk, uG, uH, uH', uV}
    {k : Type uk} [CommRing k] {G : Type uG} {H : Type uH} {H' : Type uH'}
    [Group G] [Group H] [Group H'] {V : Type uV} [AddCommGroup V] [Module k V]
    (e : H' ≃* H) {φ : H →* G} {φ' : H' →* G} (hφ : ∀ h, φ' h = φ (e h))
    {ρ : Representation k H V} {ρ' : Representation k H' V} (hρ : ∀ h, ρ' h = ρ (e h)) :
    (Representation.ind φ' ρ').Equiv (Representation.ind φ ρ)
```

The compatibilities are hypotheses on elements rather than equalities of homomorphisms because
the carrier `Representation.IndV φ ρ` depends on `φ` and `ρ`, and rewriting inside it is
awkward. No finiteness is assumed.

**`oneDimensionalEquiv`.** For a field `k`, a group `H` and `χ : H →* kˣ`, the `FDRep`
`oneDimensional χ` (module `Langlands.Representation.Finite.Virtual`) and the scalar
representation `Langlands.characterRepresentation χ` (module
`Langlands.Representation.Twist.Definitions`) are equivalent:

```lean
def Langlands.FiniteRep.oneDimensionalEquiv.{uk, uH} {k : Type uk} [Field k] {H : Type uH}
    [Group H] (χ : H →* kˣ) :
    Representation.Equiv (oneDimensional χ).ρ (Langlands.characterRepresentation χ)
```

`Langlands.LocalClassField.rankOneCharacterRepresentation χ` is by definition
`Langlands.characterRepresentation χ`, so this is also the bridge to the rank-one representation
of local class field theory.

## Proof outline

Mathlib defines `Representation.ind φ ρ` on `IndV φ ρ`, the coinvariants of
`k[G] ⊗[k] V` under `H` acting by `h • (x ⊗ v) = (x · φ h⁻¹) ⊗ ρ h v`
(`Representation.tprod ((leftRegular k G).comp φ) ρ`), with `G` acting on the left factor. For
`h ∈ H'` the operator of `h` for `(φ', ρ')` equals the operator of `e h` for `(φ, ρ)` (the
two hypotheses, unfolded through `Representation.tprod_apply`). Hence the two submodules
divided out are equal, and the identity of `k[G] ⊗ V` descends in both directions
(`Representation.Coinvariants.lift`); surjectivity of `e` is used for the inverse. The two maps
are inverse on generators (`Representation.Coinvariants.induction_on`) and commute with `G`
(`ext` on generators of `IndV`, then `simp`).

Both rank-one representations act on `k` by multiplication by `χ h`; the identity of `k` is
the equivalence, checked on `1` (`LinearMap.ext_ring`).

## Declarations, in order

- `indCongrEquiv` — the equivalence above. The proof follows the Library's
  `Langlands.InducedFixedVectors.indRangeEquiv` (module
  `Langlands.LocalFactor.Ramification.InductionProof`), the special case `H' = φ.range`.
- `oneDimensionalEquiv` — the equivalence above, as `LinearEquiv.refl k k`; compare
  `Langlands.FiniteRep.scalarCharacterEquiv` (module `Langlands.Representation.Finite.Virtual`).

## Use

The integrality proof applies `indCongrEquiv` with `H' = S` a subgroup of
`G = F ≃ₐ[K] F`, `H = F ≃ₐ[F^S] F`, `e = IntermediateField.subgroupEquivAlgEquiv S`,
`φ = AlgEquiv.restrictScalarsHom K` and `φ' = S.subtype`: the first hypothesis holds because
both sides are the same automorphism of `F`.

## Sources

Induction is transitive and depends only on the subgroup with its embedding; Serre, *Local
Fields* (1979), Chapter VI §2, uses this when passing from a subgroup `H` of `G = Gal(L/K)` to
the Galois group of `L` over the fixed field of `H` in the proof of Proposition 4 and its
Corollary (printed pages 101–102) and of Theorem 1′ (printed page 102), with the induced class
functions of §1, printed page 98 (literature ID `serre-1979-local-fields`). Mathlib's
`Representation.ind` (`Mathlib.RepresentationTheory.Induced`) is the definition used.
