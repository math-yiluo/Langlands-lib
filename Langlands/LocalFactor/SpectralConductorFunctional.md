# A conductor functional on the exact virtual group of the base field

Worker 4803 wrote this supporting module of
`SpectralConductor.spectralConductorRankOneReduction`.

## Inertia version of the class-function formula

For a p-adic field `E` with topological data `T` and a base field `K`, the Library's
`inertiaArtinConductor T K ρ` is the Artin expression of a representation `ρ` of the
actual inertia group `inertia T K`, for its action on the integer ring of `E`.

- `galoisLowerCount T K b σ` counts the indices `i < b` with `σ` in
  `lowerRamificationGroup T K i`.
- `integerRing_noetherian'`, `automorphismGroup_finite'` and
  `inertiaIntegerAction_faithful'` re-prove three facts that are private in the
  Library module `Ramification/Galois`, with the same proofs: the integer ring is
  Noetherian, the automorphism group is finite, and inertia acts faithfully.
- `inertiaArtinConductor_eq_classSum` (and the variant with primed name, whose field
  structures are implicit arguments found by unification):
  `a(ρ) = |I|^{-1} Σ_{g ∈ I} m(g) (dim V - tr ρ(g))`. It is
  `artinConductor_eq_classSum` for the inertia group acting on the integer ring. Its
  lower groups are `inertiaLowerGroup`, by the definition in `Ramification/Galois`, and
  its zeroth group is all of inertia (`inertiaLowerGroup_zero`).
- `trace_apply_one`: the trace character of a virtual class at `1` is its degree.

## The functional

Fix an actual finite Galois subfield `M` of the algebraic closure. Let
`I = inertia (dataM F M) F.Carrier` be the inertia group of `M/F`.
`lowerBound F M` is a chosen index beyond which the lower groups of `M/F` vanish. The
Library's `exists_lowerRamificationGroup_eq_bot` supplies it.
`inertiaSection F M` is a set-theoretic section of `weilInertiaRestriction F M`, which
is surjective by `HerbrandBridge.weilInertiaRestriction_surjective`.

- `inertiaClassSum F M f = |I|^{-1} Σ_{γ ∈ I} m(γ) (f(1) - f(s(γ)))` for a function `f`
  on Weil inertia, with `s` the section.
- `inertiaTrace F x` is the trace character of a base virtual class on Weil inertia.
- `conductorFunctional F M : Virtual F (base F) →+ ℂ` is
  `x ↦ inertiaClassSum F M (inertiaTrace F x)`. It is additive because the trace is
  additive.
- `conductorFunctional_one`: the trivial character has value `0`.
- `conductorFunctional_baseClass`: let `A` be a genuine continuous representation with
  a presentation `P`, and `P.extension ≤ M`. Then the value at `A` is the Artin
  expression of the refined presentation `P.refine M h`. Proof: the refined
  presentation's representation is the descent along `weilInertiaRestriction F M`, and
  `representation_apply` evaluates it at `weilInertiaRestriction (s(γ)) = γ` as
  `A(s(γ))`. The inertia class-sum formula then matches `inertiaClassSum` term by term.

The functional is defined for every class, but it is a conductor only on classes
whose inertia action factors through `I`. The reduction uses it only on such classes.

## Source

Serre, *Local Fields*, VI §2, Proposition 2, printed p. 100 (PDF p. 107), applied to
the inertia group. Since `G_i ⊆ G_0` for `i ≥ 0`, the class function is supported on
inertia, so the inertia group gives the same sum as the full Galois group.
