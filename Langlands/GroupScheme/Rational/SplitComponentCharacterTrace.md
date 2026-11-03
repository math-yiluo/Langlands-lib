# Character traces from a split component into the actual root span

Author: Worker 1264.

This derived unit combines integral Galois averaging, all-test central
cocharacter descent, the published root-annihilator centrality theorem, and
perfect real duality. It constructs an element of the actual relative-root
span rather than assuming a geometric root datum or a Weyl realization.

For a split torus, `IsSplitTorus.toRat_mem_ratSpan_iff_annihilator` proves
that the rationalized value of a character belongs to the rational span of
a finite selection of characters exactly when its integral pairing
vanishes on every integral common annihilator of that selection. The
published integral-span theorem extends the vanishing to the real
annihilator. Perfect real duality identifies its character annihilator
with the original real character span. Faithful rational-to-real scalar
extension gives the rational conclusion. The reverse implication
evaluates the double-annihilator description on each integral
cocharacter.

Now let `k` be any field, `K/k` a finite Galois extension with its finite
automorphism enumeration, `T` an affine commutative group scheme, and
`t : T → M` a morphism monic on underlying schemes into an affine group
scheme. Specify a split component `a : A → M` and a commutative-group
scheme morphism `f : A → T` whose ambient composite is `a`. For an actual
character `χ` of `T_K` trivial on `f_K`,
`IsSplitComponent.latticePairing_characterTrace_eq_zero` proves that the
integral Galois trace of `χ` pairs trivially with every cocharacter of
`T_K` central in `M_K`. The pairing adjunction transfers the trace to the
cocharacter orbit sum. Central cocharacter descent and the universal
property of the specified rational split component give its vanishing.

If `M` is additionally smooth and connected, and `T_K` is split,
`IsSplitComponent.characterTrace_mem_relativeRootSpan` puts the
rationalized trace in the span of the actual Lie-theoretic relative
roots of `t_K`. Smoothness, affineness, and connectedness persist under
the field extension by the published base-change results. Each integral
cocharacter annihilating those roots is central by
`rootAnnihilatorCentrality`. The trace therefore annihilates it, and
the first equivalence gives membership in the actual rational root span.

`IsSplitComponent.rootSpanCharacterTrace` packages this trace with its
proved root-span membership. Its displayed coercion is exactly the
rationalized integral Galois orbit sum. No maximality of `T`, reductivity
of `M`, or base-change greatestness of a central torus is needed.

This is an internal consequence of the cited Lean interfaces. It proves
the central-trace root-span step used in the intended Borel–Tits 3.6
argument. Geometric Weyl realization, positive-root containment, and the
ambient maximal-split Levi centralizer theorem remain separate.
