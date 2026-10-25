# The actual single break in prime total ramification

The theorem `Langlands.LocalClassField.primeTotallyRamifiedBreak.{u,v}` proves
exactly the published proposition `PrimeTotallyRamifiedBreak.{u,v}`. It has
no additional outer hypotheses. The fields retain independent arbitrary
universes, the supplied compatible algebra, finite dimension, and Galoisness.
The target statement and its imported constructions are unchanged.

Write `ell` for the supplied relative degree and use the canonical topological
data on both fields. The proof first applies
`inertia_eq_top_of_canonical_totalRamification` from
`PrimeRamificationArithmeticSupport`. The assumed equality of absolute
ramification indices and the published degree formula force relative residue
degree one. Base-field integers therefore represent every residue class and
are fixed by the actual Galois group. This makes the actual inertia group the
whole group.

The theorem `exists_prime_lowerRamificationGroup_pattern` from
`PrimeInertiaBreakSupport` takes one less than the first trivial lower-group
index. The prime-order subgroup dichotomy and antitonicity give the required
pattern for every natural index. The first trivial index is positive because
the zeroth group is full inertia and the Galois group is nontrivial.
Consequently, the break is positive exactly when the first lower group is
the whole group.

The arithmetic support then proves that this first group is the whole group
exactly when `ell = p`. In that case the uniformizer character has exponent
`p` in residue characteristic `p`, so it is trivial; fixed residue
representatives give the first-group condition on all integers. If `ell`
differs from `p`, taking `p`th powers is surjective on the group and moves
positive lower groups one step deeper. Were the first group the whole
group, termination would fail. The companion support Markdown gives the
implemented ideal-power displacement argument in detail.

Finally, `herbrandPsi_nat_of_prime_pattern` computes the actual `herbrandPhi`
at natural inputs by the published finite-sum formula for actual lower-group
orders. It evaluates to `n` at the proposed natural inverse value. The
published inverse identity yields the asserted value of the constructed
`herbrandPsi`. The proof retains break zero, natural subtraction only beyond
the break, and the first branch at equality `n = t`.

The helper modules form part of this proof submission and are proved directly;
no separate proposed helper proposition is used as an assumption. The
arithmetic support imports neither the parent statement nor this proof, so its
total-inertia result is reusable without a circular import. No norm or
reciprocity result is used.

The mathematical target is Serre, *Local Fields* (1979), Chapter V §3,
printed page 83 / PDF page 90. The lower-group convention is Chapter IV §1,
printed pages 61–62, and the inverse-Herbrand convention is Chapter IV §3,
printed pages 73–74. The proof above is an internal derived route to that
published statement; it does not reproduce Serre's proof through graded
embeddings. The source is registered as `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The applicable Local Fields entries in Serre's 2019 corrections, registered
as `serre-book-corrections-2019`, were checked; they do not change the
prime-break assertion on printed page 83. The correction document has SHA256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.

Worker 96 implemented the proof and both support modules. Worker 231
contributed the adapted published fixed-residue-representative argument,
the characteristic-`p` uniformizer route, and the power-lowering suggestion,
as detailed in the arithmetic support Markdown.
