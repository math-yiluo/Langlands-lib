# Proof of surjectivity on compact-open fixed vectors

The correspondence of the Lean proof with its target was checked. This proof
uses the published projection proof identified below.

The closing declaration is
`Langlands.Compact.fixedVectorSurjectivity :
Langlands.Compact.FixedVectorSurjectivity.{uG, uV, uW}`.
The group, source module, and target module retain independent universes.
The target internally quantifies over a group with a topology and
`IsTopologicalGroup`, two complex modules, two smooth representations, an open
subgroup with compact underlying set, and a surjective intertwiner. The closing
theorem has no additional hypotheses. Neither module is given a topology.

For a target fixed vector `w`, surjectivity of `f` supplies `v` with
`f v = w.val`. The proposed fixed-vector preimage is the subtype element whose
underlying vector is `averageMap ρ hρ K hK v`. The component lemma
`averageMap_mem_fixedVectors` supplies its membership proof.

After `Subtype.ext`, the remaining goal is equality of the underlying vectors.
The definition of `fixedVectorMap` reduces its left side to
`f (averageMap ρ hρ K hK v)`. Evaluating `averageMap_commute` at `v` with
`LinearMap.congr_fun` gives

```text
f (averageMap ρ hρ K hK v) = averageMap σ hσ K hK (f v).
```

Rewriting by `f v = w.val` leaves the average of a fixed vector.
`averageMap_id σ hσ K hK w.val w.property` identifies that average with
`w.val`, completing the subtype equality and the surjectivity witness.
Thus the implemented proof uses the membership and identity components of the
projection property and the naturality equality. It does not need a separate
smoothness-transfer theorem; both smoothness assumptions are supplied by the
target.

The result proves the right-surjectivity clause on compact-open fixed vectors.
The coefficient field is exactly the complex numbers. It does not state full
categorical exactness or exactness over arbitrary coefficient rings.

Original source: Bill Casselman, *Introduction to admissible representations
of p-adic groups*, Chapter II: *Smooth representations*, revision June 16, 2019,
Section 1, Proposition II.1.3, page 4 (the right-surjectivity clause).
The normalized projection discussion on page 3 and finite-coset averaging
formula in the proof of Proposition II.1.2 on page 4 explain the averaging
method. The implemented argument uses the project's normalized finite-orbit
average through its projection and naturality interface. Source ID
`casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Retained original:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The exact proposition target is `Langlands.Compact.FixedVectorSurjectivity`
(module `Langlands.Representation.Compact.SurjectivityStatement`),
published at Library commit `bb596ce619f2174816281f508cce65b3303beeb4`.
Definition dependencies are the compact averaging definitions
`Langlands.Representation.Compact.Definitions` and the smoothness definitions
`Langlands.Representation.Smooth.Definitions`.

The exact imported projection proof is
`Langlands.Representation.Compact.ProjectionProof`.
It proves `Langlands.Compact.ProjectionAndNaturality`, and supplies all
three component lemmas used above. It was
published at Library commit `d0f5322f745425b08ae8e72c1031206f45cb049e`.
The Lean file's SHA256 there is
`689b92fac7e04b7ee2cb3dd4702653725a597997331ca62c6461ba7ef12fcc41`;
the paired Markdown SHA256 is
`a2217b34bacd418614535068dcc858ae3d44ad3a0638be726fc8838499f8d5b2`.
When this proof was checked, the target, the projection proof and their
dependencies were available, and all twelve source-closure files matched their
published hashes.

Environment in which it was checked:
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The exact dependency closure and this proof were compiled, and the whole target
was checked at three independent universes. All commands exited
successfully; the closing theorem's reported axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`.
