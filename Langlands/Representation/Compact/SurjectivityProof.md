# Proof of surjectivity on compact-open fixed vectors

Worker 5 authored the Lean proof, reused without source changes by Worker 29.
Worker 29 checked its correspondence with the accepted target and prepared this
expanded explanation. This proof uses the independently checked, accepted,
and published projection proof identified below. This proof
requires its own registered independent check, semantic review, and publication.

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
accepted target.

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

The exact accepted proposition target is
`40e87eae-9077-41b0-a7d0-49e3f58c1d41`, version 1, effective snapshot
`9d79467c8b7e9c0013e365a40865b2e511da4a243ae73ebb7cac12c694d16917`,
published at commit `bb596ce619f2174816281f508cce65b3303beeb4`.
Its proposition fingerprint is
`a9729b082c2b7c43ce0f062137b52106994b68bf28ec642dce2c1024861357ea`.
Definition dependencies are compact averaging artifact
`ed385ab4-3443-4345-a7c7-5d91c74940f9`, version 1, effective snapshot
`aad5d14b4a17fc183be073cb292549ca0522d206c40cf3977960e1ddf23caebc`,
and smoothness artifact `665022df-625b-44ae-9dbd-425f6e266bab`, version 1,
effective snapshot
`092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`.

The exact imported projection proof is artifact
`0f736d22-4088-4bad-91fa-320276a98f66`, version 1,
`Langlands.Representation.Compact.ProjectionProof`, from task
`849a1dbe-68d3-4bc8-9c67-ca059539e827`, revision 1.
It proves accepted statement `91124244-2c99-4f10-91d2-bcab3a34712c`,
version 1, `Langlands.Compact.ProjectionAndNaturality`, and supplies all
three component lemmas used above. Its accepted effective snapshot is
`e2b147792d9176fec25e3cb60221aa503bfc6766d5d618ca3a79119138b5bf17`,
published at Library commit `d0f5322f745425b08ae8e72c1031206f45cb049e`.
The effective Lean SHA256 is
`689b92fac7e04b7ee2cb3dd4702653725a597997331ca62c6461ba7ef12fcc41`;
the paired Markdown SHA256 is
`a2217b34bacd418614535068dcc858ae3d44ad3a0638be726fc8838499f8d5b2`.
Reviewer 60 accepted the proof, and the final independent publication receipt
is `f166e3a5db68445f91d4a4a606c172e3`. The published integration also passed
registered checker activation 5. Worker 29 verified these receipts and the
current availability of the target, projection proof, and accepted dependencies;
all twelve source-closure files matched their published hashes.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 29 compiled the exact accepted dependency closure and this proof, then
checked the whole target at three independent universes. All commands exited
successfully; the closing theorem's reported axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`. These are development checks.
Independent proof checking, semantic review, and publication establish
acceptance separately.
