# Longest-representative Jacquet compatibility on actual rational points

`RationalPointFamily.RationalJacquetCompatibilityStatement` is the unproved
universal target for the second equation of Aubert 1995, Theorem 1.7(2),
printed p.2181 / PDF p.3:

`r_J ∘ D_G = Ad(n) ∘ D_(L_Jprime) ∘ r_Jprime`.

Here `w_J = longestRep cs J` is the specified longest member of `D(J, ∅)`,
`Jprime = associatedSubset cs J`, and every actual normalizer lift `n` of
`w_J` is quantified. The published `rootSet_associatedSubset` consequence
identifies the root set of `Jprime` with the actual character image
`w_J⁻¹(J)`, under the displayed root-sign, minimality and associated-subset
premises. It is not a freely chosen relabeling.

The field is an arbitrary nonarchimedean local field. The ambient group is
the actual rational-point group of a connected reductive group scheme with
its canonical evaluation topology `pointTopology`. The torus is maximal
split and the cocharacter generic. The labels are the actual simple relative
characters; their finite enumeration is derived from `HasRelativeRootSystem`.
The finite Weyl quotient is the normalizer of the actual torus image modulo
its full centralizer. Separate numerator and denominator comparisons connect
it to scheme-normalizer points. A Coxeter system is supplied on that exact
quotient, with `RootLengthComparison` and
`PositiveSimpleReflectionComparison` linking its length and simple
reflections to actual character signs. `minimalityLengthCriterion` and
`associatedSubsetLaws` are separate intrinsic finite-Weyl inputs.

`D` is the actual `rationalAlternatingOperator`. `rJ` and `rJprime` are
`jacquetK0` of the actual normalized Jacquet functors for `J` and `Jprime`.
`DLprime` is `rationalLeviAlternatingOperator` in the actual closed subgroup
`levi i ν Jprime`, with finite subtype labels in `Jprime` and literal
`subgroupOf` restrictions of the same ambient standard families. Both
operators use `(-1)^|I|` with no additional rank sign. They act on the exact
finite-length Grothendieck groups at carrier universe `max (u + 1) v`.
The published operator and Jacquet class formulas expose the actual functors.

The transport is the actual `conjugationK0` by `n`. Its subgroup membership
witness is derived by `associatedLeviConjugation_of_standard` from
`StandardLeviConjugationStatement` and the displayed actual-root comparisons.
It is not an arbitrary associated-Levi hypothesis. That adapter gives
`n L_Jprime n⁻¹ = L_J`; inverse conjugation is the continuous equivalence
from `L_J` to `L_Jprime`. Representation pullback thus sends the action
`σ` to `x ↦ σ(n⁻¹ x n)`, in the source's forward-conjugation convention.
No premise assumes the desired K0 equation or equality of the conjugating
elements for different lifts. Subgroup-image independence does not imply
independence of induced representation classes.

Ambient decompositions are derived from `StandardCocharacterStatement`;
restricted decompositions are derived from `StandardLeviIntersectionStatement`.
Exactness in both groups is derived by `standardParabolicFiniteLength` and
`standardLeviParabolicFiniteLength` from the existing induction and Jacquet
exactness theorems. Ambient local compactness, nonarchimedeanness and
Hausdorffness, closedness of standard parabolics, radicals and Levis,
continuity of the ambient and restricted projections, and compact-subgroup-limit
conditions for their radicals are explicit. Ambient and restricted normalized
induction and Jacquet finite-length preservation remain separate inputs.
Closedness supplies each Levi's local compactness, with the inherited topology.

No characteristic-zero, split, quasisplit or positive-rank assumption is
added. Empty simple-root sets and `J = ∅` are allowed, and the full
centralizer denominator retains the anisotropic and central contribution.
This is a proposition declaration, not a proof or a realization of its
premises. The intermediate inputs do not enlarge the parent's finite
external Chapter V structural boundary. Proof successors and the discharge
of representation-theoretic premises remain with the parent and existing
owners.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
printed p.2180 / PDF p.2 for `w_J`, `Jprime` and conjugation conventions,
and Definition 1.5 and Theorem 1.7(2), second equation, printed p.2181 /
PDF p.3. The implementation is an internal actual-family specialization of
the published generic Jacquet target and actual rational-point adapters.
The relative Weyl quotient uses the full-centralizer correction recorded in
the source audit. Neither unresolved Proposition 3.2 nor the invalid original
proof of Theorem 3.6 is used.
