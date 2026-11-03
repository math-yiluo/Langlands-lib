# Induction compatibility on the actual rational-point family

`RationalPointFamily.RationalInductionCompatibilityStatement` is the
unproved universal target for the first equation of Aubert 1995,
Theorem 1.7(2), printed p.2181 / PDF p.3:

`D_G ∘ i_J = i_J ∘ D_(L_J)`.

The operator is the unadjusted `sum_I (-1)^|I| i_I r_I`. There is no
additional rank sign. Every standard subset `J` is quantified.

The group is the actual rational-point group of a connected reductive group
scheme over an arbitrary nonarchimedean local field. The topology is the
canonical evaluation `pointTopology`; the torus is maximal split, and the
cocharacter is generic. No characteristic-zero, split, quasisplit or
positive-rank restriction is added. Simple-root finiteness is obtained from
the explicit `HasRelativeRootSystem` premise, with the torus monomorphism
derived from maximal splitness. Empty simple-root sets and `J = ∅` are
allowed.

`D` is exactly the published `rationalAlternatingOperator` of this family.
`ind` is the integer-linear map `inductionK0` of its actual normalized
induction functor for `J`. `DL` is exactly
`rationalLeviAlternatingOperator` inside the actual closed subgroup
`levi i ν J`. Its labels are the finite subtype `J`, and its subgroups are
the literal `subgroupOf` restrictions at `leviIndex J I` of the same
ambient standard families. Thus this specializes the published generic
`InductionCompatibilityStatement` without choosing an unrelated family or
formal endomorphism. The imported actual-representation class formulas for
`inductionK0` and the two operator constructions expose the functors on the
exact finite-length Grothendieck groups. Representation carriers use
`max (u + 1) v`; no resizing of their Grothendieck groups is asserted.

The premises remain separate and visible. Ambient decompositions are
derived from `StandardCocharacterStatement`; restricted decompositions are
derived from `StandardLeviIntersectionStatement`. Exactness in both groups
is derived by `standardParabolicFiniteLength` and
`standardLeviParabolicFiniteLength` from the existing induction and Jacquet
exactness theorems. The topological inputs are ambient local compactness,
nonarchimedeanness and Hausdorffness; closedness of the ambient standard
parabolics and radicals and of each Levi; continuity of the ambient and
restricted projections; and compact-subgroup-limit premises for ambient
and restricted radicals. Separate ambient and restricted normalized
induction and Jacquet finite-length preservation premises are explicit.
Closedness gives the Levi's local compactness; the other group-topological
properties restrict to it. No premise supplies the desired equation.

This is a proposition declaration, not a proof. All actual structural,
topological and representation-theoretic realization obligations remain.
Its explicit intermediate premises neither enlarge the parent's itemized
external Chapter V boundary nor establish the main identity. Proof
successors and final assembly remain with the parent and existing owners.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
Definition 1.5 and first equation of Theorem 1.7(2), printed p.2181 /
PDF p.3. The implementation is an internal actual-family specialization of
the published generic induction target and the actual rational-point
construction adapters. Aubert's 1996 erratum does not discharge the
unresolved Proposition 3.2; it is not used here.
