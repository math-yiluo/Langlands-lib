# The original Levi centralizer from positive source weights

This is a derived consumer of positive-source contraction, radical-contraction
containment, and the original multiplication comparison. It introduces no new
external-source assertion.

The supplied maps are `l : L → P`, `r : U → P`, and `j : P → G` over an arbitrary
field `k` in universe `u`. The group `G` is smooth, connected and affine, `j` is
a closed subgroup, `r` is the original represented geometric unipotent radical,
and the actual scheme multiplication `L × U → P`, with `l` first, is an
isomorphism. This is not an assertion that multiplication is a group
homomorphism. A rational Levi supplies such a radical and multiplication
isomorphism, but no choice of that radical is made here.

The first general lemma says that the image of any group homomorphism
centralizes the image of a central commutative subgroup of its source. Its proof
maps the all-test commutation equation through that homomorphism.

For the positive-source application, `a : A → L` is central, and a cocharacter
`nuA` of `A` is supplied. Another commutative group scheme `T` maps to `L` by
`t`, acts on the original `U` by an actual automorphic action `d`, and has a
cocharacter `nuT`. The exact compatibility equation is
`nuT ≫ t = nuA ≫ a`. The original map `r ≫ j` is equivariant for `d` and
ambient conjugation along `t ≫ l ≫ j`.

A supplied field extension `K/k` splits `T`. Strict positivity is required
for every character of `T_K` whose intrinsic source weight space for `d_K`
is nonbottom, evaluated on the base change of `nuT`. The zero character is
not excluded. Affineness of `U` is an explicit instance premise so that its
source weight spaces can be formed in the hypothesis. This premise is redundant
in the geometric application: the two original closed inclusions into affine
`G` give affineness of `U`. The geometric radical predicate supplies its
smoothness and connectedness.
Positive-source contraction then puts the full all-test image of `r ≫ j`
in the identity-limit subgroup for
`chi = nuA ≫ a ≫ l ≫ j`.

Only over the algebraic closure of `k`, a common split commutative group scheme
`C`, a map `c : C → G`, and cocharacters `eta` and `mu` are supplied.
The actual roots of `c` must be stable under negation. The actual base change
of `j` represents `P(eta ≫ c)`, and `mu ≫ c` is exactly the base change of
`chi`. These are inputs, not existence conclusions.

Base change preserves the proved original radical contraction. The second
part of the supplied geometric radical predicate is precisely the required
radical greatestness for the same original `r` over this algebraic closure.
Radical-contraction containment gives `P(chi)` inside the original parabolic
image after base change. Existing fpqc reflection of containment in the
monomorphic `j` then gives the containment over `k`; the subgroup on the left
need not be represented for this reflection.

Centrality of `a` fixes the original `L`. The published multiplication
comparison now gives all three ground-field all-test equalities:
`P(chi) = range(j)`, `Z(chi) = range(l ≫ j)`, and
`torusCentralizer(a ≫ l ≫ j) = range(l ≫ j)`. The last centralizer tests
commutation with the entire `A` after every refinement of a test scheme;
no rational-point density assertion is used.

For closed `l`, `positiveSourceLeviCentralizerIso` constructs an actual group
scheme isomorphism from the original `L` to any supplied representative
`m : M → G` of that whole-group centralizer. Its homomorphism followed by
`m` is exactly `l ≫ j`; its inverse followed by `l ≫ j` is exactly `m`.
These statements retain the original ambient inclusions.

The local instances for affineness over the splitting extension and for
affineness, smoothness and connectedness over the algebraic closure have explicit
module-specific names. This prevents generated declaration names from colliding
with other base-change developments during combined imports and kernel replay.
Their types, bodies and local scope are unchanged.

No splitness of `A`, reductivity, minimality, or maximal splitness is claimed
or needed by this adapter. The positive direction and the common-torus
presentation over the algebraic closure remain explicit obligations.
In particular, this is not a proof of
`MinimalParabolicLeviCentralizerStatement` and constructs no torus factor
through a supplied solvable radical.
