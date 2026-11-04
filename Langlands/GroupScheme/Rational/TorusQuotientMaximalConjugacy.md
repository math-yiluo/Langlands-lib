# Maximal tori over a torus quotient with a homomorphic section

This internal construction supplies actual source isomorphisms and rational
kernel conjugators for maximal tori in a split-unipotent extension of a torus
with a supplied homomorphic section. Stable-vector existence and torus-action
linearization remain explicit proposition inputs. It does not prove the full
solvable maximal-torus conjugacy statement.

## Maximality and a homomorphic section

Let `G` be affine and locally of finite type over any field `k`, let `Q` be a
torus, and suppose group-scheme homomorphisms `q : G → Q` and `s : Q → G`
satisfy `s ≫ q = 𝟙 Q`. For a maximal torus `i : T → G`, assume that every
homomorphism `j : T → G` with `i ≫ q = j ≫ q` is rationally subgroup-conjugate
to `i`. This comparison allows arbitrary homomorphisms `j`.

The section `s` is monic. The published field-extension descent theorem
`SplittingAssembly.isAffine_of_isTorus` gives affineness of `Q`, so the existing
closedness theorem for monomorphisms from affine tori makes `s` a closed torus
inclusion. Compare `i` with
`(i ≫ q) ≫ s`; they have equal quotient maps. Conjugacy transfers full
maximality to the latter map. Its factorization through the closed torus `s`
then forces `i ≫ q` to be invertible, by the unchanged `IsMaximalTorus`
definition. The construction `IsMaximalTorus.torusQuotientIsoOfSection` retains
the actual isomorphism whose homomorphism is exactly `i ≫ q`.

This argument does not assume that `i ≫ q` is closed or maximal beforehand.
The section is a homomorphism; an underlying scheme section is insufficient.

## Split-unipotent kernel specialization

Assume an actual closed `n : N → G`, with `N` smooth, connected, unipotent and
split unipotent, and that `q` is an actual represented fppf quotient by the
all-test range of `n`. Retain the supplied torus `Q` and homomorphic section.
The two explicit proposition inputs are
`SplitUnipotentStableVectorSubgroupStatement` and
`TorusVectorActionLinearizationStatement`, each in the original universe.

The published equal-map split-unipotent conjugacy theorem supplies the
comparison premise, with its affine torsor input instantiated by the published
unconditional proof. Thus
`IsMaximalTorus.splitUnipotentTorusQuotientIso` identifies each maximal torus
with `Q`. Composing these actual quotient isomorphisms gives
`IsMaximalTorus.isoOverSplitUnipotentTorusQuotient`; its companion equation says
that the two source maps into `Q` agree under this precise isomorphism.

`SplitUnipotentTorusQuotientConjugacyData` retains an actual source isomorphism,
an actual `k`-point of the specified group `N`, and the equality saying that its
image under `n` conjugates the original inclusions with that source isomorphism.
`IsMaximalTorus.splitUnipotentTorusQuotientConjugacy` constructs these data by
applying the published same-source cocycle correction after the source
alignment. The final theorem packages these witnesses in the unchanged
`MaximalToriAreConjugate` predicate.

All fields, all characteristics, finite fields, imperfect fields, nonsplit tori,
and the original universe are retained. No closed-subgroup unipotence input is
needed. Existence of the torus quotient, its split-unipotent kernel and the
homomorphic section are supplied, and the two named structural propositions
remain unproved here.

## Provenance

This is an internal deduction from the existing full maximality definition,
conjugacy transport, affine torus monomorphism closedness and split-unipotent
same-source cocycle construction. The proof follows the maximality comparison
described above. It uses no new external assertion, axiom or conjugacy theorem
for maximal split tori.
