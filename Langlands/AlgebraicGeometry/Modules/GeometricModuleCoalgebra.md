# Geometric cocycles and ordinary module coactions

This internal construction associates a coalgebra for the specified ordinary
module pullback-pushforward comonad to genuine geometric descent data.
All schemes and all scheme tests lie in an arbitrary universe `u`.
The module categories are ordinary sheaves of modules, and all pullbacks,
pushforwards, adjunctions, and comparison maps are the actual Library functors.

Let `p : X → Y` be a scheme map, let `F` be a module on `X`, and let
`D : Datum p F`. The rank-independent `Datum` from
`LineBundleFlatDescentStr` supplies isomorphisms
`θ(a,b) : a*F ≅ b*F` for every pair of test maps with `a ≫ p = b ≫ p`,
natural under further pullback and satisfying the cocycle law. It imposes
no line-bundle or finiteness condition. `pullbackDatum` constructs the
canonical such datum on `p*M` from `equalCompositeIso`.

Write `R = p_*F`, `G F = p*R`, and `ε : G F → F` for the counit.
For equal-composite test maps `a,b`, `evaluation a b` is the actual map
`a*G F → b*F` given by `equalCompositeIso` on `R`, followed by `b*ε`.
`evaluation_tr` proves its compatibility with further pullback using
the canonical datum and composition comparisons.
`evaluation_comp` proves that changing the first lift and then evaluating
is direct evaluation, using the canonical comparison cocycle law.
These constructions and identities require no geometric assumptions.

Assume now that `p` is affine and `F` is quasi-coherent. On the kernel pair
`Q = X ×_Y X`, write `s = fst`, `t = snd`.
The specified affine base-change map
`B(F) : G F → t_*s*F` is invertible. `coaction D` is

`F → t_*t*F → t_*s*F → G F`,

using the unit for `t`, `t_*θ(t,s)`, and `B(F)⁻¹`.
`coaction_comp_baseChange` cancels this last inverse and records the
result after postcomposition with the actual `B(F)`.

`pushforwardBaseChange_eq_unit_comp_counit` gives an alternate formula
for the specified base-change map on any commutative square, without
affineness or quasi-coherence assumptions. It is the unit for the
base-changed map followed by the pushforward of the inverse pullback-square
comparison and the pulled-back counit. The proof uses the published unit
identity for this same base-change map, its naturality, and the right
triangle identity.

Under the affine and quasi-coherent assumptions, this formula and the
adjunction for `t` turn `coaction_comp_baseChange` into
`t*(coaction D) ≫ evaluation t s = θ(t,s)`.
`coaction_evaluation` pulls that equality back along the unique map
from each equal-composite test into the kernel pair. The transport
calculus and naturality of `D` give

`a*(coaction D) ≫ evaluation a b = θ(a,b)`

on every scheme test. At `a = b = id`, this gives the counit law;
`coaction_counit` uses naturality and invertibility of the identity
pullback comparison to express it as the actual equality
`coaction D ≫ ε = id_F`.

`evaluation_jointly_monic` shows that maps into `a*G F` are equal if
all their further pullbacks become equal after the indicated composition
comparison and evaluation at every lift. For this proof it suffices to
use `X ×_Y U` for the base map `a ≫ p`. Postcomposition with the
composition comparison and the affine quasi-coherent base-change
isomorphism detects equality. Under the projection adjunction, the
resulting maps are precisely the evaluated maps in the hypothesis.
The identification uses the alternate counit formula, the square
comparison formula through a common composite, and `compIso_assoc`.

`coaction_compatible` applies joint monicity to the two overlap maps.
After further evaluation, all-test evaluation reduces their equality
to the original cocycle law of `D`. Thus
`a*(coaction D) ≫ E(a,b;R) = θ(a,b) ≫ b*(coaction D)`
for every equal-composite test.

`coaction_coassoc` cancels the invertible composite
`B(G F) ≫ t_*E(s,t;R)`. Here `G F` is quasi-coherent because affine
pushforward and arbitrary pullback preserve quasi-coherence. Base-change
naturality and the overlap compatibility transform one side into
`η_t(F) ≫ t_*t*(coaction D)`; the published base-change unit identity
transforms the other into `coaction D ≫ η_t(G F)`.
Unit naturality equates these expressions. The cocycle cancellation
`θ(t,s) ≫ θ(s,t) = id` is the only additional descent calculation.

Finally, `coalgebra D` has underlying object `F`, structure map
`coaction D`, and the proved counit and coassociativity laws for exactly
`modulePullbackDescentComonad p`. Flatness and surjectivity are not
assumptions of this construction.

The provenance is internal: the proof combines the published
rank-independent datum and transport calculus, canonical equal-composite
pullbacks, specified base-change identities, and affine quasi-coherent
base change. It does not take object effectivity or an atlas as a premise.
Extracting an effective geometric descent structure from the coalgebra
comparison equivalence, descending coherent-family conditions, and proving
`FieldCoherentStackAtlasStatement` remain separate obligations.
