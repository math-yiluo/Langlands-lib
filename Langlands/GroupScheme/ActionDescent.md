# Descent of automorphic actions through an fpqc homomorphism

This internal derived construction starts with an actual automorphic action of
`H` on `G`, a group-scheme homomorphism `q : H → Q`, and the condition that the
scheme-theoretic kernel of `q` acts trivially on every test scheme over the base.
It assumes `q` is quasi-compact, flat and surjective on underlying schemes.

`KernelActsTrivially` refers to the published actual kernel and its inclusion.
The equal-image lemma divides two acting points, lifts their quotient through
the kernel pullback, and uses the trivial kernel action. The action morphism
therefore coequalizes the relations of `q × id_G`. Mathlib's fpqc effective
epimorphism instance and `EffectiveEpi.desc` produce `quotientActionSchemeHom`.
Cancellation of that epimorphism proves the structural map equation, yielding
`quotientActionHom` over the original base. Its composite with `q × id_G` is the
original action morphism; `lift_quotientActionHom` gives the all-test lift formula.

`quotientAction` bundles this descended morphism as an actual
`AutomorphicAction Q G`. The unit law follows from the lift formula applied to
the unit of `H`. To prove the multiplication law in the acting variable, the
implementation pulls back `q` twice, successively lifting the two acting
points. To prove compatibility with multiplication in `G`, it pulls back `q`
once. On these covers, naturality and `lift_quotientActionHom` reduce the desired
identities to the original action laws.

The local-lift equality criterion `hom_ext_of_local_quotient_lift` constructs the
pullback of the underlying morphism of `q` along any chosen `Q`-point of a test
scheme. It gives this pullback its compatible structure over the original base.
Its projection is an epimorphism, since it is again quasi-compact, flat and
surjective. Cancellation proves the equality on the original test. There is no
assumption that `H(T) → Q(T)` is surjective.

`quotientAction_act_lift` is the all-test action formula.
`quotientAction_restrict_hom` and `quotientAction_restrict` identify the
restriction with the original action, respectively on morphisms and as bundled
actions. `quotientAction_hom_unique` cancels the effective epimorphism
`q × id_G` on underlying schemes, and `quotientAction_unique` gives uniqueness
as a bundled action. The elementary `ext_hom` lemma uses proof irrelevance for
the three action laws.

Conversely, `restrict_kernelActsTrivially` proves that the restriction of any
action of `Q` makes the actual kernel of `q` act trivially. It uses the existing
kernel point equivalence to identify the composite acting point with the unit.
Together these constructions give `exists_quotientAction_iff`: for the specified
fpqc homomorphism, an action descends exactly when its kernel acts trivially.

This is an internal derived construction from the published `AutomorphicAction`
and scheme-theoretic kernel APIs, together with pinned Mathlib's fpqc effective
epimorphism and `EffectiveEpi.desc` APIs. The underlying descent instance comes
from `Mathlib.AlgebraicGeometry.Sites.Fpqc`; compatibility, action laws and
uniqueness are proved here by the preceding cancellation and local-lift
arguments. No new external structural theorem is asserted.

The base scheme and all three group schemes are arbitrary within the common
universe. The only geometric assumptions on `q` are quasi-compactness, flatness
and surjectivity of its underlying scheme morphism. Smoothness of its kernel,
affineness of the target groups, finite type, reductivity and a field base are
not assumed. No quotient group scheme is constructed: `Q` and `q` are inputs.
In particular, this unit does not prove the existence of a torus quotient by a
character kernel or identify such a quotient with the multiplicative group.
