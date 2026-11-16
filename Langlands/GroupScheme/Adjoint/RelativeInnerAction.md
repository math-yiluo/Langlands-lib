# Inner actions of supplied full-centre quotients over arbitrary bases

Worker 682.

This internal derived construction starts with group schemes `G` and `A`
over an arbitrary scheme `S`, a homomorphism `q : G → A`, and the published
predicate `RelativeRoot.IsFppfQuotient (center G) q`. The kernel equality
in that predicate identifies its full range on every test with the full
scheme-theoretic centre. No quotient existence is asserted here.

`conjugation_kernelActsTrivially` uses that range equality to put every
point of the actual kernel in the centre. The all-test centrality
condition implies that conjugation by it is the identity. This lemma
requires no affine or separated hypothesis.

For the remaining constructions, `G → S` is affine and `A → S` is
separated. The structural equation `q ≫ (A → S) = (G → S)` and Mathlib's
`IsAffineHom.of_comp` show that the underlying map of `q` is affine,
hence quasi-compact. Its flatness and surjectivity come from the supplied
fppf quotient predicate. The published fpqc action-descent construction
then gives `RelativeRoot.IsFppfQuotient.innerAction`, an actual bundled
`AutomorphicAction A G`.

`innerAction_restrict` identifies its restriction along `q` with
conjugation as a bundled action. `innerAction_act_lift` evaluates it on
every quotient point with a lift, and the published full-centre
faithfulness theorem proves `innerAction_isFaithful`. The published
uniqueness of descended actions gives `innerAction_unique` and the
existence-and-uniqueness formulation `existsUnique_innerAction`.

All schemes and group schemes lie in an arbitrary common universe.
There is no field, affine-base, quasi-compact-base, reductivity,
smooth-kernel or pointwise-surjectivity assumption. In particular,
affineness of `A → S` suffices for the separatedness hypothesis. A
reductive `G` already supplies the required affine structural map.

The provenance is internal: these results combine the Library's actual
kernel, centre, automorphic action, fpqc action descent and full-centre
faithfulness APIs, with pinned Mathlib's affine-morphism cancellation
against a separated target. No additional external structural theorem
is invoked. The result constructs an action from a supplied quotient;
it proves neither the existence of that quotient nor a quasi-split
inner form.
