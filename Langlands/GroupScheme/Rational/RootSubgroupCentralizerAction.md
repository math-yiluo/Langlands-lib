# Actions fixing a torus and intrinsic root subgroups

This internal construction induces an actual action on an intrinsic root
subgroup from an action fixing its defining commutative group map. It then
applies to conjugation on an ambient normalized subgroup. Over any field, if
both the acting group and the represented root group are vector groups of
dimension one, the ambient conjugation action on that root group is trivial
on every test scheme and every refinement.

## General action and root stability

Let `B` be any scheme, `S` a commutative group scheme over `B`, and `H`, `K`
group schemes over `B`. Let `b : AutomorphicAction K H` be an actual action and
`s : S.toGrp ⟶ H` an actual homomorphism. Assume that every point of `K` fixes
every point of the image of `s`, on every relative test scheme. No torus,
splitting, field, or monomorphism hypothesis on `s` is needed here.

For a character `α` of `S`, `orbit_act_of_fixes_torus` proves that the action
commutes with the `s`-conjugation orbit map. The proof uses the action's
multiplication and inverse laws and its fixedness on the two `S` factors.
`IsOrbitExtension.act_of_fixes_torus` acts on the same affine-line extension,
with the acting point pulled back from the original test scheme. Naturality
preserves its orbit equation and `evalZero_act` preserves its identity value
at zero. Consequently `subgroup_isStable_of_fixes_torus` proves stability of
the entire intrinsic root functor `subgroup s α`.

Given an actual representative `j : V ⟶ H` of that root functor,
`rootActionOfFixesTorus` applies the represented stable-subgroup construction
to produce an actual `AutomorphicAction K V`. Its companion
`rootActionOfFixesTorus_act_comp` identifies its composite with `j` with the
original action on `H`. Representability, including monicity of `j`, is an
explicit premise; the construction does not assert existence of a vector
parametrization of any root group.

## Ambient conjugation

Let `h : H ⟶ G` and `a : K ⟶ G` be actual group homomorphisms. Assume that `h`
is a monomorphism of relative schemes, that `range h` is normalized by
`range a` on every test scheme, and that `range a` is contained in the full
conjugation-fixed subgroup for `s ≫ h`. Thus the image of `K` centralizes the
image of `S` on all tests. These premises in particular apply to a closed
normal inclusion `h` and any subgroup centralizing this image.

`normalizedConjugation_fixes_torus` proves that the published actual action
`ofNormalizedConjugation h a hn` fixes `s`. It composes with the monomorphism
`h`, uses the ambient conjugation formula, and reverses the commutation
equality supplied by the centralizer premise. Cancelling `h` proves the
required equality in `H`.

`rootActionOfTorusCentralizer` then constructs an actual action of `K` on
any supplied representative `j : V ⟶ H` of `subgroup s α`.
`rootActionOfTorusCentralizer_act_comp` proves that its composite with
`j ≫ h` is exactly conjugation by the original point of `K` in `G`.

## Vector lines and scope

Over `Spec k` for any field `k : Type u`, assume explicitly that `K` and `V`
are vector groups of dimension one. The published vector-line action
rigidity theorem identifies the induced action with the trivial action.
`act_root_eq_of_vectorLines` therefore fixes every represented root point,
and `subgroup_le_fixedSubgroup_of_vectorLines` proves fixedness of the whole
intrinsic root functor after every refinement. In the ambient situation,
`range_root_comp_le_centralizer_of_vectorLines` proves
`range (j ≫ h) ≤ (AutomorphicAction.conjugation a).fixedSubgroup`.
The proof uses the same actual representing inclusion and ambient action
equation, so it retains all relative schemes, including nonreduced tests.

The constructions and proofs are internally derived from orbit extensions,
represented-subgroup actions, normalized conjugation, and vector-line
rigidity. They impose no characteristic restriction. They do not prove
root-group dimension one, vector-group structure for a reductive root,
generation by roots, centralization of all of `H`, the full normal-root
dichotomy, or the host almost-simple-generation theorem. Those remaining
structural obligations are not supplied by this contribution.
