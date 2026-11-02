# Actual relative Weyl quotients

This construction supplies subgroup primitives for the general reductive Aubert
program. For an actual group `G` and subgroup `T`, `Weyl T` is precisely
`N_G(T) / Z_G(T)`, using the full centralizer. It does not replace the
denominator by `T`. The construction applies to the rational-point subgroup of
a maximal split torus whether the original reductive group is split,
quasisplit, or neither. The identification of that subgroup with such a torus,
the associated relative roots, and Weyl-group finiteness remain structural
obligations; none is asserted by this file.

Aubert, *Dualité dans le groupe de Grothendieck des représentations lisses de
longueur finie* (1995), printed p.2180, actually prints `N_G(T0)/T0` and
`N_{L_I}(T0)/T0`. The present construction uses the full-centralizer quotient
required by this task at general reductive scope. This convention is explicit
in Renard (9 July 2026 edition), V.4.1, printed p.118 / PDF p.124:
`W_G = N_G(A_empty)/Z_G(A_empty) = N_G(A_empty)/M_empty`.
Thus this construction corrects the denominator in the printed Aubert notation;
it does not claim that the two quotients agree in general. The role of the
quotients in Aubert's identities is on printed pp.2181–2182, Theorem 1.7.
The implementation is an internal group-theoretic construction using Mathlib's
actual subgroup normalizers, centralizers, and quotient groups.

`normalizerIn T L` is `N_G(T) ∩ L`. When `T ≤ L`,
`intrinsicNormalizer_map` proves that this is exactly the image in `G` of the
normalizer of `T.subgroupOf L` in `L`. `WeylIn T L` divides that numerator by
its intersection with the full ambient centralizer. If `Z_G(T) ≤ L`, the
denominator is the entire `Z_G(T)` viewed in the numerator, as witnessed by
`centralizer_le_normalizerIn`. Thus a standard Levi containing the minimal Levi
has the required quotient `N_L(T) / Z_G(T)`.

`inclusion` sends the class of a normalizer element in `L` to the class of the
same actual element in `G`. `inclusion_mk` exposes that formula, and
`inclusion_eq_one_iff` and `inclusion_injective` prove that this map embeds the
subgroup quotient. Normality of the restricted denominator follows by pulling
back Mathlib's normal centralizer in the ambient normalizer.

`torusAction` descends actual conjugation on `T` to `Weyl T`.
`torusAction_mk_apply` identifies its value on each representative with
`n * t * n⁻¹`. Its injectivity uses the exact kernel computation
`Subgroup.normalizerMonoidHom_ker`, so this action has no arbitrary relabeling.
It is an action on the actual subgroup; an action on relative roots or
characters requires the separate structural comparison.

`conjugationEquiv` restricts actual conjugation by `g` to an isomorphism
`L ≃* L'` when the image of `L` under that conjugation is `L'`. Its displayed
formula fixes the direction needed later for transport from the associated
Levi to the original Levi in Aubert's Jacquet identity. Choosing a representative
and establishing the relevant subgroup equality remain separate inputs.

Finally, `weylIn_centralizer_subsingleton` proves that the quotient for the
minimal Levi `L_empty = Z_G(T)` is trivial. This includes the empty simple-root
case without a positivity or nonempty-rank assumption. The proof observes that
every numerator element is centralizing, so the denominator is the top subgroup.

These are quotient constructions and elementary comparison proofs, not proofs
of Aubert's identities, reductive structural theorems, or representation-theoretic
premises. They introduce no admissibility, geometric lemma, character
independence, Langlands classification, or induced-class Weyl-conjugacy input.
