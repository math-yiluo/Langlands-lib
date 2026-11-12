# The uniform Lang–Weil estimate for families with zero-dimensional fibres

Author: Worker 69.

This module states the case `d = 0` of the uniform Lang–Weil estimate in families,
`FamilyLangWeilInDimension 0` from `Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilStatement.lean`.
It is the base case of the Library's Lang–Weil route to Conrad's Lemma 4.6. The module contains
no proof.

## The statement

`FamilyLangWeilZeroStatement` is `FamilyLangWeilInDimension 0`: for every morphism
`f : X ⟶ S` locally of finite type, quasi-compact and geometrically irreducible, with `S` of
finite type over `ℤ` and every fibre of pure dimension `0`, there is `C > 0` such that for every
finite field `κ` and every `s : Spec κ ⟶ S`, the number `N_s` of `x : Spec κ ⟶ X` with
`x ≫ f = s` satisfies `|N_s − (#κ) ^ 0| ≤ C (#κ) ^ (0 − 1/2)`, that is,
`|N_s − 1| ≤ C (#κ) ^ (−1/2)`.

## Relation to the sources

This is the dimension-zero case of `FamilyLangWeilStatement`; see its Markdown for the sources
(Conrad, Lemma 4.6, printed p.12, registered source `conrad-2011-weil-grothendieck-adelic-points`;
Lang and Weil, *Number of points of varieties in finite fields*, Theorem 1, printed p.819, PDF
p.2, registered source `lang-weil-1954-number-of-points`, here with `r = 0`; Tao, *The Lang–Weil
bound*, Theorem 2). Provenance: derived. The case `d = 0` has no separate statement in these
sources; it is named here so that the base case of the induction on `d` can be proved through
its own proof task. The bound is expected to hold with
`N_s = 1` exactly: the image `y` of `s` is a closed point of `S` with finite, hence perfect,
residue field `κ(y) ⊆ κ`, and a geometrically irreducible zero-dimensional scheme of finite type
over a perfect field has exactly one point, with residue field equal to the base field; the same
then holds after base change to `κ`, so `X ×_S Spec κ` has exactly one `κ`-point. This
explanation is not part of the statement.

## Status

Open. A proof is to be supplied through its own focused proof task.
