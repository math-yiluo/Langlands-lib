# The induction step of the uniform Lang–Weil estimate by hyperplane slicing

Author: Worker 69.

This module states the induction step of the Library's Lang–Weil route to Conrad's Lemma 4.6:
the uniform Lang–Weil estimate in fibre dimension `d + 1` implies it in fibre dimension `d + 2`,
given Bertini's theorem for the generic hyperplane section and the uniform upper bound for point
counts in families. The module contains no proof.

## The statement

`FamilyLangWeilSlicingStatement` is the implication

`BertiniGenericHyperplaneStatement → FamilyPointUpperBoundStatement →`
`  ∀ d : ℕ, FamilyLangWeilInDimension (d + 1) → FamilyLangWeilInDimension (d + 2)`,

all in the same universe `u`:

- `BertiniGenericHyperplaneStatement` (`Langlands/AlgebraicGeometry/LangWeil/BertiniGenericHyperplaneStatement.lean`):
  the section of a geometrically irreducible affine `k`-scheme of finite type and dimension at
  least `2` by the generic affine hyperplane is geometrically irreducible over `k(a_*, a_0, …)`;
- `FamilyPointUpperBoundStatement` (`Langlands/AlgebraicGeometry/LangWeil/FamilyPointUpperBoundStatement.lean`):
  the uniform bound `C (#κ) ^ e` for points over `κ`-points whose fibre has dimension at most
  `e`;
- `FamilyLangWeilInDimension` (`Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilStatement.lean`):
  the uniform Lang–Weil estimate for geometrically irreducible families with fibres of pure
  dimension `d`, at all `κ`-points of a base of finite type over `ℤ`.

The hypothesis `FamilyLangWeilInDimension (d + 1)` is used for families over arbitrary bases of
finite type over `ℤ`, in particular over parameter spaces of hyperplanes.

## Relation to the sources

Provenance: derived. This is the induction step of the proof of Theorem 1 of Serge Lang and
André Weil, *Number of points of varieties in finite fields* (Amer. J. Math. 76 (1954); registered
source `lang-weil-1954-number-of-points`; PDF page = printed page − 817), printed pp.822–823
(PDF pp.5–6): for `V` of dimension `r ≥ 2` not contained in a hyperplane, count the pairs
`((x), H)` of a rational point `(x)` of `V` and a rational hyperplane `H` through it in two ways,
`N K_n = ∑_H N_{V·H}`; for `H` outside the set `R` of hyperplanes with `V·H` not a variety, apply
the induction hypothesis to the variety `V·H` of dimension `r − 1`; bound the hyperplanes in `R`
by Lemma 2 (printed p.821, PDF p.4: `N_R ≤ A_2 q^{n−1}`) and the points of each `V·H` with
`H ∈ R` by Lemma 1 (printed p.820). Lang–Weil obtain the uniformity of the exceptional set `R`
from Chow coordinates; here it comes from applying the statements to families over arbitrary
bases of finite type over `ℤ`.

The same step is in Terence Tao, *The Lang–Weil bound* (registered
source `tao-2012-lang-weil-bound`), Section 2: for `dim V ≥ 2`, a generic affine hyperplane
section `V ∩ H` is geometrically irreducible of dimension `dim V − 1` (Lemma 6, Bertini), the
hyperplanes over `F` failing this lie in a proper subvariety of bounded complexity and are few by
Lemma 1, and counting pairs `(x, H)` with `x ∈ V(F) ∩ H` (Lemma 7, or Remark 2 with the crude
bound of Lemma 1 for the exceptional `H`) transfers the estimate from the slices to `V`. Bertini's
theorem is taken in the form of Stacks Project, Lemma 37.32.3 (Tag 0G4F). Uniformity in the
family replaces Tao's bounded complexity.

## Expected proof route

The proof is not part of this module. A natural route: by Noetherian induction it suffices to
treat a dense open of an integral affine base `S` and a closed subscheme `X ⊆ 𝐀ⁿ_S` (an affine
open dense in the fibres; the rest has smaller fibre dimension and is handled by the upper
bound). Let `X' ⊆ X ×_S S'` with `S' = 𝐀^{n+1}_S` be the universal hyperplane section. Over the
generic point of `S'` its fibre is the generic hyperplane section of the generic fibre of `X`,
geometrically irreducible by Bertini, so by Stacks 0559 (proved in the Library as
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.finiteTypeGeometricallyIrreducibleGenericSpreading`)
and dimension theory there is an open `W ⊆ S'` over which `X'` is geometrically irreducible with
fibres of pure dimension `d + 1`. Apply `FamilyLangWeilInDimension (d + 1)` to `X'` over `W`. For
`s : Spec κ ⟶ S`, the number of parameters `(a_*, a) ∈ κ^{n+1}` outside `W` is `O((#κ)^n)` by
the upper bound; a slice not containing `X_s` has dimension at most `d + 1`; the parameters whose
hyperplane contains `X_s` number at most `(#κ)^{n−1}`. Summing `#(X_s ∩ H)(κ)` over all
parameters with `a ≠ 0` gives `#X_s(κ) · ((#κ)^n − 1)`, and comparing the two evaluations of the
sum gives the estimate for `X_s`.

## Status

Open. A proof is to be supplied through its own focused proof task.
