# The holomorphic operators of the noncompact picture, formally

## Definitions

- `Hol n`: the polynomials in the coordinates `v` of the lower unipotent group.
- `nbH = 1 + lowMatG v`, `nbInvH` its adjugate, `conjH X = nbH · X · nbInvH`,
  `fieldWH X p = (low(conjH X) · nbH)_p` and `lamH α X = Σ_k α_k (conjH X)_{kk}`.
- `ιP = rename vV : Hol n → Pol n`.
- `opDataH α X`: the operator data `(ιP ∘ fieldWH X, ιP (lamH α X))` of `X`.
- `symbMat`: the elementary matrices `E_{kj}` (for the position `(k, j)`) and `E_{c+1, a}` (for
  the position `(a, c)`).

## Results

- `nbH_map_eval`, `nbInvH_map_eval`, `conjH_map_eval`, `eval_fieldWH`, `eval_lamH`: evaluated at
  `v`, these give `nbMat v`, `(nbMat v)⁻¹`, `conjMat X v`, `fieldW X v` and
  `Σ_k α_k (conjMat X v)_{kk}` (modules `ComplexNoncompactPicture`, `ComplexNoncompactFiltration`).
- `nbH_map_ιP`, `nbInvH_map_ιP`, `conjH_map_ιP`: mapped into `Pol n` they give `nbF`, `nbInvF`,
  `nbF X nbInvF` of `ComplexMomentSymbols`.
- `sum_lw`, `trace_mul_lowMatG_transpose`, `trace_lowMatG_mul`: summation over the strictly lower
  positions and two trace identities.
- `sym_opDataH`: the symbol of `opDataH α X` is `tr(X · Φ)`; `sym_opDataH_single`: for
  `X = E_{kj}` it is `Φ_{jk}`; `sym_opDataH_symbMat`: `sym (opDataH α (symbMat i)) = symb i`.

## Provenance

Internal infrastructure of Task 7064 for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
