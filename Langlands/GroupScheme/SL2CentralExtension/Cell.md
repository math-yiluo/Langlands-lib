# The splitting on the open cell, glued over `SL₂`

Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1, proof pp. 129-131). Throughout, `X : Ext S` is the point-level data
from `Setup`. The results that use Conrad's relation (4.3.1) assume `hD : X.DComm`.

Conrad defines the section on the open cell `Ω = V × D × U` by `y′(a) h′(t) x′(b)`. He shows
that it respects multiplication where defined, and extends it to `SL₂` by schematic density. The
implementation works with points over arbitrary test schemes instead. Fppf-locally, every
matrix `m` has a translate `x(r) m` in the open cell. The section is defined there as
`x′(-r) · y′(a) h′(t) x′(b)`. These local values are independent of the choices and glue.

## Contents

- `Mat.yhx_add` (`y(a) h(t) x(b) · x(c) = y(a) h(t) x(b + c)`) and `Mat.yhx_zero_one`
  (`y(0) h(1) x(c) = x(c)`).
- `Loc.exists_cell₂`, `Loc.exists_cell`: for matrices `m`, `m′` over `T`, fppf-locally there is
  `r` such that both `x(r) m` and `x(r) m′` lie in the open cell. The entry `(x(r) m)₀₀` is
  `m₀₀ + r m₁₀`. The first column `(m₀₀, m₁₀)` is unimodular, so this linear polynomial in `r`
  is nowhere degenerate. Hence the product of the polynomials for `m` and `m′` takes a unit
  value locally (`Loc.exists_isUnit_eval`).
- `form a t b = y′(a) h′(t) x′(b)` lifts `yhx a t b` (`Q_form`). It is natural (`form_res`). Also
  `xl_eq_form` (`x′(c) = form 0 1 c`) and `form_mul_xl`.
- `form_mul_exists`: if `s = 1 + b₁a₂` is a unit, the product `form a₁ t₁ b₁ · form a₂ t₂ b₂` is
  again of the form `form a t b`. The proof uses `xl_yl` (relation (4.3.1)), `hl_yl`, `xl_hl` and
  `hl_mul`.
- `form_mul_eq`: if `yhx a₁ t₁ b₁ · yhx a₂ t₂ b₂ = yhx a t b`, then
  `form a₁ t₁ b₁ · form a₂ t₂ b₂ = form a t b`. Comparing upper-left entries shows that
  `1 + b₁a₂` is a unit. `form_mul_exists` applies, and the parameters agree by
  `Mat.yhx_injective`.
- `CellRep m e`: `e = x′(-r) · form a t b` for some `r, a, t, b` with
  `x(r) m = yhx a t b`. Results: `exists_cellRep`, `cellRep_res`, `Q_of_cellRep` (`Q e = m`) and
  `cellRep_unique` (two representatives of `m` are equal, by `form_mul_eq` applied to
  `x(r′ - r) · yhx a t b = yhx a′ t′ b′`).
- `sigmaFun hD m`: the representatives glue (`Loc.glue`, `exists_sigma`) to a point of `E`,
  defined by choice and characterized by `sigmaFun_spec`. It is natural (`sigmaFun_res`) and
  lifts `m` (`Q_sigmaFun`). It is multiplicative (`sigmaFun_mul`). Locally, choose `r` with
  `x(r) m₁` and `x(r) m₁ m₂` in the cell and `p` with `x(p) m₂` in the cell. Then
  `form_mul_xl` and `form_mul_eq` compare the representatives.
- `sigma hD T : Mat.SL2 Γ(T.left, ⊤) →* (T ⟶ E.X)` is the resulting group homomorphism, with
  `sigma_apply`, `sigma_res` (naturality: `k ≫ sigma hD T m = sigma hD V (res k m)`) and
  `Q_sigma` (`Q (sigma hD T m) = m`).
