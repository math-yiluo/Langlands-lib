# Tadić's Theorem A.10: the exhaustion from its ingredients

Author: Worker 1792. It uses Worker 1745's `TadicXBlockAdapters` (members of
`X_k` are Tadić building blocks once rectangular socles of rank at most `k` are
Speh representations). Module
`Langlands.Representation.Classification.TadicExhaustionAssembly`, namespace
`Langlands.Classification`. The theorems take published propositions as
explicit hypotheses; there are no axioms and no `sorry`.

The hypotheses used are `TadicBlockReduction` (Lemma 4.8(ii)),
`TadicRectangleHeadSocleDistinct` (Lemma 6.3), `IrreducibleLanglandsHeadProduct`
(Corollary A.6(ii)), `SpehUnitarizability` (Theorem A.8) and
`MultisegmentHeadClassification`. The proof follows
Tadić's proof of Theorem A.10 (1986, printed pp.378–379).

## Declarations

- `isUnitarizable_of_isSpeh`: with `SpehUnitarizability`, a representation
  isomorphic (after the rank transport `hD ▸`) to a Speh representation is
  unitarizable.
- `TadicSocleHeadDuality.isZelevinskySocle_of_isLanglandsHead`: assume
  A.10(iii) up to rank `m`, Lemma 4.8(ii), Corollary A.6(ii), Theorem A.8 and the
  classification. For unitary `ρ` and `n, d > 0`, a Langlands head `π` of
  `a(d,n)^ρ` on `GL_(m+1)` is a Zelevinsky socle of `a(n,d)^ρ` or of
  `a(d,n)^ρ`. This is Tadić's step from "`L(a(n,d)^ρ)` is unitarizable" to
  "`L(a(n,d)^ρ) ∈ {⟨a(n,d)^ρ⟩, ⟨a(d,n)^ρ⟩}`".
  Proof: `π` is irreducible and, being a Speh representation
  (`exists_isSpeh_of_isLanglandsHead`), unitarizable. If `π` is a Zelevinsky socle
  of some `a(u,v)^τ` with `τ` unitary, then
  `tadic_parameters_of_isZelevinskySocle_of_isLanglandsHead` gives `τ = ρ` and
  `{u,v} = {n,d}`. Otherwise Lemma 4.8(ii), applicable because `(U^m)` follows
  from A.10(iii) up to rank `m` and Theorem A.8, writes `π` as a product of members
  of `X_m`, which `TadicSocleHeadDuality.not_iso_xBlockProduct` excludes.
- `TadicSocleHeadDuality.succ`: A.10(iii) up to rank `m` implies it up to rank
  `m + 1`. Let `σ` be a Zelevinsky socle of `a(n,d)^ρ` on `GL_(m+1)` and `π` a
  Langlands head of `a(d,n)^ρ` (`exists_isLanglandsHead_tadicMultisegment`). By the
  previous step:
  - if `π` is a socle of `a(n,d)^ρ`, then `π ≅ σ`
    (`nonempty_iso_of_isZelevinskySocle`), so `σ` is a head of `a(d,n)^ρ`;
  - if `π` is a socle of `a(d,n)^ρ` and `n = d`, the same applies;
  - if `π` is a socle of `a(d,n)^ρ` and `d < n`, Lemma 6.3 for `a(d,n)^ρ` is
    contradicted;
  - if `π` is a socle of `a(d,n)^ρ` and `n < d`, take a Langlands head `π'` of
    `a(n,d)^ρ` (again `exists_isLanglandsHead_tadicMultisegment`). By the
    previous step `π'` is a socle of `a(n,d)^ρ`, which
    contradicts Lemma 6.3, or of `a(d,n)^ρ`. In the latter case `π ≅ π'`, and
    the classification gives `a(d,n)^ρ = a(n,d)^ρ`; comparing numbers of
    segments gives `d = n`, a contradiction.
- `tadicSocleHeadDuality`: A.10(iii) in every rank, by induction from
  `TadicSocleHeadDuality.zero`.
- `tadicUnitaryDualExhaustion_of_ingredients`: from
  `TadicExhaustionLemmaStatements F T` (the conjunction of Lemma 4.8(ii), Lemma 6.3
  and Corollary A.6(ii)), `SpehUnitarizability F T` and
  `MultisegmentHeadClassification F T`, the
  published `TadicUnitaryDualExhaustion F T` follows. Let `π` on `GL_(n+1)` be
  irreducible and unitarizable. If `π` is a Zelevinsky socle of some `a(u,v)^ρ`
  with `ρ` unitary, it lies in `X_(n+1)`, hence is a Tadić building block
  (Worker 1745's `isTadicBuildingBlock_of_isTadicXBlock` with
  `TadicSocleHeadDuality.spehComparison`), and the one-block product is the
  required factorization. Otherwise Lemma 4.8(ii) with `(U^n)` writes `π` as a
  product of members of `X_n`, each a Tadić building block in the same way.
