# The Haar factor of a Levi conjugation in the intertwining integral

Module `Langlands.Global.AdelicIntertwiningStabilizerModulusStatement` contains one `Prop`-valued
definition, `Langlands.Global.IntertwiningStabilizerModulusStatement`, and no theorems. It
identifies the Haar factor that the closed-quotient change of variables of the intertwining
integral attaches to a point of the target Levi subgroup. This file does not prove the statement.

## Role

The Library's intertwining integral runs over `(V(F) ∩ w U(𝔸) w⁻¹) \ V(𝔸)`
(`IsIwasawaCompact.intertwiningIntegral`). The theorem `intertwiningIntegralConjugation`
(module `AdelicIntertwiningClosedQuotient`) moves a left translate `a` of the external argument
into the integrand when conjugation by `a` preserves `V(𝔸)` and the closed stabilizer
`H = intertwiningAdelicStabilizer p iU (iV ≫ q) w`, the points `v` of `V(𝔸)` with
`w⁻¹ v w ∈ U(𝔸)`. The price is the factor `mulEquivHaarChar α / mulEquivHaarChar αH`, where `α` is
conjugation by `a` on `V(𝔸)` and `αH` its restriction to `H`. For `a` in the image of `M'(𝔸)`, the
module `AdelicIntertwiningHaarOffset` proves that `α` preserves `H`
(`conjAdelic_mem_intertwiningAdelicStabilizer_iff`). The statement here computes the factor.

## Data and hypotheses

- a number field `F` and group schemes `G, P, M, U, Q, M', V` over `F`, with `G`, `P`, `Q`, `V`
  affine and locally of finite type and `V` with affine structure morphism;
- parabolics `p : P → G`, `q : Q → G` (`IsParabolicSubgroup`), geometric unipotent radicals
  `iU : U → P`, `iV : V → Q`, and rational Levi subgroups `l : M → P`, `l' : M' → Q`, with
  `iV ≫ q` a closed immersion;
- `IsConnectedReductive G` and a Weyl conjugation `hw : IsWeylConjugation p l q l' w c`, so that
  `l(c(m)) = w⁻¹ l'(m) w`;
- proofs `hi` that `iU ≫ p` is a closed subgroup, `hVu` that `V` is unipotent, and `hUn`, `hVn` that
  the images of `iU`, `iV` are normal. They are used to build the closed stabilizer, its local
  compactness and the automorphism `αH`, and are consequences of the other hypotheses.

## Conclusion

For every `m ∈ M'(𝔸)`, with `α = EisensteinConstantTerm.conjAdelic q iV hVn (l'(m))` and
`αH = subgroupAutomorphism H α _`,

`mulEquivHaarChar α / mulEquivHaarChar αH = l'(m)^{ρ_Q} · (c ≫ l)(m)^{-ρ_P}`

as complex numbers. Here `x^{λ}` is `parameterPower`, `ρ_Q = halfModulusParameter F Q` is
`½ det(Ad | Lie Q)` and `ρ_P = halfModulusParameter F P`. In the notation of Bernstein–Lapid,
the factor is `δ_Q(m)^{1/2} δ_P(w⁻¹ m w)^{-1/2}`.

## Mathematical content

By the convention of Mathlib's `mulEquivHaarChar`, `mulEquivHaarChar α` is the factor by which
`α` multiplies Haar measure on `V(𝔸)`. For conjugation by a Levi point this is the normalized
absolute value of `det(Ad(m) | Lie V)`, and `mulEquivHaarChar αH` is that of
`det(Ad(m) | Lie (V ∩ w U w⁻¹))`. The ratio is the absolute determinant on
`𝔳 ∩ w 𝔲̄ w⁻¹`, where `𝔲̄` is the opposite of `𝔲`. Since `𝔳̄ ∩ w 𝔲 w⁻¹` is dual to it as an
`M'`-module, this equals
`(|det(Ad(m) | 𝔳)| / |det(Ad(m) | w 𝔲 w⁻¹)|)^{1/2} = δ_Q(m)^{1/2} δ_P(w⁻¹ m w)^{-1/2}`.
On a Levi subgroup, `|det(Ad | Lie Q)|` equals `|det(Ad | 𝔳)|`, because a connected reductive group
has trivial adjoint determinant on its own Lie algebra. Bernstein–Lapid state the result as "the
modulus character of `M_Q` on `(w U_P w⁻¹ ∩ U_Q)(𝔸) \ U_Q(𝔸)` corresponds to `ρ_Q − w ρ_P`", and
deduce it by decomposing `w` into elementary symmetries.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024) (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), the sentence
  after (6.5), p. 201 (TeX lines 1248–1257).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995)
  (`moeglin-waldspurger-1995-spectral-decomposition`), II.1.6, printed pp. 87–88 (chapter PDF
  `06.1_pp_78_100_Definitions.pdf`, pp. 10–11), which Bernstein–Lapid cite for this sentence.
  Proposition (i) there asserts that the intertwining integral lies in the space of the
  parameter `wπ`. That assertion contains this normalization, which is not written out
  separately.

## Provenance

The statement is derived from the cited sentence of Bernstein–Lapid. Its formulation through the
Library's closed stabilizer, `conjAdelic`, `mulEquivHaarChar` and `parameterPower` is internal.
It is the normalization that turns `intertwiningIntegralConjugation` into Bernstein–Lapid (6.5).
