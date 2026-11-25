# Reduction of Langlands' spectral decomposition to four analytic ingredients

Module `Langlands.Global.AdelicSpectralDecompositionReduction` states four propositions about
the wave packets of the presented standard parabolics on `[G] = A_G G(F) \ G(𝔸)`. It proves
that together they imply the published `Langlands.Global.SpectralDecompositionStatement`
(Getz–Hahn Theorem 10.5.1). It proves none of the four. The finiteness of the set `S` in the
target comes from `standardParabolicSpectrumFiniteness`, proved in the module
`Langlands.Global.AdelicStandardParabolicFiniteness`, which this module imports.

| Declaration | Kind | Source |
| --- | --- | --- |
| `RelativeWavePacketOrthogonalityStatement` | statement | Lapid 2011, Proposition 2 (empty sum over `Ω(P, P')`); Arthur 2005, Theorem 7.2(b) |
| `RelativeWavePacketAssociationStatement` | statement | Arthur 2005, Theorem 7.2(a), functional equation (7.3); GH §10.5 |
| `RelativeWavePacketCompletenessStatement` | statement | Delorme 2023, Theorem 7.9; Arthur 2005, Theorem 7.2(b), (7.5) |
| `GroupParabolicSpectrumStatement` | statement | GH §10.5, `L²_G([G]) = L²_disc([G])`; the first part of item 2 of the target, verbatim |
| `l2_inner_eq_integral_mul_conj` | theorem (proved) | internal |
| `isOrtho_topologicalClosure_span` | theorem (proved) | internal |
| `isWeylConjugation_symm` | theorem (proved) | internal |
| `and_of_right_of_imp` | theorem (proved) | internal |
| `spectralDecomposition_of_reduction` | theorem (proved) | internal |

## Sources

- Getz–Hahn, *An introduction to automorphic representations* (2024), registered as
  `getz-hahn-2024-automorphic-representations`, §10.5, printed pp.281–282 (PDF pp.293–294):
  the decomposition (10.21) "where the (finite) direct sum is over all association classes
  `𝒫` of parabolic subgroups", the families (10.22) over `i(𝔞_M^G)^*`, the integrals
  (10.24), `L²_𝒫([G])` as the closure of the span of the integrals of compactly supported
  families, the remark that `(𝔞_G^G)^* = {0}` and `L²_G([G]) = L²_disc([G])`, and
  Theorem 10.5.1, with the comment "This is [Art05, Theorem 7.2], except that Arthur
  decomposes `L²(G(F)\G(𝔸_F))` whereas we have decomposed `L²([G])`".
- J. Arthur, *An introduction to the trace formula*, in Clay Math. Proc. 4 (2005), registered
  as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`. Printed pp.33–34 (PDF
  pp.45–46): the Weyl sets `W(𝔞_P, 𝔞_{P'})` and representatives `w_s ∈ G(ℚ)`. Theorem 7.2,
  printed p.35 (PDF p.47). Part (a): the functional equation (7.3) `E(x, M(s, λ)φ, sλ) = E(x, φ, λ)`, and for
  `λ ∈ i𝔞_P^*` both `E(x, φ, λ)` and `M(s, λ)` are analytic and `M(s, λ)` extends to a
  unitary operator. Part (b): the unitary map from the space of Weyl-invariant families onto
  `L²_𝒫(G(ℚ)\G(𝔸))` and the orthogonal direct sum (7.5).
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page = printed page + 9).
  §2, printed pp.311–312: `Ω(P, Q)` as in Arthur 1980, built from the Weyl group
  `Ω = N_G(T₀)/M₀`; for `w ∈ Ω(P, Q)`, `M(w, λ)φ` takes values in a finite-dimensional
  subspace of `A²_Q` determined by the `K`- and `𝔷`-types of `φ`, and
  `E_Q(M(w, λ)φ, wλ) = E(φ, λ)`. Printed p.314 (PDF p.323): Proposition 2, `Θ_{P,φ} ∈ L²(G\G(𝔸))` and the inner product (4)
  `(Θ_{P,φ}, Θ_{P',φ'}) = ∫_{i𝔞_P^*} ∑_{w ∈ Ω(P,P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`;
  Theorem 2 (the isometry `Ē`, "one-half" of Langlands' `L²` decomposition).
- P. Delorme, *On the spectral theorem of Langlands* (2023), registered as
  `delorme-2023-spectral-theorem-langlands`: Theorem 6.1 (Lapid's isometry `Ē`) and
  Lemma 6.2 (a wave packet of one `P` is in the image of `Ē`, by symmetrization), p.22;
  Theorem 7.9, pp.33–35 (published PDF; TeX source 2006.12893): "The image of the map `Ē` of
  Theorem 6.1 is equal to `L²(G(F)\G(𝔸))`."

## Common data

All four statements quantify over the data of `SpectralDecompositionStatement`, unchanged: a
number field `F : Type`; `G` with `IsAffineHom G.X.hom`, `IsAffine G.X.left`,
`LocallyOfFiniteType G.X.hom` and `IsConnectedReductive G`; a subgroup `K` of `G(𝔸)` with
`IsMaximalCompactSubgroup F G K`; a matrix representation `rho` with `IsClosedSubgroup rho`;
`hsmooth`, `hcalc`; and a minimal parabolic `p₀ : P₀ → G` (a closed immersion, `P₀` affine)
with `IsIwasawaCompact p₀ K`. A *presented standard parabolic* is the target's datum
`(P, M, U, A, p, iU, l, a, r, hA, hT)` with its instance arguments, together with
`range p₀ ≤ range p`, `LeviSubgroup.IsGeometricUnipotentRadical iU` and
`hK : IsIwasawaCompact p K`. Its *wave packets* are the functions `Θ : G(𝔸) → ℂ` with
`IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ`, and `L²_P([G])` is
`parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT` (module
`Langlands.Global.AdelicParabolicSpectrum`). A wave packet `Θ` is *square integrable* when
`y ↦ Θ(y.out)` is in `L²([G])`, that is,
`MemLp (fun y => Θ y.out) 2 (RestrictionSplitCentre.canonicalMeasure F G)`. The pairing of two
functions is `∫ y, f y * conj (g y) ∂(canonicalMeasure F G)` on
`[G] = RestrictionSplitCentre.CanonicalQuotient F G`.

The statements quantify only over presented standard parabolics, like the target. Each
statement is weaker for this restriction, except the completeness statement, whose
hypothesis then asks orthogonality only to the wave packets of presented standard
parabolics. Mathematically every standard parabolic has a presentation (Markdown of
`Langlands.Global.AdelicSpectralDecompositionStatement`, "Standard parabolics"), so this does
not change its content. That existence is not proved in the Library.

The sources fix `K` in good position with respect to a minimal Levi subgroup. The statements
here use the `K` of the target, any maximal compact subgroup with `P₀(𝔸)K = G(𝔸)`. The
passage between the two is explained in the paragraph "The compact subgroup" of the target's
Markdown; it is explanatory and not proved here.

## Statements

### `RelativeWavePacketOrthogonalityStatement`

For presented standard parabolics `P = MU` and `P' = M'U'` such that there are no rational
point `w` of `G` and no `c : M' → M` with `IsWeylConjugation p l p' l' w c`, every square
integrable wave packet `Θ` of `P` and every square integrable wave packet `Θ'` of `P'` satisfy
`∫ y, Θ(y.out) · conj Θ'(y.out) = 0`.

Correspondence. Lapid takes `Ω(P, P')` from Arthur 1980. It is Arthur's Weyl set
`W(𝔞_P, 𝔞_{P'})` (Arthur 2005, printed p.33, PDF p.45): the distinct linear isomorphisms
from `𝔞_P` onto `𝔞_{P'}` obtained by restricting elements of the Weyl group
`W₀ = N_G(T₀)/M₀`, each represented by some `w_s ∈ G(F)` (printed p.34, PDF p.46). Such a
representative `w` normalizes `T₀` and maps `A_P` onto `A_{P'}`, hence `M = C_G(A_P)` onto
`M' = C_G(A_{P'})`, so `w M w⁻¹ = M'`. If no rational point conjugates `M` to `M'`, then
`Ω(P, P') = ∅` and the sum (4) of Proposition 2 is empty, so the inner product is `0`. Lapid
works with a fixed Levi subgroup of each standard parabolic; by the paragraph "The choice of
Levi subgroup" of the target's Markdown, the wave packets of `P` do not depend on this choice,
and the hypothesis does not either, since rational Levi subgroups of `P` are conjugate under
`U(F)`.

Lapid, Arthur and Delorme work on `G(F)\G(𝔸)` with parameters in `i𝔞_P^*`; here, as in GH,
the space is `[G]` and the parameters are in `i(𝔞_M^G)^*`. For `a ∈ A_G` (central) and
`λ = λ₁ + λ₂` with `λ₁ ∈ i(𝔞_M^G)^*`, `λ₂ ∈ i𝔞_G^*`, one has
`E(φ, λ)(a g) = e^{⟨λ₂, H_G(a)⟩} E(φ, λ)(g)` and `E(φ, λ) = e^{⟨λ₂, H_G(·)⟩} E(φ, λ₁)`.
So the wave packet on `G(F)\G(𝔸)` of a product `a₁(λ₁) a₂(λ₂) φ` is the product of the
Fourier transform of `a₂`, evaluated at `H_G(g)`, and the wave packet of `a₁ φ` over
`i(𝔞_M^G)^*`, and inner products on `G(F)\G(𝔸) ≅ A_G × [G]` factor accordingly. Choosing
`a₂ ≠ 0` gives the statement on `[G]`. This is explanatory and not proved here.

### `RelativeWavePacketAssociationStatement`

For presented standard parabolics `P = MU` and `P' = M'U'`, a rational point `w` and
`c : M' → M` with `IsWeylConjugation p l p' l' w c` (that is, `c` is an isomorphism and
`l(c(m')) = w⁻¹ l'(m') w`, so `w M w⁻¹ = M'`), and a wave packet `Θ` of `P`: every
`f ∈ L²([G])` with `f = Θ ∘ out` almost everywhere lies in `L²_{P'}([G])`.

Correspondence. This is the step that identifies the closed span of the wave packets of one
`P` with GH's `L²_𝒫([G])`, which GH and Arthur define with families over all `P ∈ 𝒫` (see
"Single parabolics instead of families" in the Markdown of
`Langlands.Global.AdelicParabolicSpectrum`). For `Θ = ∫ E(φ(λ), λ) dλ` over
`λ ∈ i(𝔞_M^G)^*`, the functional equation (7.3) and the substitution `λ' = wλ`, a linear
isomorphism from `i(𝔞_M^G)^*` onto `i(𝔞_{M'}^G)^*`, give
`Θ = ∫ E(φ'(λ'), λ') dλ'` (up to the constant Jacobian of the coordinates) with
`φ'(λ') = M(w, w⁻¹λ') φ(w⁻¹λ')`. Since `M(w, λ)` is analytic on `i𝔞_P^*` (Theorem 7.2(a)),
`φ'` is smooth and compactly supported. It takes values in a finite-dimensional subspace of
`A²_{P'}`: Lapid (§2, printed p.312, PDF p.321) records that `M(w, λ)φ` takes values in a
finite-dimensional subspace of `A²_{P'}` determined by the `K`- and `𝔷`-types of `φ`. So `Θ`
is a wave packet of `P'`, and its class lies in `L²_{P'}([G])`. The sources state this for
Weyl elements `w ∈ Ω(P, P')` and the Levi subgroups containing a fixed minimal Levi `M₀`. A
general rational `w` with `w M w⁻¹ = M'` reduces to this case: after replacing `M` and `M'` by
these Levi subgroups (paragraph "The choice of Levi subgroup" of the target's Markdown),
`w T₀ w⁻¹` is a maximal split torus of `M'`, hence `m w T₀ w⁻¹ m⁻¹ = T₀` for some
`m ∈ M'(F)`, and `m w` represents an element of `Ω(P, P')`. This is explanatory and not proved
here. The statement asks for one direction only; `spectralDecomposition_of_reduction` obtains
the other from `isWeylConjugation_symm`.

### `RelativeWavePacketCompletenessStatement`

For `f : [G] → ℂ` in `L²([G])`: if `∫ y, f y · conj Θ(y.out) = 0` for every square integrable
wave packet `Θ` of every presented standard parabolic, then `f = 0` almost everywhere.

Correspondence. Delorme's Theorem 7.9 says that the image of Lapid's isometry `Ē` is all of
`L²(G(F)\G(𝔸))`. That image is the closure of the span of the wave packets `Θ_{P,φ}` of the
standard parabolics `P ⊇ P₀`: each `Ē(F)` is a finite sum of such wave packets, and each
`Θ_{P,φ}` is `Ē` of its symmetrization (Delorme, Lemma 6.2). So a function on `G(F)\G(𝔸)`
orthogonal to all `Θ_{P,φ}` is zero; this is the surjectivity half of Arthur's
Theorem 7.2(b). The statement on `[G]` follows by the factorization described under the
orthogonality statement: if `f ∈ L²([G])` is orthogonal to all wave packets over
`i(𝔞_M^G)^*`, then `h ⊗ f` is orthogonal to all wave packets of product functions
`a₁ ⊗ a₂`, for every `h ∈ L²(A_G)`. These span a dense subspace of the image of `Ē`, because
`‖Θ_{P,φ}‖² ≤ |Ω(P, P)| ∫ ‖φ(λ)‖² dλ`, by (4) with `P' = P`, the Cauchy–Schwarz inequality
and the unitarity of `M(w, λ)` for `λ ∈ i𝔞_P^*` (Arthur, Theorem 7.2(a)). This is explanatory
and not proved here.

### `GroupParabolicSpectrumStatement`

For a presented standard parabolic with `p` an isomorphism,
`parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT = discreteSpectrum F G hG`.

Correspondence. This is word for word the first part of item 2 of the target. GH have
`L²_G([G]) = L²_disc([G])` by definition. Here it is a theorem, explained in the Markdown of
`Langlands.Global.AdelicParabolicSpectrum` (case `P = G`) and in the target's Markdown
(paragraph "`L²_disc`"): the wave packets of `G` are finite sums of square-integrable
automorphic forms on `[G]`, and their closed span is the discrete part of the right regular
representation. It is kept as a separate premise because proving it requires the theory of
square-integrable automorphic forms.

## Helper theorems

- `l2_inner_eq_integral_mul_conj`: if `u =ᵐ f` and `v =ᵐ g` for `u v : Lp ℂ 2 m`, then
  `inner ℂ v u = ∫ a, f a * conj (g a) ∂m`.
- `isOrtho_topologicalClosure_span`: in a complex inner product space, if `⟪u, v⟫ = 0` for all
  `u ∈ s` and `v ∈ t`, then the closures of the spans of `s` and `t` are orthogonal
  (`Submodule.IsOrtho`).
- `isWeylConjugation_symm`: if `IsWeylConjugation p l q l' w c`, then
  `IsWeylConjugation q l' p l w⁻¹ (inv c)`. Proof: `(G.innerIso w⁻¹).inv = (G.innerIso w).hom`
  by `innerIso_inv_hom`, then cancel `c` in `comp_eq`.
- `and_of_right_of_imp`: from `b` and `b → a`, conclude `a ∧ b`.

## The reduction theorem

`spectralDecomposition_of_reduction` takes `RelativeWavePacketOrthogonalityStatement`,
`RelativeWavePacketAssociationStatement`, `RelativeWavePacketCompletenessStatement` and
`GroupParabolicSpectrumStatement` and proves `SpectralDecompositionStatement`.

Proof (as implemented). Introduce the data of the target and the set `S`. With
`and_of_right_of_imp`, item 2 is proved first and then used for item 1.

1. Item 2, for presented standard parabolics `P` and `P'`.
   - If `p` is an isomorphism, `GroupParabolicSpectrumStatement` gives
     `L²_P([G]) = L²_disc([G])`.
   - If `IsWeylConjugation p l p' l' w c`, prove both inclusions with
     `Submodule.topologicalClosure_minimal` and `Submodule.span_le`: every generator of
     `L²_P([G])`, the class of a wave packet of `P`, lies in the closed subspace
     `L²_{P'}([G])` by the association statement. The reverse inclusion uses the association
     statement with `P` and `P'` exchanged, for `w⁻¹` and `inv c` (`isWeylConjugation_symm`).
   - If there are no such `w` and `c`, `isOrtho_topologicalClosure_span` reduces the
     orthogonality to generators: classes `u` and `v` of wave packets `Θ` and `Θ'`.
     `l2_inner_eq_integral_mul_conj` turns `⟪u, v⟫ = 0` into the pairing of `Θ` and `Θ'`.
     The orthogonality statement gives it, with square integrability from `Lp.memLp u` and
     `Lp.memLp v`.
2. Item 1, finiteness: `standardParabolicSpectrumFiniteness` gives `S.Finite` from the
   association part of item 2.
3. Item 1, density: by `Submodule.topologicalClosure_eq_top_iff` it suffices that every `x`
   orthogonal to `sSup S` is `0`. For a square integrable wave packet `Θ` of a presented
   standard parabolic, its class `hΘL.toLp` lies in `L²_P([G]) ∈ S`, hence in `sSup S`. So
   `⟪hΘL.toLp, x⟫ = 0`, which `l2_inner_eq_integral_mul_conj` turns into
   `∫ y, x y * conj Θ(y.out) = 0`. The completeness statement gives `x = 0` almost
   everywhere, so `x = 0` in `L²([G])`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Remarks

- Square integrability. The premises require the wave packets to be square integrable on
  `[G]`. By Lapid's Proposition 2 every wave packet is, so mathematically this restricts
  nothing. It makes the premises weaker, and `parabolicSpectrum` only contains classes of
  square integrable wave packets anyway.
- Integrals. All integrals are Bochner integrals. In the orthogonality statement and in the
  hypothesis of the completeness statement, the integrands are integrable by Cauchy–Schwarz,
  because both factors are in `L²([G])`. So no hypothesis holds only because a divergent
  integral has the value `0`.
- `IsRelativeWavePacket` requires the continuations `E j` to be meromorphic on all of
  `X^*(P) ⊗ ℂ` and equal to the Eisenstein series for `Re λ` sufficiently regular, so they are
  the meromorphic continuations of the Eisenstein series (Markdown of
  `Langlands.Global.AdelicParabolicSpectrum`).

## Scope

None of the four statements is proved here. Their expected inputs:

- orthogonality: Lapid's Proposition 2 (Arthur's asymptotic inner product formula, Lapid
  Theorem 1 and Proposition 1) and the passage from `G(F)\G(𝔸)` to `[G]`;
- association: meromorphic continuation, functional equation and unitarity of the
  intertwining operators on `i𝔞_P^*` (Arthur's Theorem 7.2(a));
- completeness: Delorme's Theorem 7.9 and its inputs;
- `GroupParabolicSpectrumStatement`: the structure of the discrete spectrum, namely that each
  square-integrable automorphic form generates a finite sum of irreducible subrepresentations,
  and that their `K`-finite, `𝔷`-finite vectors are dense.
