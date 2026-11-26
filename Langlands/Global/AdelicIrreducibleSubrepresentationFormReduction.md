# Irreducible subrepresentations of `L²([G])`: reduction to the automorphy of `K`-finite vectors

Module `Langlands.Global.AdelicIrreducibleSubrepresentationFormReduction` reduces the published
`Langlands.Global.IrreducibleSubrepresentationFormSpectrumStatement` (module
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction`) to one proposition about `L²([G])` that
does not mention parabolic data,
`IrreducibleSubrepresentationFiniteVectorAutomorphyStatement`: in an irreducible
subrepresentation of `L²([G])`, every `K`-finite vector is the class of an automorphic form on
`G(F) \ G(𝔸)` that is left invariant under `A_G`. Automorphic forms are taken in the
smoothness and finite-level convention of Borel–Jacquet, which the Library's
`IsAutomorphicFunctionOn` implements (see "Smoothness convention" below).

It proves the comparison `isSquareIntegrableInducedForm_of_isIso`: for a presented parabolic
`p : P → G` that is an isomorphism onto a connected reductive group, such automorphic forms belong
to Lapid's `A²_P` (`IsSquareIntegrableInducedForm`). With it and the density of the `K`-finite
vectors (`subset_closure_canonicalL2FiniteVectors`, module
`Langlands.Global.AdelicL2FiniteVectorDensity`), the theorem
`irreducibleSubrepresentationFormSpectrum_of_finiteVectorAutomorphy` derives
`IrreducibleSubrepresentationFormSpectrumStatement` from the proposition. The module does not
prove the proposition.

| Declaration | Kind | Source |
| --- | --- | --- |
| `map_eq_one_of_isGeometricUnipotentRadical` | theorem (proved) | internal |
| `parabolicQuotientSubgroup_le_rationalSubgroup_of_isIso` | theorem (proved) | internal |
| `modulusParameter_eq_zero` | theorem (proved) | internal |
| `halfModulusParameter_eq_zero` | theorem (proved) | internal |
| `isSplitComponentEquivariant_of_isIso` | theorem (proved) | internal |
| `integrable_iwasawa_of_isIso` | theorem (proved) | internal |
| `isSquareIntegrableInducedForm_of_isIso` | theorem (proved) | internal |
| `IrreducibleSubrepresentationFiniteVectorAutomorphyStatement` | statement | derived: the assertion underlying Getz–Hahn Theorem 6.6.4 (with the errata), in the Borel–Jacquet §§4.1–4.2 convention |
| `irreducibleSubrepresentationFormSpectrum_of_finiteVectorAutomorphy` | theorem (proved) | internal |

All names are in the namespace `Langlands.Global`.

## Sources

Page numbers are printed pages, with one-based PDF pages in parentheses.

- J. R. Getz and H. Hahn, *An introduction to automorphic representations* (2024), registered
  as `getz-hahn-2024-automorphic-representations`:
  - Theorem 6.6.2, pp.170–171 (PDF pp.184–185): the `K`-finite vectors of an irreducible unitary
    representation of `G(𝔸)` form an admissible module.
  - Theorem 6.6.4 with its proof, p.172 (PDF p.186): the `K`-finite vectors of a discrete
    automorphic representation, that is of an irreducible subrepresentation `V` of `L²([G])`,
    are automorphic forms ("it suffices to show that `V_fin` lies in `A_{A_G}`").
  - Lemma 9.7.2 with its proof, pp.264–265 (PDF pp.276–277): the `K`-finite vectors of an
    irreducible unitary representation of `A_G \ G(𝔸)` are dense, with a reproducing function
    `π(f)ϕ = ϕ`, `f ∈ C_c^∞(A_G \ G(𝔸))`, for each of them; the proof takes the normalized
    characteristic function of a compact open subgroup at the finite places and, at the
    archimedean place, Proposition 4.5.6, p.122 (PDF p.138).
  - (6.1), p.158 (PDF p.172): `C^∞(A_G \ G(𝔸))` is the algebraic tensor product
    `C^∞(A_G \ G(F_∞)) ⊗ C^∞(G(𝔸^∞))`, and likewise for `C_c^∞`.
  - Definition 6.3.3, p.163 (PDF p.177): an automorphic form is a smooth function (in the sense
    of (6.1)) of moderate growth that is left `G(F)`-invariant, `K`-finite and `Z(𝔤)`-finite.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, Corvallis
  Part I (1979), registered as `borel-jacquet-1979-automorphic`:
  - §3.2, p.194 (PDF p.189): the idempotent `e_L` of a compact open subgroup `L` of `G(𝔸_f)`;
    `f * e_L = f` if and only if `f` is right invariant under `L`.
  - §4.1, p.194 (PDF p.189): a function on `G(𝔸)` is smooth if it is continuous, `C^∞` in the
    archimedean variable and locally constant in the finite variable.
  - §4.2(b), p.195 (PDF p.190): an automorphic form satisfies `f * ξ = f` for a simple element
    `ξ` of the Hecke algebra, which may be taken of the form `ξ_∞ ⊗ e_L`.
- Getz–Hahn, errata of October 2026, registered as `getz-hahn-2024-errata-2026-10`, p.1, §4.6:
  Corollary 4.6.3 (an infinitesimal character for irreducible admissible `(𝔤, K)`-modules)
  requires `K` connected; p.2, §6.6, corrects a display on p.171 and a reference in the proof of
  Theorem 6.6.2.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`: I.2.4, pp.25–26 (PDF pp.8–9),
  the counting lemma, and I.2.5, Lemma, p.27 (PDF p.10), moderate growth of right convolutions.

## Smoothness convention

The automorphic forms in the proposition are those of `IsAutomorphicFunctionOn` (module
`Langlands.Automorphic.GroupSchemeInvariantForms`). Its smoothness condition
`IsAdelicSmoothFunction` asks for continuity, smoothness of every archimedean slice
`x ↦ φ(x, y)` and right invariance under one open subgroup of `G(𝔸_f)`. Continuity and
slice-wise smoothness are Borel–Jacquet's smoothness of §4.1. The common open level is the one
that automorphic forms acquire from the Hecke condition §4.2(b) through the idempotent `e_L` of
§3.2. This is the convention of the target `IrreducibleSubrepresentationFormSpectrumStatement`
(see the section "Smoothness convention" of the Markdown of
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction`).

Getz–Hahn's space `A_{A_G}` is built from the smooth functions of their (6.1), an algebraic
tensor product, through Definition 6.3.3. Every function in such a tensor product is a finite
sum `Σ_p a_p(x) b_p(y)`, so all its archimedean slices lie in one finite-dimensional space. The
carrier of `IsAutomorphicFunctionOn` is strictly larger, and the difference occurs on actual
automorphic forms. For the adelic lift of the weight-12 cusp form `Δ` on `SL_2` over `ℚ`, right
invariant under `SL_2(Ẑ)`, left rational invariance gives slices at the finite parts of
`diag(m⁻¹, m)`; after removing the common weight factor these are `m¹² Δ(m² z)`. Their
`q`-expansions start at `q^{m²}`, so they are linearly independent. The note
`notes/automorphic/getz-hahn-literal-tensor-boundary.md` shows more generally that under the
literal reading of (6.1) the cusp forms vanish as soon as `G` has a proper parabolic
`F`-subgroup, and that the compactly supported line of (6.1) is not affected.

The proposition is therefore not a literal transcription of Theorem 6.6.4. It is the
corresponding assertion about representatives of `K`-finite vectors for the Borel–Jacquet
carrier.

## Setting

`L²([G])` is `Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)` on
`[G] = A_G G(F) \ G(𝔸)`, and
`R = RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter hG` is the
right regular representation of `G(𝔸)` on it. For a subgroup `K` of `G(𝔸)`,
`K_∞ = K.comap (ofInfinite F G)` is its archimedean part. A `K`-finite vector is one satisfying
`IsCanonicalL2FiniteVector hG K` (module `Langlands.Global.AdelicL2FiniteVectorDensity`): its
translates by `K_∞` span a finite-dimensional subspace and it is fixed by an open subgroup of
`G(𝔸_f)`; for a maximal compact `K` these are the `K`-finite vectors of Getz–Hahn for
`K = K_∞ K^∞` (see that module's Markdown).

## Statements

### `IrreducibleSubrepresentationFiniteVectorAutomorphyStatement`

For a number field `F : Type`, `G` with `IsAffineHom G.X.hom`, `IsAffine G.X.left`,
`LocallyOfFiniteType G.X.hom` and `hG : IsConnectedReductive G`, a subgroup `K` of `G(𝔸)` with
`IsMaximalCompactSubgroup F G K`, `rho : MatrixRepresentation G (Fin N)` with
`IsClosedSubgroup rho`, `hsmooth : SmoothOfRelativeDimension d G.X.hom`,
`hcalc : AdelicDifferentialCommutator F G hsmooth`, and `V` with
`Langlands.Analysis.IsIrreducibleSubrepresentation R V`: every `w ∈ V` with
`IsCanonicalL2FiniteVector hG K w` has a function `φ : G(𝔸) → ℂ` with

- `IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K_∞ rho φ`,
- `IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) φ`, and
- `w =ᵐ fun y => φ y.out`.

Correspondence. Getz–Hahn Theorem 6.6.4 and its proof show that the `K`-finite vectors of a
discrete automorphic representation, viewed as functions on `[G]`, are automorphic forms; the
proof states this as membership in `A_{A_G}`. The proposition is the corresponding assertion
about representatives for the Borel–Jacquet carrier (section "Smoothness convention"), not for
the algebraic tensor carrier of (6.1). An automorphic form on `[G]` is here a left
`G(F)`-invariant function on `G(𝔸)` satisfying `IsAutomorphicFunctionOn`: smooth in the sense
of Borel–Jacquet §4.1 with one common open level as given by §4.2(b), `K_∞`-finite, `𝔷`-finite
and of moderate growth for the adelic norm of `rho`. It is also left invariant under `A_G`, and
the class of `w` is the class of `φ`. Two steps of the printed proof need the following
replacements:

- `𝔷`-finiteness. The printed proof uses the infinitesimal character of Corollary 4.6.3, which
  the October 2026 errata restrict to connected `K`. For connected reductive `G` the elements of
  the centre `Z(𝔤)` are fixed by the adjoint action of the connected group of complex points of
  `Res_{F/ℚ} G`, which contains `G(F_∞)`; so they commute with `K_∞` and with `G(𝔸_f)` and
  preserve the spaces of vectors of a given `K_∞`-type fixed by a compact open
  `L`; these spaces are finite-dimensional by Theorem 6.6.2, so a `K`-finite vector is annihilated
  by an ideal of finite codimension, which is what `IsCenterFiniteFunction` asks.
- Moderate growth. The printed proof cites Lemma 4.4.13, which bounds continuous seminorms of the
  archimedean smooth-vector representation, not values of functions. A pointwise bound follows
  from the reproducing function of Lemma 9.7.2: fold `∫ f(h) ϕ(x h) dh` onto `[G]`, count the
  rational translates meeting `x · supp f` by a power of the height of `x` (Mœglin–Waldspurger
  I.2.4) and apply the Cauchy–Schwarz inequality, as in Mœglin–Waldspurger I.2.5.

The reproducing function of Lemma 9.7.2 and the resulting representative play different roles
with respect to (6.1). The kernel is compactly supported: in the proof of Lemma 9.7.2 it is
`f = f_∞ ⊗ e_L`, with `f_∞` smooth and compactly supported on `A_G \ G(F_∞)` (Proposition 4.5.6)
and `e_L` the normalized characteristic function of a compact open subgroup `L` of `G(𝔸_f)` fixing
the vector. For such kernels the algebraic tensor description of `C_c^∞` in (6.1) applies. The
representative `φ(x) = ∫ f(h) ϕ(x h) dh` is a left `G(F)`-invariant function on `G(𝔸)` and need
not be a finite sum of products, as the example of `Δ` above shows. It is continuous, its
archimedean slices are smooth, and it is right invariant under `L` because `f` is left invariant
under `L`. These are the conditions of `IsAdelicSmoothFunction`, which is the form of the
conclusion.

## Proved results

Throughout, `p : P → G` is an isomorphism, `G` is connected reductive, `l : M → P` is a rational
Levi subgroup (`IsRationalLeviSubgroup l`) and `iU : U → P` a geometric unipotent radical. Then
`P` is connected reductive (`IsConnectedReductive.of_iso`), `l` is an isomorphism
(`IsRationalLeviSubgroup.isIso_of_isIso_parabolic`), and
`e = hl.isoOfIsIsoParabolic hG : M ≅ G` has `e.hom = l ≫ p`.

- `map_eq_one_of_isGeometricUnipotentRadical hP hU n`: for connected reductive `P` the point
  `iU(n)` of `P(𝔸)` is `1`. Proof: `IsConnectedReductive.hasTrivialUnipotentRadical`, applied to
  the ground-field radical `hU.1` (closed, smooth, connected, unipotent and normal), gives
  `SubgroupFunctor.range iU = ⊥`, and `n ≫ iU` lies in that range.
- `parabolicQuotientSubgroup_le_rationalSubgroup_of_isIso hG hU`: `U(𝔸) M(F) ≤ G(F)`. Proof:
  the subgroup is the join of the image of `U(𝔸)`, which is trivial by the previous theorem and
  `map_comp_apply`, and the image of `M(F)`, which lies in `G(F)` by `rational_naturality` for
  `l ≫ p`.
- `modulusParameter_eq_zero hP`, `halfModulusParameter_eq_zero hP`: for connected reductive `P`,
  `2ρ_P = 1 ⊗ det(Ad | Lie P)` and `ρ_P` are zero, since
  `Lie.connectedReductiveAdjointDeterminant` gives `adjointDeterminantCharacter P = 0`.
- `isSplitComponentEquivariant_of_isIso hG hl hφ`: a function left invariant under `A_G`
  satisfies the `A^n_P` condition. Proof: `ρ_P = 0`, so the factor `parameterPower` is `1`
  (`parameterPower_zero`); `p(l(a)) = e(a)` (`map_comp_apply`) lies in `A_G` for `a ∈ A_M` by
  `RestrictionSplitCentre.map_mem_canonicalSubgroup`.
- `integrable_iwasawa_of_isIso hG hl hKc hφc hφ hL2`: for continuous `φ` left invariant under
  `A_G G(F)` (`canonicalRationalSubgroup`) with `y ↦ φ(y.out)` in `L²([G])`, the function
  `(k, y) ↦ ‖δ_P(l(y.out))⁻¹‖ · ‖φ(p(l(y.out)) k)‖²` is integrable on `K × [M]` for the Haar
  probability measure of `K` and the canonical measure of `[M]`. Proof: `2ρ_P = 0`, so the
  modulus factor is `1` and the integrand is `W(k, y.out)` with `W(k, m) = ‖φ(e(m) k)‖²`. `W` is
  continuous and left invariant in `m` under `A_M M(F)`
  (`RestrictionSplitCentre.map_mem_canonicalRationalSubgroup`), so `(k, y) ↦ W(k, y.out)` is
  continuous (`LeftCosetSpace.continuous_out_of_invariant`) and, `[M]` being a Borel space
  (`canonicalQuotient_borelSpace`), almost everywhere strongly measurable. For the finiteness of
  the integral, `canonicalMeasure F M` is s-finite (an image of a quotient measure), so
  `lintegral_prod` reduces it to the inner integrals. For fixed `k`, the inner integral equals
  `∫_{[M]} H_k(ē y) dy` with `H_k(z) = ‖φ(z.out k)‖²` on `[G]` and
  `ē = RestrictionSplitCentre.canonicalQuotientMap e`; by
  `RestrictionSplitCentre.map_canonicalMeasure` the image of the measure of `[M]` under `ē` is
  `s` times the measure of `[G]`, so it equals `s ∫_{[G]} H_k`; the right invariance
  `canonicalMeasure_rightInvariant` (`MeasurePreserving.lintegral_comp`) turns this into
  `s ∫_{[G]} ‖φ(z.out)‖²`, which is finite by the `L²` hypothesis
  (`lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`). The outer integral of this constant for the
  probability measure on `K` is finite.
- `isSquareIntegrableInducedForm_of_isIso hl hG hU hKc hφ hA hL2`: an automorphic form `φ` on
  `G(F) \ G(𝔸)` (for `K_∞` and `rho`) that is left invariant under `A_G` and whose class
  `y ↦ φ(y.out)` lies in `L²([G])` satisfies
  `IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ`. Proof: the automorphy
  conditions other than left invariance are those of `φ`; left invariance under
  `parabolicQuotientSubgroup` follows from `parabolicQuotientSubgroup_le_rationalSubgroup_of_isIso`;
  the `A^n_P` condition is `isSplitComponentEquivariant_of_isIso`; invariance under
  `A_G G(F)` (`LeftCosetSpace.invariant_sup`) and continuity of `φ` give the integrability by
  `integrable_iwasawa_of_isIso`.
- `irreducibleSubrepresentationFormSpectrum_of_finiteVectorAutomorphy hA`: the proposition
  implies `IrreducibleSubrepresentationFormSpectrumStatement`. Proof (as implemented): introduce
  the data and the instance `LocallyOfFiniteType P.X.hom` (from
  `IsClosedSubgroup.locallyOfFiniteType`, as in the statement). Let `V` be irreducible and
  `v ∈ V`. Since `V` is closed and invariant and `K` is compact (`hKmax.1`),
  `subset_closure_canonicalL2FiniteVectors` puts `v` in the closure of the `K`-finite vectors of
  `V`. For each such `w`, `hA` gives an automorphic, `A_G`-invariant `φ` with `w =ᵐ φ ∘ out`; then
  `φ ∘ out` is in `L²([G])` (`MemLp.ae_eq`), so `isSquareIntegrableInducedForm_of_isIso` (with the
  Levi of the presentation, `r.isCompatible.levi`) shows `φ ∈ A²_P`, and `w` is the generator of
  `squareIntegrableFormSpectrum` with `k = 1`, `v = φ` and `c = 1`. Hence the closure of the
  `K`-finite vectors lies in the closure of the span of the generators (`closure_mono`,
  `Submodule.topologicalClosure_coe`), which is `squareIntegrableFormSpectrum`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

- Proved: the comparison between `A_G`-invariant square-integrable automorphic forms on
  `G(F) \ G(𝔸)` and Lapid's `A²_P` for a full parabolic, and the reduction of
  `IrreducibleSubrepresentationFormSpectrumStatement` to
  `IrreducibleSubrepresentationFiniteVectorAutomorphyStatement`.
- Stated, not proved here: `IrreducibleSubrepresentationFiniteVectorAutomorphyStatement`, whose
  proof needs the admissibility of irreducible unitary representations of `G(𝔸)` (or the action of
  `𝔷` by scalars on smooth vectors together with Harish-Chandra's finiteness theorem), reproducing
  functions, regularity, `𝔷`-finiteness and moderate growth of the representatives.
