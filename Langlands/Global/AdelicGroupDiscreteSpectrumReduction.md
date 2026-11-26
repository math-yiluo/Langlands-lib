# The discrete spectrum and the square-integrable automorphic forms: reduction to two inputs

Module `Langlands.Global.AdelicGroupDiscreteSpectrumReduction` reduces the published
`Langlands.Global.GroupSquareIntegrableFormSpectrumStatement` (module
`Langlands.Global.AdelicGroupParabolicSpectrumReduction`) to two new propositions, one for each
inclusion:

- `SquareIntegrableFormFiniteProjectionStatement`: the finite discrete content of a
  square-integrable automorphic form;
- `IrreducibleSubrepresentationFormSpectrumStatement`: every irreducible subrepresentation of
  `L²([G])` lies in the closed span of the square-integrable automorphic forms.

It proves the implications `groupSquareIntegrableFormSpectrum_of_reduction` and
`groupParabolicSpectrum_of_reduction`, the latter ending in
`Langlands.Global.GroupParabolicSpectrumStatement` (module
`Langlands.Global.AdelicSpectralDecompositionReduction`). It proves neither new proposition.

| Declaration | Kind | Source |
| --- | --- | --- |
| `norm_canonicalL2RightAction` | theorem (proved) | internal |
| `SquareIntegrableFormFiniteProjectionStatement` | statement | derived: Getz–Hahn Theorems 6.2.4 and 6.3.4 (Harish-Chandra); Borel–Jacquet §4.3 (i) |
| `IrreducibleSubrepresentationFormSpectrumStatement` | statement | Getz–Hahn Theorem 6.6.4 and Lemma 9.7.2 |
| `groupSquareIntegrableFormSpectrum_of_reduction` | theorem (proved) | internal |
| `groupParabolicSpectrum_of_reduction` | theorem (proved) | internal |

All names are in the namespace `Langlands.Global`.

## Sources

Page numbers are printed pages, with one-based PDF pages in parentheses.

- Getz–Hahn, *An introduction to automorphic representations* (2024), registered as
  `getz-hahn-2024-automorphic-representations`:
  - Theorem 6.2.4, p.160 (PDF p.174), after Harish-Chandra 1966, §8, Theorem 1: for a
    `K_∞`-finite, `Z(𝔤)`-finite function `φ` on `G(F_∞)` there is `f ∈ C_c^∞(G(F_∞))` with
    `R(f)φ = φ`. This is a smoothing at the archimedean places only.
  - Theorem 6.3.4, p.164 (PDF p.178), the adelic form of Harish-Chandra's finiteness theorem
    (Theorem 6.2.6, p.161): for an ideal `J ⊆ Z(𝔤)` of finite codimension, a `K_∞`-type `σ`
    and a compact open `K^∞ ≤ G(𝔸_f)`, the space `A(J, σ)^{K^∞}` of automorphic forms is
    finite-dimensional.
  - (6.1) and (6.2), p.158 (PDF p.172), and Definition 6.3.3, p.163 (PDF p.177): smooth
    functions on `G(𝔸)`, the finite decomposition of `G(F) \ G(𝔸) / K^∞` into arithmetic
    quotients, and automorphic forms.
  - Proposition 4.4.7, p.116 (PDF p.131): density and smoothness of `K`-finite vectors.
    Definition 4.4.12 and Lemma 4.4.13, pp.119–120 (PDF pp.134–135): the smooth vectors of a
    Hilbert space representation of `G(F_∞)` form a representation of moderate growth, a bound
    on continuous seminorms of the archimedean smooth-vector representation.
    Corollary 4.6.3, p.125 (PDF p.140): Schur's lemma for irreducible admissible
    `(𝔤, K)`-modules. Theorem 6.6.2, pp.170–171 (PDF pp.184–185): admissibility of the
    `K`-finite vectors of an irreducible unitary representation of `G(𝔸)`.
  - Theorem 6.6.4 with its proof, p.172 (PDF p.186): the space of `K`-finite vectors of a
    discrete automorphic representation, that is of an irreducible subrepresentation `V` of
    `L²([G])`, is an automorphic representation; the proof shows that these vectors, viewed as
    functions on `[G]`, are automorphic forms ("it suffices to show that `V_fin` lies in
    `A_{A_G}`").
  - Lemma 9.7.2, pp.264–265 (PDF pp.276–277): the `K`-finite vectors of an irreducible unitary
    representation `(π, V)` of `A_G \ G(𝔸)` are dense in `V`, and every `K`-finite `ϕ` satisfies
    `π(f)ϕ = ϕ` for some `f ∈ C_c^∞(A_G \ G(𝔸))`.
  - §9.1 (9.6), p.242 (PDF p.254): the discrete spectrum.
- Getz–Hahn, errata of October 2026, registered as `getz-hahn-2024-errata-2026-10`, p.1, §4.6:
  before Corollary 4.6.3 one must assume `K` connected to deduce that `Z(𝔤)` commutes with the
  action of `K` (counterexample `K = O_2(ℝ)`), so Corollary 4.6.3 gives an infinitesimal
  character only for connected `K`. The same errata correct a display on p.171 and a
  cross-reference in the proof of Theorem 6.6.2; these do not affect the results cited here.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations* (1979),
  registered as `borel-jacquet-1979-automorphic`: §3.2, p.194 (the idempotent `e_L` of a
  compact open `L ≤ G(𝔸_f)`); §4.1, p.194 (a function on `G(𝔸) = G_∞ × G(𝔸_f)` is smooth if
  it is continuous, `C^∞` in the archimedean argument for a fixed finite argument and locally
  constant in the finite argument for a fixed archimedean argument); §4.2, p.195 (automorphic
  forms of type `(ξ, J, K_∞)`; condition (b), `f * ξ = f` for a simple Hecke element `ξ`, with
  the remark that `ξ_f * e_L = ξ_f` for some compact open `L`, so the form is right
  `L`-invariant); §4.3 (i), p.195 (the space of automorphic forms of a fixed type is
  finite-dimensional, with the finite decomposition `G(𝔸) = G(F) · C · G_∞ · L` at its start).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`: I.2.4, pp.25–26 (PDF pp.8–9),
  the counting lemma bounding the rational translates meeting a translated compact set by a
  power of the norm; I.2.5, Lemma, p.27 (PDF p.10), right convolution by a smooth compactly
  supported function gives moderate growth, in (b) for square-integrable functions with a
  unitary central character.

- Harish-Chandra, *Discrete series for semisimple Lie groups. II* (1966), registered as
  `harish-chandra-1966-discrete-series-ii`, §8, Theorem 1, p.18: for a smooth function `f`
  on a connected semisimple group with values in a finite-dimensional space such that the functions `z f`, for `z`
  in the algebra generated by the centre of the enveloping algebra and the complexified Lie
  algebra of `K`, span a finite-dimensional space, `f * α = f` for some
  smooth compactly supported `α` supported near `1` and invariant under `K`-conjugation.

## Smoothness convention

The Library's `IsAdelicSmoothFunction` (module `Langlands.Automorphic.GroupSchemeInvariantForms`)
asks for continuity, smoothness of every archimedean slice and invariance under one open
subgroup of `G(𝔸_f)`. Continuity and slice-wise smoothness are Borel–Jacquet's smoothness of
§4.1 (which asks for local constancy in the finite argument, not a common level). The common
compact open level is the one that automorphic forms acquire from the Hecke condition §4.2 (b)
through the idempotent `e_L` of §3.2. This convention is not the literal algebraic tensor
product of Getz–Hahn (6.1); the note
`notes/automorphic/getz-hahn-literal-tensor-boundary.md` explains why the literal reading is too
restrictive for automorphic forms. The explanations below use the Borel–Jacquet convention.

## Setting

Both propositions quantify over the data of `GroupSquareIntegrableFormSpectrumStatement`: a
number field `F : Type`, `G` with `IsAffineHom G.X.hom`, `IsAffine G.X.left`,
`LocallyOfFiniteType G.X.hom` and `hG : IsConnectedReductive G`, a subgroup `K` of `G(𝔸)` with
`IsMaximalCompactSubgroup F G K`, `rho` with `IsClosedSubgroup rho`, `hsmooth` and `hcalc`, and
data `P M U A`, a closed immersion `p : P → G`, `iU : U → P`, `l : M → P`, `a : A → M` with the
instance hypotheses `IsAffine P.X.left`, `IsAffine M.X.left`, `LocallyOfFiniteType M.X.hom`,
`IsAffine U.X.left`, a `ParabolicRootPresentation p l a`,
`LeviSubgroup.IsGeometricUnipotentRadical iU`, `hK : IsIwasawaCompact p K` and `IsIso p`.

`L²([G])` is `Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)`, and
`R = RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter hG` is the right
regular representation of `G(𝔸)` on it. As in the Markdown of
`Langlands.Global.AdelicGroupParabolicSpectrumReduction`, for `p` an isomorphism the elements of
Lapid's `A²_P` (`IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l`) are the
square-integrable automorphic forms on `[G]`, for the archimedean compact subgroup
`K_∞ = K.comap (ofInfinite F G)`. The comparison is explanatory in this module.

## Statements

### `SquareIntegrableFormFiniteProjectionStatement`

For the data above, let `f ∈ L²([G])`, `k : ℕ`, `v : Fin k → G(𝔸) → ℂ` and `c : Fin k → ℂ`
with `IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)` for every `j`
and

`f =ᵐ fun y => ∑ j, c j * v j y.out`.

Then there is a finite-dimensional subspace `W` of `L²([G])` such that, for every subspace `V`
with an orthogonal projection (`V.HasOrthogonalProjection`) that is invariant under every
`R g`, the orthogonal projection `V.starProjection f` lies in `W`.

Correspondence and provenance (derived). In a Hilbert space the subspaces with an orthogonal
projection are the closed ones, so `V` ranges over the closed `G(𝔸)`-invariant subspaces of
`L²([G])`. The statement is the consequence of Harish-Chandra's finiteness theorem that the
classical proof of "`A²_G ⊆ L²_disc([G])`" uses. The following argument explains the
projection statement and identifies its analytic inputs.

1. Put `φ = ∑ j, c j · v j`. Choose a compact open subgroup `L` of `G(𝔸_f)` inside the open
   subgroups fixing the `v j`. The right `K_∞`-translates of `φ` span a finite-dimensional
   space, so the `K_∞`-types of `φ` form a finite set `Ξ`; the intersection `J` of ideals of
   finite codimension annihilating the `v j` has finite codimension and annihilates `φ`. Here
   `K_∞ = K.comap (ofInfinite F G)`; since `K` is maximal compact in `G(𝔸)`, it is the product
   of its projections, and `K_∞` is maximal compact in `G(F_∞)`.
2. Let `W` be the space of `L²` classes of the automorphic forms on `G(F) \ G(𝔸)` that are
   right `L`-invariant, have `K_∞`-types in `Ξ` and are annihilated by `J`. It lies in the
   finite sum of the spaces `A(J, σ)^L`, `σ ∈ Ξ`, so it is finite-dimensional by Getz–Hahn
   Theorem 6.3.4 (Borel–Jacquet §4.3 (i)).
3. Since `R` is unitary, the projection `P_V` onto a closed invariant `V` commutes with every
   `R g`, hence with the integrated operators `R(β) = ∫ β(g) R(g) dg`, `β ∈ C_c^∞(G(𝔸))`. In
   particular `P_V f` is right `L`-invariant with `K_∞`-types in `Ξ`.
4. A common archimedean reproducing kernel. Getz–Hahn Theorem 6.2.4 gives a kernel for one
   given function; one kernel for all of `φ` comes from finitely many slices. Let
   `t_1, …, t_h` represent the finite set `G(F) \ G(𝔸_f) / L` (Borel–Jacquet §4.3, p.195;
   Getz–Hahn (6.2), p.158) and `c_1, …, c_m` the finitely many connected components of
   `G(F_∞)`. On the identity component `G(F_∞)°` the vector-valued function
   `x ↦ (φ(c_j x t_i))_{i, j}` is smooth, and its translates by the centre `𝔷` of the
   enveloping algebra and by `K_∞ ∩ G(F_∞)°` span a finite-dimensional space, because `φ` is
   annihilated by `J`, is `K_∞`-finite, and `𝔷` acts by right-translation derivatives, which
   commute with left translation by `c_j`. Harish-Chandra 1966, §8, Theorem 1, p.18, stated for
   a vector-valued function (Getz–Hahn use it for Theorem 6.2.4), gives
   `α ∈ C_c^∞(G(F_∞)°)` with `φ(c_j x t_i) = ∫ α(h) φ(c_j x h t_i) dh` for all `i`, `j` and
   `x ∈ G(F_∞)°`. Every `g ∈ G(𝔸)` is `γ c_j x t_i l` with `γ ∈ G(F)`, `x ∈ G(F_∞)°` and
   `l ∈ L`. Since `G(F_∞)` commutes with `G(𝔸_f)`, left `G(F)`-invariance and right
   `L`-invariance carry the identity to `φ(g) = ∫ α(h) φ(g h) dh`, that is `φ = R(α)φ` on
   `G(𝔸)`. With the normalized characteristic function `e_L` of `L` (Borel–Jacquet §3.2) and
   `β = α ⊗ e_L`, the right `L`-invariance gives `φ = R(β)φ`, so `f = R(β) f` and
   `P_V f = R(β) P_V f`.
5. For `g ∈ L²([G])`, `R(β)g` is represented by `x ↦ ∫ β(h) g(x h) dh`, a continuous,
   right `L`-invariant function with smooth archimedean slices. That it has moderate growth on
   `G(𝔸)` is an analytic estimate to be supplied by the proof: fold the integral onto `[G]` and
   bound the number of rational translates meeting `x · supp β` by a power of `‖x‖`
   (Mœglin–Waldspurger I.2.4 (a)(i)), then apply the Cauchy–Schwarz inequality. Archimedean
   smoothing alone does not suffice: for `G = G_m` over `ℚ`, the subgroup `ℝ_{>0}` of
   `G(ℝ) = ℝ^×` acts trivially on the compact quotient `[G]`, so convolution by an archimedean
   kernel supported in `ℝ_{>0}` with integral one fixes every class, including essentially
   unbounded `L²` classes.
   Borel–Jacquet §4.3 (ii) assumes a fixed central character and is not used here.
6. For `z ∈ J`, differentiating under the integral gives `z(R(β)g) = R(β_z)g` with
   `β_z ∈ C_c^∞(G(𝔸))` (as in the proof of Getz–Hahn Corollary 6.2.5). Since `zφ = 0`,
   `R(β_z) f = 0`, and so `z(P_V f) = R(β_z) P_V f = P_V R(β_z) f = 0`.

By steps 3–6, `P_V f` is the class of an automorphic form in the space of step 2, so
`P_V f ∈ W`. The proposition keeps only the conclusion that the projections lie in a
finite-dimensional space, which is all the reduction theorem uses.

### `IrreducibleSubrepresentationFormSpectrumStatement`

For the data above, every `V : Submodule ℂ L²([G])` with
`Langlands.Analysis.IsIrreducibleSubrepresentation R V` satisfies

`V ≤ squareIntegrableFormSpectrum K hK.isCompact rho hsmooth hcalc p iU l`,

the closure of the span of the classes of finite linear combinations of elements of `A²_P`.

Correspondence. `IsIrreducibleSubrepresentation R V` says that `V` is a closed, nonzero,
`G(𝔸)`-invariant subspace with no closed invariant subspaces other than `0` and `V`: an
irreducible subrepresentation of `L²([G])`, that is, a discrete automorphic representation of
`A_G \ G(𝔸)` realized in `L²([G])` (Getz–Hahn Definition 3.7.1 and §9.1). The following
argument explains the analytic inputs to this inclusion.

1. By Getz–Hahn Lemma 9.7.2 the `K`-finite vectors of `V` are dense in `V`, and each such `ϕ`
   satisfies `π(f)ϕ = ϕ` for some `f ∈ C_c^∞(A_G \ G(𝔸))`. This full adelic convolution
   identity gives `ϕ` an actual representative `x ↦ ∫ f(h) ϕ(x h) dh`, which is continuous,
   right invariant under a compact open subgroup of `G(𝔸_f)` and smooth in the archimedean
   variable, as `IsAdelicSmoothFunction` asks. It is `K_∞`-finite because `ϕ` is.
2. Moderate growth of the representative is a separate analytic step, to be supplied by the
   proof. Getz–Hahn's proof of Theorem 6.6.4 cites Lemma 4.4.13, but that lemma (with
   Definition 4.4.12, pp.119–120) bounds continuous seminorms of the archimedean
   smooth-vector representation, not values of functions; using it would require the
   continuity of point evaluation and a passage from archimedean to adelic heights. Instead,
   apply to the reproducing kernel `f` of step 1 the estimate of step 5 of the previous
   proposition: fold `∫ f(h) ϕ(x h) dh` onto `[G]`, bound the number of rational translates
   meeting `x · supp f` by a power of the height of `x` (Mœglin–Waldspurger I.2.4 (a); compare
   the compact-kernel argument of I.2.5 (b), stated there with a unitary central character),
   apply the Cauchy–Schwarz inequality, and compare that height with the adelic norm of `rho`
   used by `HasModerateGrowthFunction`.
3. The representative is `Z(𝔤)`-finite. The printed proof of Theorem 6.6.4 obtains this from
   the infinitesimal character of Corollary 4.6.3, which the October 2026 errata restrict to
   connected `K`; here `K_∞` may be disconnected. For connected reductive `G` the step still holds. Every `z ∈ Z(𝔤)` is fixed
   by the adjoint action of the complex points of the connected group `Res_{F/ℚ} G`, which
   contain `K_∞`: on each finite piece of the PBW filtration of `U(𝔤_ℂ)` this action is
   algebraic, and its differential kills `z`. So `z` commutes with `K_∞` and with `G(𝔸_f)`,
   and preserves the spaces `V_fin(τ)^L` of vectors of `K_∞`-type `τ` fixed by a compact open
   `L`, which are finite-dimensional by Getz–Hahn Theorem 6.6.2. A `K`-finite vector lies in a
   finite sum of such spaces, so it is annihilated by an ideal of finite codimension in
   `Z(𝔤)`. This is all that `IsCenterFiniteFunction` asks; no infinitesimal character is
   needed.
4. The representative is square integrable on `[G]` because it lies in `L²([G])`. So `V` lies in
   the closure of the classes of the square-integrable automorphic forms on `[G]`, which is
   `squareIntegrableFormSpectrum` for `P = G`.

Getz–Hahn take `K = K_∞ K^∞` with `K_∞` maximal compact in `G(F_∞)` and `K^∞` compact open;
here `K` is a maximal compact subgroup of `G(𝔸)` and the forms are `K_∞`-finite for
`K_∞ = K.comap (ofInfinite F G)`. A proof must also show that the representatives satisfy
`IsSquareIntegrableInducedForm` for the isomorphism `p`, including the `A^n_P` condition
`IsSplitComponentEquivariant` and the Iwasawa form of the integrability condition.

## Proved results

- `norm_canonicalL2RightAction hG g f`: `‖R g f‖ = ‖f‖`. Proof: `R g` is the linear map of the
  linear isometry `RestrictionSplitCentre.rationalQuotientL2RightTranslate` for the canonical
  measure and its right invariance `canonicalMeasure_rightInvariant`; `LinearIsometry.norm_map`.
- `groupSquareIntegrableFormSpectrum_of_reduction hF hD`: the two propositions imply
  `GroupSquareIntegrableFormSpectrumStatement`. Proof (as implemented): introduce the data and
  the instance `LocallyOfFiniteType P.X.hom` (from `IsClosedSubgroup.locallyOfFiniteType`, as in
  the statements), and prove the two inclusions.
  - `squareIntegrableFormSpectrum ≤ discreteSpectrum F G hG`: the discrete spectrum is a
    topological closure, hence closed, so it suffices that it contains the generating set
    (`Submodule.topologicalClosure_minimal`, `Submodule.span_le`). For a generator `f` with
    data `k, v, c`, `hF` gives a finite-dimensional `W` containing the projections of `f`
    onto all closed invariant subspaces; `Langlands.Analysis.mem_discretePart_of_starProjection_mem`
    (module `Langlands.Representation.Unitary.DiscretePartCriteria`) with
    `norm_canonicalL2RightAction` gives `f ∈ discreteSpectrum F G hG`.
  - `discreteSpectrum F G hG ≤ squareIntegrableFormSpectrum`: the right side is a topological
    closure, hence closed, and contains every irreducible subrepresentation by `hD`;
    `Langlands.Analysis.discretePart_le_of_forall_le` applies.
- `groupParabolicSpectrum_of_reduction hF hD`: compose with
  `groupParabolicSpectrum_of_squareIntegrableFormSpectrum` (module
  `Langlands.Global.AdelicGroupParabolicSpectrumReduction`).

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

- Proved: the abstract Hilbert space steps that turn the two propositions into
  `GroupSquareIntegrableFormSpectrumStatement` and `GroupParabolicSpectrumStatement`.
- Not proved here: `SquareIntegrableFormFiniteProjectionStatement` and
  `IrreducibleSubrepresentationFormSpectrumStatement`. The first needs Harish-Chandra's finiteness
  theorem for a general connected reductive group and the regularity, growth and
  `𝔷`-annihilation of the projections; the second needs the density of `K`-finite vectors in an
  irreducible subrepresentation and their automorphy, with the transport of the conditions of
  `IsSquareIntegrableInducedForm` from `[M]` to `[G]` along `l ≫ p`.
