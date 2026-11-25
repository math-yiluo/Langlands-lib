# Admissibility of principal series over `ℝ` and `ℂ`

Lean module: `Langlands.Representation.Archimedean.PrincipalSeriesAdmissible`. It imports
`Langlands.Representation.Archimedean.PrincipalSeriesGKModule` and
`Langlands.LinearAlgebra.TriangularUnitary`. All declarations are in the namespace
`Langlands.Archimedean.PrincipalSeries`, so that their names do not clash with the real
declarations of the same short names in `Langlands.Archimedean`.

This module proves, for `F = ℝ` or `ℂ` (any `RCLike` field `F`), that the `K`-finite functions
of a right-translation-stable subspace of a principal series of `GL_n(F)` form an admissible
representation of `K`. Here `K` is `O(n)` over `ℝ` and `U(n)` over `ℂ`. It also proves the
sharper bound that a matrix representation of degree `d` of `K` occurs at most `d` times. In
particular the `K`-finite functions of every principal series `principalSeries F n χ` are
admissible (`isAdmissibleGKModule_principalSeriesRep`).

## Provenance

The module restates the real module
`Langlands.Representation.Archimedean.RealStandardModuleAdmissible` for an arbitrary `RCLike`
field. The real module proves these results for `F = ℝ` only. The Lean proofs are the real proofs with `ℝ`
replaced by `F`; nothing in them used that the field is `ℝ`. The generalization is needed
because the complex standard modules (`complexStandardModule n ds`, a complex principal
series) are not covered by the real module. The results are derived content. The
mathematical model is Knapp 1986, Proposition 8.4 (see "Source" below), as for the real
module.

## Notation

- `GL_n(F)` is `Langlands.GeneralLinear n F`. `K` is `unitaryCompact F n` as a subgroup of
  `GL_n(F)`, or `Matrix.unitaryGroup (Fin n) F` as a group; `Unitary.toUnits` maps the second
  onto the first.
- `principalSeries F n χ` (module `StandardModule`) is the Library's normalized smooth
  principal series. It consists of the smooth functions `f` on `GL_n(F)` with
  `f(diag(a) · u · g) = principalSeriesCharacter F n χ a · f(g)` for all
  `a : Fin n → Fˣ` and all upper unipotent `u`. The arguments below use only that two functions
  of the same principal series satisfy this law with the same multiplier.
- For a subspace `V` of functions on `GL_n(F)` stable under right translation by `K` (the
  hypothesis `hVK`), `kFiniteRep V hVK` (module `PrincipalSeriesGKModule`) is right
  translation by `K` on the `K`-finite functions of `V`. `principalSeriesRep F n χ` is
  `kFiniteRep` for `V = principalSeries F n χ`.
- `gkIntertwiners ρ d τ` (module `GKModule`) is the space of linear maps
  `T : ℂ^d → V` with `T (τ(k) x) = ρ(k) (T x)`. `IsAdmissibleGKModule ρ` says that this
  space is finite-dimensional for every `d` and every continuous `τ : K →* Matrix (Fin d) (Fin d) ℂ`.

## Declarations

- `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact` (Iwasawa decomposition, existence
  only): every `g ∈ GL_n(F)` is `diag(a) · u · k` with `a : Fin n → Fˣ`, `u` upper unipotent and
  `k ∈ K`. The Library's `TriangularUnitary.exists_upperTriangular_mul_unitary` (over any
  `RCLike` field; proved there through a Cholesky factorization of `g gᴴ`) gives `g = b · w`
  with `b` invertible upper triangular and `w` unitary. The diagonal entries of `b` are nonzero
  because `det b` is their product (`Matrix.det_of_isUpperTriangular`). With
  `D = diag(b₁₁, …, bₙₙ)`, the matrix `D⁻¹ · b` is upper triangular with ones on the diagonal,
  and `g = D · (D⁻¹ · b) · w`. The factor order is that of `principalSeries` and of the
  p-adic `Iwasawa.diagonalUnits`.
- `eq_of_eqOn_unitaryCompact_of_mem_principalSeries` and
  `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`: two functions of the same
  principal series that agree on `K` are equal. Write `g = diag(a) · u · k` and apply the
  transformation law to both functions.
- `gkIntertwinerValueAtOne V hVK d τ`: the linear map sending an intertwiner `T` to the
  linear functional `x ↦ (T x)(1)` on `ℂ^d`. `gkIntertwinerValueAtOne_apply` unfolds it.
- `gkIntertwiner_apply_unitary`: `(T x)(k) = (T (τ(k) x))(1)` for `k ∈ K`. Indeed
  `T (τ(k) x) = ρ(k) (T x)` is the right translate of `T x` by `k`, whose value at `1` is
  `(T x)(k)`.
- `gkIntertwinerValueAtOne_injective`: if `V ≤ principalSeries F n χ`, then
  `gkIntertwinerValueAtOne` is injective. If `S` and `T` give the same functional, the
  previous lemma shows that `S x` and `T x` agree on `K` for every `x`, so they are equal.
- `finrank_gkIntertwiners_kFiniteRep_le`: the intertwiner space has dimension at most
  `dim (ℂ^d)^* = d`, by injectivity into the dual of `ℂ^d`.
- `isAdmissibleGKModule_kFiniteRep`: hence `kFiniteRep V hVK` is admissible for every
  right-translation-stable subspace `V` of a principal series (`Module.Finite.of_injective`).
- `finrank_gkIntertwiners_principalSeriesRep_le` and `isAdmissibleGKModule_principalSeriesRep`:
  the case `V = principalSeries F n χ`.

The bound `≤ d` holds for every matrix representation of degree `d`, irreducible or not, so
continuity of `τ` is not used. Smoothness of the functions is not used either.

## Source

- A. W. Knapp, *Representation Theory of Semisimple Groups: An Overview Based on Examples*,
  Princeton University Press, 1986, registered as
  `provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855` (file
  `Knapp, Representation Theory of Semisimple Groups, An Overview Based on Examples (1986).pdf`,
  SHA256 `a8ae5776789005035f477f7ea79ee4a268ad43b2d84a607d55b4bedf763dbe75`). Proposition 8.4,
  p.207 (PDF 221), and its proof and Remark (1), pp.207–208 (PDF 221–222). There, for a linear
  connected reductive group `G`, a parabolic subgroup `S = MAN` and an irreducible unitary `σ`
  of `M`, the induced representation `U(S, σ, ν)` is admissible with
  `[U(S, σ, ν)|_K : τ] ≤ dim τ`, by Frobenius reciprocity for `K`. This module does not use
  that result or any identification of the Library's models with classical parabolic
  induction. It proves the analogous finiteness and multiplicity bound directly for the
  Library's function models on `GL_n(ℝ)` and `GL_n(ℂ)`. Evaluation at `1` embeds `Hom_K(τ, V)`
  into `Hom(τ, ℂ)` because a principal-series function is determined by its restriction to
  `K`. This is the part of the Frobenius-reciprocity argument that the bound needs.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), registered
  as `getz-hahn-2024-automorphic-representations`. p.116 (PDF 131): admissibility of a
  `(𝔤, K)`-module, whose Library form is `IsAdmissibleGKModule` (see the `GKModule` Markdown).
