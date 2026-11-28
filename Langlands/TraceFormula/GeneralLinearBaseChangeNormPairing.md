# Norm pairing of rational points of `Res_{L/K} GL_n` and `GL_n`

Module `Langlands.TraceFormula.GeneralLinearBaseChangeNormPairing`, namespace
`Langlands.TraceFormula`.

Notation (local to the module): `GLₙ` is `GroupScheme.GeneralLinear.groupScheme (Fin n)
(CommRingCat.of K)` with local `IsAffine` and `Smooth` instances, `Wₙ = weilGroup K L GLₙ`,
and `Θₙ = normOneAut K (unitGaloisAut K L GLₙ σ)`. `K` and `L` are number fields with
`[Algebra K L] [FiniteDimensional K L]`, `σ : L ≃ₐ[K] L` and `l : ℕ`. The matrix coordinate
of a point of `Wₙ(𝔸_K)` is `cyclicWeilAdelicMap K L n : Wₙ(𝔸_K) → GL_n(𝔸_L)`. The matrix
coordinate of a point of `GLₙ(𝔸_K)` is `GeneralLinearGroupPoints.adelicHomeomorph K n`.
`AdelicGL.rational` is the diagonal embedding of rational matrices. The ordered norm of
`x ∈ Wₙ(𝔸_K)` is `N(x) = x Θ(x) ⋯ Θ^{l-1}(x)`, the product over `List.range l` of
`adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x`.

## Matrix coordinates

- `mem_rationalNormOneSubgroup_weil_iff`, `mem_rationalNormOneSubgroup_gl_iff`: a norm-one
  point is rational exactly when its matrix coordinate is in the range of
  `AdelicGL.rational`.
- `exists_rationalNormOne_weil`, `exists_rationalNormOne_gl`: every rational matrix over `L`
  (resp. `K`) is the coordinate of a rational norm-one point.
- `normOne_weil_ext`, `normOne_gl_ext`: norm-one points with equal matrix coordinates are
  equal.
- `adeleInclusion_map_rational`: entrywise adele inclusion `GL_n(𝔸_K) → GL_n(𝔸_L)` maps
  `AdelicGL.rational K n b` to `AdelicGL.rational L n (baseChange K L n b)`.
- `cyclicWeilAdelicMap_norm`: if the coordinate of `x` is `AdelicGL.rational L n a`, the
  coordinate of `N(x)` is `AdelicGL.rational L n (cyclicNorm σ l a)`.
- `twistedConj_adelicEquiv_rational`, `cyclicWeilAdelicMap_twistedConj`: in coordinates,
  twisted conjugation by `Θₙ` is `a ↦ c⁻¹ a σ(c)`, with `σ` applied entrywise
  (`entrywiseAut σ n`).

On the `Wₙ` side these follow from `generalLinearWeilAdelicTwist` (module
`Langlands.TraceFormula.GeneralLinearWeilAdelicTwistProof`). It identifies `Wₙ(𝔸_K)` with
`GL_n(𝔸_L)` through `cyclicWeilAdelicMap`, matching rational points. Under it, `adelicAut K
(unitGaloisAut K L GLₙ (σ ^ k))` becomes the entrywise Galois action
`AdelicGLTransport.adelicEquiv n (σ ^ k).toRingEquiv`, which acts on rational matrices by
`entrywiseAut (σ ^ k) n` (`AdelicGLTransport.adelicEquiv_rational`). Twisted conjugation on
norm-one points uses `generalLinearWeilNormOne_twistedConj`. On the `GLₙ` side they follow
from `GeneralLinearGroupPoints.rationalEquiv` and
`GeneralLinearGroupPoints.adelicHomeomorph_rational`.

## The norm relation

`BaseChangeNormRelated σ l r q` for `r ∈ Wₙ(𝔸_K)¹` and `q ∈ GLₙ(𝔸_K)¹` means: there is
`y ∈ GL_n(L)` with

`Φ(N(r)) · AdelicGL.rational L n y = AdelicGL.rational L n y · ΦG(q)`,

where `Φ = cyclicWeilAdelicMap K L n` and `ΦG(q)` is the entrywise adele inclusion of the
coordinate of `q`. This is the relation used in the matching and vanishing hypotheses of
`GeneralLinearBaseChangeTraceComparisonStatement`, written for norm-one points. It is the
relation "`N(δ)` is `GL_n(L)`-conjugate to `γ`" of Arthur–Clozel (*Simple algebras, base
change, and the advanced theory of the trace formula*, Chapter 1, §1) and Henniart–Lemaire
(*Changement de base et induction automorphe pour GL_n en caractéristique non nulle*,
I.2.2), transported to adelic points.

- `baseChangeNormRelated_iff`: if the coordinates of `r` and `q` are rational matrices `a` and
  `b`, then `BaseChangeNormRelated σ l r q ↔ IsNormAssociated σ l a b`. Here
  `IsNormAssociated` (module `Langlands.BaseChange.Norm`) says `y⁻¹ cyclicNorm σ l a y =
  baseChange K L n b` for some `y ∈ GL_n(L)`. The proof rewrites with
  `cyclicWeilAdelicMap_norm` and `adeleInclusion_map_rational`, then uses injectivity of
  `AdelicGL.rational`.

## Properties from the cyclic norm lemma

All of the following assume `IsCyclicAlgebra σ l` and use `cyclicNormLemma` (module
`Langlands.BaseChange.CyclicNormLemma`; Arthur–Clozel, Chapter 1, Lemma 1.1, and
Henniart–Lemaire, I.2.2). Each proof passes to rational matrix coordinates with the lemmas
above and `baseChangeNormRelated_iff`.

- `exists_baseChangeNormRelated`: every rational norm-one point of `Wₙ` is related to a
  rational norm-one point of `GLₙ` (existence of the norm `b` of `a`, then
  `exists_rationalNormOne_gl`).
- `baseChangeNormRelated_of_twistedConj_left`: the relation is invariant under rational
  `Θₙ`-twisted conjugation of the first argument. In coordinates, `a ↦ c⁻¹ a σ(c)` preserves
  norm association (`IsNormAssociated.twistedConj`, using `σ^l = 1`).
- `baseChangeNormRelated_of_conj_right`: the relation is invariant under rational conjugation
  of the second argument.
- `isTwistedConjugate_of_baseChangeNormRelated`: two rational points of `Wₙ` related to the
  same rational point of `GLₙ` are rationally `Θₙ`-twisted conjugate. Their norms are
  conjugate in `GL_n(L)`, so the cyclic norm lemma makes their coordinates
  `σ`-conjugate. `isTwistedConjugate_of_rational_coordinates` (module
  `Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives`) lifts this to the
  norm-one points.
- `isConjugate_of_baseChangeNormRelated`: two rational points of `GLₙ` related to the same
  rational point of `Wₙ` are rationally conjugate (uniqueness of the norm up to
  `GL_n(K)`-conjugacy, then `exists_rationalNormOne_gl` and `normOne_gl_ext`).
