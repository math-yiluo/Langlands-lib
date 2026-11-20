# Adelic radical integral vanishing for `GL_n`

`Langlands.TraceFormula.GeneralLinearRadicalIntegralVanishingStatement.{u}` says that
vanishing along every two-sided translate of the standard upper two-block unipotent
subgroups at one finite place implies vanishing along every two-sided translate of the
adelic unipotent radical of every proper rational parabolic of `GL_n`.

## Library notation

- `AdelicGL F n` is the group of invertible `n × n` matrices over the adele ring of the
  number field `F`. For a finite place `v : Langlands.Global.FinitePlace F`,
  `FiniteCompletion F v` is the completion `F_v`.
- For `h : a + b = n`, `Langlands.GeneralLinear.blockUnipotent h Z` is
  `[[1, Z], [0, 1]]` in `GL_n(F_v)` when `Z` is an `a × b` matrix over `F_v`.
  The map `ι_v` first applies `FiniteAdelicGL.localInclusion F n v` to put the matrix
  at `v` and the identity at the other finite places, then applies `AdelicGL.ofFinite F n`
  to put the identity at the infinite places.
- Write `GL_n` for `GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`.
  `GeneralLinearGroupPoints.adelicHomeomorph F n` identifies `AdelicGroupPoints F GL_n`
  with `AdelicGL F n` as topological groups. Elaboration uses the Library's
  `isAffine_groupScheme` and `smoothStatement` as local instances for this group scheme.
- `ProperRationalParabolic GL_n` is the type of rational parabolic subgroup functors
  of `GL_n` distinct from the full group. For such a `P`, write `N_P` for the radical
  `properRationalParabolicRadicals hPD hG P`. Its adelic points are the subgroup
  given by `AdelicSubgroupPoints.adelicPoints`. The measure
  `properParabolicHaarMeasure F GL_n hPD hG P` is Haar on `N_P(𝔸_F)` scaled by the
  inverse mass of the Library's associated measure on `N_P(F) \ N_P(𝔸_F)`.

## Statement

Let `F : Type u` be a number field and `n : ℕ`. Assume `hPD : ParabolicDynamicStatement.{u}`,
the characterization of parabolic subgroups of connected reductive groups by cocharacters,
and `hG : IsConnectedReductive GL_n`. Fix a finite place `v` of `F` and a continuous,
compactly supported function `f : AdelicGL F n → ℂ`.

For every `a, b : ℕ` and `h : a + b = n` with `0 < a` and `0 < b`, equip the space of
`a × b` matrices over `F_v` with its Borel σ-algebra. Assume that every additive Haar
measure `ν` on this space and all `x, y : AdelicGL F n` satisfy

`∫ Z, f (x * ι_v (blockUnipotent h Z) * y) ∂ν = 0`.

This is the local vanishing hypothesis of Task 7577 with `F` in place of `K`.

Then for every `P : ProperRationalParabolic GL_n` and all `x, y : AdelicGroupPoints F GL_n`,
with `↑m` denoting the inclusion of `m : N_P(𝔸_F)`, the conclusion is

`∫ m, f (GeneralLinearGroupPoints.adelicHomeomorph F n (x * ↑m * y)) ∂properParabolicHaarMeasure F GL_n hPD hG P = 0`.

This is the vanishing hypothesis of Tasks 7578 and 7579 specialized to `GL_n` and
the test function `f ∘ GeneralLinearGroupPoints.adelicHomeomorph F n`.

For `n ≤ 1`, both vanishing conditions are vacuous. The local condition needs a split
into two positive block sizes. A proper rational parabolic requires weights
`e : Fin n → ℤ` with a strict increase `e i < e j`, by the Library's
`exists_properRationalParabolicRadicals_eq_comap`.

## Source

The statement is derived from the proof of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Lemma 16.4.2, printed p. 430 (PDF p. 438), registered as
`getz-hahn-2024-automorphic-representations`. The source takes a smooth product
`f = f_v ⊗ f^v` on `A_G \ G(𝔸_F)`. The proof unfolds a constant term of `R(f)` to an integral
over `N_P(𝔸_F)` and uses supercuspidality of `f_v` to make that integral vanish.
Supercuspidality in Definition 16.4.1 tests the radicals of all proper local parabolics.
[Getz–Hahn, *An Introduction to Automorphic Representations*](https://doi.org/10.1007/978-3-031-41153-3)

The derived statement isolates that vanishing step for `GL_n`. It takes the displayed
two-block vanishing condition directly on an arbitrary continuous compactly supported
`f`, and formulates the adelic vanishing using the Library's normalized radical Haar
measure.
