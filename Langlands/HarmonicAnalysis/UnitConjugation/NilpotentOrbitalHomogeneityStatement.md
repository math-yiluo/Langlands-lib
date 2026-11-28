# Homogeneity of nilpotent orbital integrals

The module `Langlands.HarmonicAnalysis.UnitConjugation.NilpotentOrbitalHomogeneityStatement`
states, as `Langlands.HarmonicAnalysis.LieAlgebraNilpotentOrbitalHomogeneityStatement.{u, v}`,
Harish-Chandra's Lemma 3.2 for the Lie algebra `A` of the unit group of a finite-dimensional
semisimple algebra over a nonarchimedean local field of characteristic zero. The statement is
**not** proved here.

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero, every
finite-dimensional semisimple `F`-algebra `A : Type v` with its module topology (and a Borel
σ-algebra on `Aˣ`), every nilpotent `N : A`, every Borel σ-algebra on the coset space of the
centralizer `C = conjugationCentralizer N`, every Haar measure `μG` on `Aˣ`, every
right-invariant Haar measure `μH` on `C`, every compatible quotient measure `ν` with
convergent orbital integrals `hconv`, every `t : Fˣ` and every Schwartz–Bruhat function `f`:

`orbitalDistribution N ν hconv (scalarDilation (t ^ 2) f) =
  (distribHaarChar F t : ℂ) ^ (finrank F A - finrank F (Subalgebra.centralizer F {N})) *
    orbitalDistribution N ν hconv f`.

Here `scalarDilation (t ^ 2) f` is `X ↦ f(t⁻² X)` (module
`Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing`), `distribHaarChar F t` is
Mathlib's modulus of `F` (the factor by which `x ↦ t x` multiplies Haar measure on `F`), which
is the normalized absolute value `|t|` (the Library's
`HarishChandraSchwartz.distribHaarChar_eq_residueNormalizedAbsoluteValue`), and the exponent
`dim_F A - dim_F C_A(N)` is the dimension of the orbit of `N`, `C_A(N)` being the centralizer of
`N` in the Lie algebra `A`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
§3.1, printed pp. 17–19 (PDF pp. 32–34), Lemma 3.2 (Lemma 3): "Fix `O ∈ O(0)`. Then
`ρ(t²) μ_O = |t|^{d(O)} μ_O`", where `(ρ(t)T)(f) = T(f_t)`, `f_t(X) = f(t⁻¹X)`, and `d(O)` is
the dimension of `O`. The statement holds for every normalization of the invariant measure on
the orbit, hence for every compatible quotient measure. The proof uses the Jacobson–Morozov
theorem and the modulus of the action of a one-parameter subgroup on the orbit.

Kottwitz, *Harmonic analysis on reductive p-adic groups and Lie algebras*, in *Harmonic
Analysis, the Trace Formula, and Shimura Varieties*, Clay Math. Proc. 4, 2005, source ID
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12),
Lemma 17.2, printed p. 461: `μ_O(f_{α²}) = |α|^{-dim O} μ_O(f)` for `f_β(X) = f(βX)`, the same
identity in the opposite normalization of dilations.
