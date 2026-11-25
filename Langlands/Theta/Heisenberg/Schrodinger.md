# The Schrödinger representation of a polarization

**GKT §1.2.2** (the Schrödinger model: the action (1.6) of Theorem 1.13, p. 25, with the book's
`(X, Y)` the file's `(Y, X)`: the functions live on the file's `X`).

The module `Langlands.Theta.Heisenberg.Schrodinger` defines the Schrödinger representation of the
Heisenberg group of a polarized module, on all functions and on Schwartz–Bruhat functions.

## Content

Let `R` be a commutative ring with `⅟2`, and `β : X →ₗ[R] Y →ₗ[R] R` a pairing. On `X × Y`,

`polarizedForm β ((x, y), (x', y')) = β x y' - β x' y`

is an alternating form (`polarizedForm_isAlt`) for which `X × 0` and `0 × Y` are isotropic; for a
perfect pairing of finite free modules this is a symplectic module with a polarization (every
symplectic space over a field is of this form; that is not formalized here). For an additive character `ψ : AddChar R ℂ` the
Schrödinger operator of `w = (x₀, y₀)` is

`schrodingerFun ψ β w φ x = ψ (β x y₀ + ½ β x₀ y₀) · φ (x + x₀)`

on functions `φ : X → ℂ`: translation by `x₀` followed by multiplication by the character
`ψ (β · y₀)`, with the phase `ψ (½ β x₀ y₀)` that makes the family symmetric. The operators form a
projective representation of `X × Y`:

`schrodingerFun ψ β w ∘ schrodingerFun ψ β w' = ψ (½ polarizedForm β w w') • schrodingerFun ψ β (w + w')`

(`schrodingerFun_comp`), and since `(w, 0)(w', 0) = (w + w', ½ polarizedForm β w w')` in
`HeisenbergGroup (polarizedForm β)`, the map `(w, t) ↦ ψ t • schrodingerFun ψ β w` is a
representation, `schrodinger ψ β`, with central character `ψ`
(`schrodinger_hasCentralCharacter`). This is the Schrödinger model of the Heisenberg
representation: Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964),
chapter I; Folland, *Harmonic analysis in phase space*, chapter 1; Mœglin–Vignéras–Waldspurger,
*Correspondances de Howe sur un corps p-adique*, chapter 2, section I (page references to be
added).

Three settings of the subject are instances of this one definition: the real case
`X = Y = ℝˡ` with `β` the inner product and `ψ(t) = e^{2πit}` (the operators of
`Langlands.Theta.Real.schrodingerL2` on `L²(ℝˡ)`, through the bridge
`Theta.Real.schrodingerFun_real`), the
case `X = Y = R^κ` with the dot product, and the case `X = Y = M_{α×ν}(E)` with a Hermitian pairing,
for the unitary dual pairs.

When `R` is a nonarchimedean topological ring, `ψ` is continuous (hence locally constant,
`HarmonicAnalysis.isLocallyConstant_of_continuous_addChar`) and `x ↦ β x y` is continuous for each
`y`, the operators preserve the locally constant compactly supported functions on a topological
group `X` (`schrodingerFun_mem`); `schrodingerSB ψ β hψ hβ` is the resulting representation on
`HarmonicAnalysis.SchwartzBruhat X`. Over a nonarchimedean local field, for a perfect pairing of
finite-dimensional spaces and a non-trivial `ψ`, it is smooth, irreducible and admissible
(`Langlands.Theta.Heisenberg.SchrodingerIrreducible`). The predicates `HasCentralCharacter` and
`Normalizes` are those of `Langlands.Theta.Heisenberg.Representation`.

**Change of normalization.** If `β' = a β` for a unit `a`, then `polarizedForm β' = a polarizedForm β`
(`polarizedForm_eq_mul`), `(w, t) ↦ (w, a⁻¹ t)` is an isomorphism of Heisenberg groups
`mulCenEquiv a h : HeisenbergGroup B' ≃* HeisenbergGroup B` for forms with `B' = a B`, and the
Schrödinger representation of `(β', ψ)` is that of `(β, x ↦ ψ(a x))` composed with it
(`schrodinger_comp_mulCenEquiv`, and `schrodingerSB_comp_mulCenEquiv` on Schwartz–Bruhat functions).
A Heisenberg representation of `(W, ½ ⟪,⟫)` with central character `ψ` is therefore one of
`(W, ⟪,⟫)` with central character `ψ_{1/2} : x ↦ ψ(x/2)`; this is how the unitary pair of
`Langlands.Theta.DualPair.Unitary.LeraySplitting` passes between the Library's form `½ ⟪,⟫` and the
book's `⟪,⟫` (GKT §11.1.1, p. 306).

## Relation to the source

No text of this file is taken from the source repository
(<https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`). Its definitions
unify four definitions of the source: `GlobalTheory.RealWeil.rhoFun`
(`PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean`, lines 22–26),
`GlobalTheory.WeilM.schr` (`Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean`, line 116),
`GlobalTheory.SplitUnitary.heisFun` (`PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean`,
line 79), and the clause `∀ t v, ρ ⟨0, t⟩ v = ψ t • v` of `Heisenberg.IsIrrSmoothOf`
(`PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`, lines 53–55), the predicate
`HasCentralCharacter` of `Langlands.Theta.Heisenberg.Representation`.

## Declarations

- `polarizedForm`, `polarizedForm_apply`, `polarizedForm_isAlt`.
- `schrodingerFun`, `schrodingerFun_apply`, `schrodingerFun_zero`, `schrodingerFun_comp`,
  `schrodingerLinear`, `schrodingerLinear_apply`.
- `schrodinger`, `schrodinger_apply`, `schrodinger_ofVec`, `schrodinger_hasCentralCharacter`.
- `mulCenEquiv`, `mulCenEquiv_apply`, `polarizedForm_eq_mul`, `schrodinger_comp_mulCenEquiv`,
  `schrodingerSB_comp_mulCenEquiv`.
- `schrodingerFun_mem`, `schrodingerSB`, `schrodingerSB_apply`,
  `schrodingerSB_hasCentralCharacter`.

## Dependencies

`Langlands.Theta.Heisenberg.Representation`, `Langlands.HarmonicAnalysis.AdditiveCharacterExists` (local
constancy of continuous characters, and `Langlands.HarmonicAnalysis.Basic` for `SchwartzBruhat`);
Mathlib: `RepresentationTheory.Subrepresentation`.
