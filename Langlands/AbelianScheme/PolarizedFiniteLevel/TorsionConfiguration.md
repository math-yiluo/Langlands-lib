# Equivalence of torsion configurations of ordinary polarized full-level data

The module `Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfiguration`
defines one predicate, `Datum.TorsionConfigurationEquivalent`. It proves nothing.

## The definition

Fix `P : Prerequisites.{u}`, a scheme `S : Scheme.{u}` and natural numbers
`g d n`. For two data `a b : Datum P S g d n` over the same base,
`a.TorsionConfigurationEquivalent b` says the following. There is an isomorphism
of `𝒪_S`-modules

`φ : a.rigidificationModule ≅ b.rigidificationModule`

such that for every coefficient tuple `r : Fin (2 * g) → ZMod n` there is an
isomorphism of `𝒪_S`-modules

`ψ : (a.torsionPoint r)^* a.cubicBundle ≅ (b.torsionPoint r)^* b.cubicBundle`

(both sides are `Scheme.Modules.pullback` of the underlying module of the cubic
bundle) with

`φ.hom ≫ b.torsionEvaluation r = a.torsionEvaluation r ≫ ψ.hom`.

The isomorphism `φ` is the same for all `r`. The isomorphism `ψ` may depend on `r`.

The Library objects used are the following, all published:

- `Datum.cubicBundle` (module `CanonicalBundle`) is the tensor cube `L³` of the
  datum's canonical bundle `L`. The canonical bundle is the diagonal Poincaré
  bundle of the polarization, `L^Δ(ω)` in GIT Definition 7.5.
- `Datum.rigidificationModule` (module `CanonicalBundle`) is the direct image
  `E = π_* L³` along the structure morphism `π` of the abelian scheme.
- `Datum.torsionPoint r` (module `FrameLocus`) is the torsion section
  `P_r = Σ_i r_i · s_i` of the ordered full level `(s_i)`.
- `Datum.torsionEvaluation r : E ⟶ P_r^* L³` (module `FrameLocus`) is evaluation
  at `P_r`. It is the pullback along `P_r` of the adjoint of the cubic evaluation
  `π^* E ⟶ L³`.

## Meaning over a field

Let `S = Spec K` for a field `K`. Then `E` amounts to the vector space
`V = H⁰(A, L³)`. Each `P_r^* L³` amounts to the fibre line `L³(P_r)`, and
`torsionEvaluation r` is the evaluation `V → L³(P_r)` at the point `P_r`. The
condition with `r` fixed says that `φ` carries the evaluation of `a` at its `r`-th
torsion point to the evaluation of `b` at its `r`-th torsion point, up to a
linear isomorphism of the target lines. If both evaluations at `P_r` are nonzero,
this is equivalent to `φ` mapping the hyperplane of sections of `L_a³` vanishing at
`P_r^a` onto the hyperplane of sections of `L_b³` vanishing at `P_r^b`.

Suppose all evaluations are nonzero, for instance when `L³` is globally generated.
Then each torsion point `P_r` determines the point `[ev_r]` of the projective space
of lines in `V^∨`. This is the image of `P_r` under the morphism given by the
complete linear system `|L³|`. The predicate then says that the projective linear
isomorphism induced by `φ` carries the indexed point family `([ev^a_r])_r` to the
indexed point family `([ev^b_r])_r`, label by label. In words, the two embedded
configurations of labelled `n`-torsion points are projectively equivalent. The
definition uses the evaluation maps directly and does not choose an embedding.

The module proves no properties of the predicate (reflexivity, symmetry,
transitivity, compatibility with base change). Isomorphic data are expected to
have equivalent torsion configurations, but this is not proved here.

## Provenance

This is an internal definition. GIT does not define it. It records the
projective configuration of the labelled torsion points in the cubic embedding.
GIT works with this embedding in Chapter 7, §2 (Mumford–Fogarty–Kirwan,
*Geometric Invariant Theory*, 3rd edition, registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).
Definition 7.5 (printed p.130, PDF p.143) defines a linear rigidification as an
isomorphism `P(π_*(L^Δ(ω)³)) ≅ P^m × S`. The text after Definition 7.6 (printed
p.131, PDF p.144) uses the resulting embedding together with the identity
section and the `2g` level sections. The predicate here is stated without a
choice of basis of `E`, so it makes sense over every base.

## Role

The predicate is the interface between two companion statements,
`TorsionBracketMapStatement` and `TorsionConfigurationDeterminationStatement`.
Together with the accepted `LargeLevelFiniteTypeStatement`, they give
`LargeLevelQuasiFiniteProjectiveStatement` through the proved definition
`largeLevelQuasiFiniteProjective_of_torsionBrackets` (module
`LargeLevelQuasiFiniteProjectiveBracketReduction`).
