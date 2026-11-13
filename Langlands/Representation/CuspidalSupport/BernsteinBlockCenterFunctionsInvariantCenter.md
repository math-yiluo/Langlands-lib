# `ℨ_D^{W(D)} ⊂ ℨ_Ω` for an actual Bernstein cuspidal datum (Renard VI.10.4, proof)

Worker 98. Statement module for one step of the proof of Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
VI.10.4, Theorem (printed pp.211–212 / PDF pp.217–218). The module contains one
closed proposition, `BernsteinInvariantCenterInclusionStatement`, and no proof.
It is an intermediate statement for the conditional reduction of
`BernsteinBlockCenterFunctionsStatement` (Task 5545, first sentence of the
Theorem).

## Renard's notation and the step in question

In the proof of VI.10.4, `D = (M, ρ)` is a cuspidal datum with inertial
class `D` on `M`. `ρ₀` is an irreducible constituent of `ρ|_{⁰M}` and
`Π_D = ind_{⁰M}^{M} ρ₀`, a progenerator of the block of `M` attached to `D`.
`ℨ_D` is the centre of `R_D = End_M(Π_D)`. By VI.4.4 it is the algebra of
polynomial functions on `Irr(M)_D`; the function of `ζ ∈ ℨ_D` takes, at
`ρ ⊗ ω`, the scalar by which `ζ` acts on `ρ ⊗ ω`. `W(D)` is the stabiliser of
`D` in `W(M) = N_G(M)/M`. It acts on `Irr(M)_D` and hence on `ℨ_D`.
`R_Ω = End_G(i_P^G Π_D)` and `ℨ_Ω` is its centre. Here `ℨ_D` is viewed
inside `R_Ω` by functoriality of `i_P^G`.

On printed p.211 / PDF p.217, Renard proves `ℨ_Ω ⊂ ℨ_D^{W(D)}`. He then states
that the inclusion is an equality. Its converse, `ℨ_D^{W(D)} ⊂ ℨ_Ω`, is the
bimodule-filtration argument that ends on printed p.212 / PDF p.218 with
`ℨ_Ω = ⋂_{w ∈ W(D)} 𝒞_{ℨ_D}(Hom_M(Π_D, w·Π_D)) = ℨ_D^{W(D)}`. This
module states that converse inclusion. In words: a `W(D)`-invariant element
`ζ` of `ℨ_D` induces a central element `i_P^G(ζ)` of `R_Ω`.

## The Lean statement

`BernsteinInvariantCenterInclusionStatement.{uF, uV}` has the binders of the
published `BernsteinBlockCenterFunctionsStatement`, with the same inline
`haveI`/`letI` instances for `G` and the Levi `M = bernsteinLeviScheme i ν a.roots`.
These are: `F, G, T, i, ν`, the topology and group instances on `G(F)`, a
`BernsteinStandardFamily i ν`, and an actual cuspidal datum `a` with carriers
in `Type (max uF uV)`. Then for

- every smooth representation `ρ₀` of `⁰M = rationalCommonNormKernel M` (carriers
  in `Type (max uF uV)`) that is irreducible,
- every `⁰M`-map `j : ρ₀ → ρ|_{⁰M}` (`ρ = a.representation`, restricted with
  `SmoothRep.restrictSubgroup`) that is injective,

and with the local names

- `X = X(M)`, the published `unramifiedCharacters` of `M`;
- `twist ω = rationalUnramifiedTwist M ω ρ`, that is `ρ ⊗ ω`;
- `Assoc ω ω'`: there is a `RationalLeviConjugacy` `c` of the standard Levi of
  `a` to itself with `ρ ⊗ ω ≅ c^*(ρ ⊗ ω')`. This is the same relation as in
  `BernsteinBlockCenterFunctionsStatement`: `(M, ρ ⊗ ω)` and `(M, ρ ⊗ ω')` are
  associated, i.e. `ρ ⊗ ω'` is a `W(D)`-translate of `ρ ⊗ ω`;
- `piD = rationalNormKernelSummandInduction M ρ₀`, the published
  `ind_{⁰M}^{M} ρ₀`, which is `Π_D`;
- `I = bernsteinStandardRepresentedInductionFunctor i ν family a.roots`, the
  published normalized parabolic induction `i_P^G` along the standard
  parabolic of `a`, in the represented-parabolic interface. Through the
  published `bernsteinStandardRepresentedInductionIso`, its objects are the
  literal inductions `ind ω` of `BernsteinBlockCenterFunctionsStatement`;

the statement says: for every `ζ ∈ Subring.center (End piD)`, the following
implication holds. Assume that whenever `Assoc ω ω'` and `ζ` acts, by
precomposition, as a scalar `c` on every map `Π_D → ρ ⊗ ω`, it acts by the same
`c` on every map `Π_D → ρ ⊗ ω'`. Then `I.map ζ ∈ Subring.center (End (I.obj piD))`.

### Why the hypothesis is `W(D)`-invariance

By VI.4.4, in the form proved in `BernsteinBlockCenterFunctionsLevi`
(`BernsteinLeviCenterVarietyStatement`), a central `ζ` acts on every map
`Π_D → ρ ⊗ ω` by the scalar `Ψ ζ ω`, the value at `ρ ⊗ ω` of the function of
`ζ`. The same module gives a surjection `Π_D → ρ ⊗ ω`, so these Hom spaces are
nonzero. The hypothesis therefore says exactly `Ψ ζ ω = Ψ ζ ω'` whenever
`ρ ⊗ ω` and `ρ ⊗ ω'` are associated. An element `w ∈ W(M)` carrying
`ρ ⊗ ω` to `ρ ⊗ ω'` maps `D` to itself, so it lies in `W(D)`. Conversely,
every `w ∈ W(D)` carries each point of `Irr(M)_D` to an associated point. The
hypothesis is thus the `W(D)`-invariance of the function of `ζ`, phrased
through the actions on the `ρ ⊗ ω` so that it needs no explicit `W(D)`-action
on `ℨ_D`.

### Why the conclusion is `ζ ∈ ℨ_Ω`

Renard identifies `ℨ_Ω` with `𝒞_{ℨ_D}(R_Ω)`, the elements of `ℨ_D` that commute
with `R_Ω`. Here `ℨ_D` acts on `R_Ω ≅ Hom_M(Π_D, r_D i_P^G Π_D)` on the left by
functoriality and on the right by precomposition. In terms of
`R_Ω = End_G(i_P^G Π_D)` these are post- and precomposition by `i_P^G(ζ)`. So
`ζ ∈ 𝒞_{ℨ_D}(R_Ω)` means exactly that `i_P^G(ζ)` is central in `R_Ω`, which is
the conclusion `I.map ζ ∈ Subring.center (End (I.obj piD))`.

## Choices and provenance

- **Provenance: derived.** This is one step of Renard's proof, the inclusion
  `ℨ_D^{W(D)} ⊂ ℨ_Ω`, stated for the actual standard cuspidal data of the
  published Bernstein framework. Renard states the equality
  `ℨ_Ω = ℨ_D^{W(D)}`. The opposite inclusion is not stated here: the reduction
  of `BernsteinBlockCenterFunctionsStatement` derives what it needs of it
  from the scalar computation and the other published statements.
- `Π_D` and `ℨ_D` are those of the published VI.4.4 statement
  (`RationalSummandCenterVarietyStatement`), at the group `M_a`.
- `i_P^G` is the represented-parabolic functor rather than the literal
  `normalizedInductionFunctor` of `BernsteinBlockCenterFunctionsStatement`.
  The two agree objectwise through `bernsteinStandardRepresentedInductionIso`.
  The represented form is the one used by the published
  `RepresentedParabolic.InducedProgeneratorCenterInclusionStatement` (VI.10.4,
  `ℨ_Ω ⊂ ℨ_D`), so the same scalar computation serves both inclusions.
- Renard takes `P` to be any parabolic with Levi `M`; the standard parabolic
  of the datum is one such choice.
- `j` only records that `ρ₀` is a constituent of `ρ|_{⁰M}`, as in Renard's
  definition of `Π_D`. Its existence is proved in `BernsteinBlockCenterFunctionsLevi`.
