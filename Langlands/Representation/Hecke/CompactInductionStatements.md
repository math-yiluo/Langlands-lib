# The compact Hecke-induction comparison: statement

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.6, (III.2.6.1)–(III.2.6.2) and
the Theorem, printed pp.75–76 / PDF pp.81–82. Source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`CompactInductionHeckeStatement` is a closed `Prop`-valued definition.
It asserts a natural isomorphism `p` from the actual `Homomorphism.P`
induction of the Hecke module of a smooth `H` representation to the
Hecke module of the actual compact function induction, twisted by the
constructed relative modular character. The subgroup `H` is arbitrary
closed; `G` is Hausdorff, locally compact and nonarchimedean. Local
compactness of `H` follows from closedness. Both left Haar measures are
supplied, and group and input carrier universes are independent.

The precise right module law (III.2.6.1) is part of the conclusion:

`(T · a)(x) = ∫ h : H, ΔG(h) a(h) T(xh⁻¹) dμH(h)`.

Here `Δ = haarScale` is Mathlib's modular factor, the inverse of
Renard's `δ`. This is exactly the action of `𝒟(H)` on `𝒟(G)`
through the Haar identifications. In particular the statement does not
replace it by unweighted right translation.

The natural isomorphism is characterized on the original elementary
tensor `T ⊗ w` by

`λ(p(T ⊗ w)(g)) = ∫ h : H, T((hg)⁻¹) ΔG(h) λ(ρ(h⁻¹)w) dμH(h)`

for every algebraic complex-linear functional `λ : W →ₗ[ℂ] ℂ`.
Renard writes the same formula before (III.2.6.2) as
`∫ check(f)(hg) (δG ρ)(h⁻¹)w dμH(h)`, for `T = f μG`;
`δG(h⁻¹) = ΔG(h)` accounts for the coefficient in Lean.
The output representation is twisted by
`δ_{H\G} = δG|H / δH = ΔH / ΔG|H`, using the actual
`relativeModularCharacter`.

The scalarization avoids imposing a topology or completeness on `W`;
all its algebraic linear functionals separate vectors, so the displayed
identities uniquely specify the vector-valued map in the source. An
existential natural isomorphism is a conclusion, including existence
and bijectivity of that prescribed map, its Hecke equivariance, and
naturality in `W`. The elementary tensors belong to exactly the balanced
quotient used by `NondegenerateTensorFunctor.P`; no balancing premise,
map certificate, or isomorphism is assumed.

`compactModularEvaluation` only exposes evaluation of the published
compact-function carrier; it introduces no new induction object.
The comparison is expressed directly after the published smooth-to-Hecke
functor, without an additional III.1.4 equivalence hypothesis. By that
equivalence this is the asserted natural isomorphism in `M(G)`.
The file proves none of these conclusions; proofs belong to a separate task.
