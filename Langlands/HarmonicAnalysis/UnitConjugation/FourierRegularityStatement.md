# Harish-Chandra's Theorem 4.4: local summability on the Lie algebra of `Aˣ`

The module `Langlands.HarmonicAnalysis.UnitConjugation.FourierRegularityStatement` states, as
the proposition `Langlands.HarmonicAnalysis.LieAlgebraFourierRegularityStatement.{u, v}`, the
local summability clause of Harish-Chandra's Theorem 4.4 for the Lie algebra `A` of the unit
group of a finite-dimensional semisimple algebra over a nonarchimedean local field of
characteristic zero: the Fourier transform of a conjugation-invariant distribution supported in
the closure of the saturation of a compact set is given by a locally integrable function. The
statement is **not** proved here.

## Statement

`LieAlgebraFourierRegularityStatement.{u, v}` quantifies over

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`: a nonarchimedean local field of characteristic
  zero, that is a finite extension of some `ℚ_p`;
- `A : Type v` with `[Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]`: a
  finite-dimensional semisimple associative `F`-algebra with its module topology and Borel
  σ-algebra. Its topological ring structure is Mathlib's `IsModuleTopology.isTopologicalRing`,
  bound with `haveI` inside the statement;
- `ψ : UnitaryAdditiveCharacter F`, a nontrivial continuous unitary character;
- `B : LinearMap.BilinForm F A` with `hB : IsInvariantPairing B`: symmetric, nondegenerate and
  invariant under conjugation by `Aˣ`;
- `μ : AdditiveHaarMeasure A`, the Library's additive Haar measure (any normalization);
- a compact `ω ⊆ A` and `T ∈ invariantSupportedIn ω`, that is `T` invariant under conjugation by
  `Aˣ` and supported in the closure of `⋃_u u ω u⁻¹` (Harish-Chandra's `J(ω)`).

The claim: there is `Θ : A → ℂ` with `LocallyIntegrable Θ μ.measure` and

`distributionFourier ψ hB.isSymm hB.nondegenerate μ T f = ∫ X, Θ X * f X ∂μ.measure`

for **every** Schwartz–Bruhat function `f : SchwartzBruhat A`, where the left side is
`T(f̂)` with `f̂(Y) = ∫ ψ(B(Y, X)) f(X) dμ(X)`
(`Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier`).

The universes of `F` and `A` are independent. Quantifying over every `ψ`, `B` and `μ` is
Harish-Chandra's statement for fixed choices: replacing `μ` by `c μ` multiplies both sides by
`c`, so one `Θ` serves every Haar measure, and the theorem holds for each admissible `ψ` and `B`.

## Scope: unit groups of semisimple algebras

`Aˣ` is the group of `F`-points of the connected reductive group `GL₁(A)` and `A` with the
commutator bracket is its Lie algebra, with the adjoint action `X ↦ u X u⁻¹`. By Wedderburn–Artin
(Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`) `A` is a finite
product of matrix algebras `M_{d_i}(D_i)` over finite-dimensional division `F`-algebras `D_i`, so
`Aˣ = ∏ GL_{d_i}(D_i)`. The scope therefore contains finite products, matrix algebras over finite
field extensions of `F` (`D_i` commutative) and over central division algebras (`D_i` nonsplit).
Nonsplit factors occur among the algebras that arise by descent: the fixed points in a matrix
algebra of a semisimple automorphism, such as a twisted conjugation over a cyclic extension, form
a semisimple algebra whose simple factors can be matrix algebras over noncommutative division
algebras.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15).

- Introduction, printed pp. 1–2 (PDF pp. 16–17): `Ω` a p-adic field, assumed of characteristic
  zero; `G` the group of rational points of a connected reductive group, `g` its Lie algebra with
  the adjoint action; `J`, `ω^G`, `J(ω)`; the invariant form `B`, the character `χ ≠ 1`, the
  Haar measure `dX`, `f̂(Y) = ∫ χ(B(Y, X)) f(X) dX` and `T̂(f) = T(f̂)`.
- Theorem 4.4 (Theorem 3 of the original), stated on printed p. 2 (PDF p. 17) and printed p. 31
  (PDF p. 46): for compact `ω ⊆ g` and `T ∈ J(ω)` there is a locally summable function `F` on
  `g` with (1) `T̂(f) = ∫_g F(X) f(X) dX` for all `f ∈ C_c^∞(g)`, (2) `F` locally constant on
  the regular set `g'`, (3) `|η|^{1/2} F` locally bounded. The proof on printed p. 31 proves
  clauses (1) and (2), with the local summability; it begins "This proof does not prove (3)",
  and Remark 4.5 (printed p. 32) returns to (3). It uses Lemma 4.3, Corollary 4.2 with Howe's
  finiteness theorem (Theorem 12.1), and the parts of Theorem 1.1 already proved for regular
  orbits.

This statement is clause (1) with the local summability of the function. The Library's
`LocallyIntegrable` (integrable on a neighbourhood of every point) is local summability on the
locally compact space `A`.

Clozel, *Characters of non-connected, reductive p-adic groups*, Canad. J. Math. 39 (1987),
source ID `clozel-1987-nonconnected-characters` (PDF page = printed page − 148), §3.4, printed
pp. 155–156 (PDF pp. 7–8), uses exactly this part. For a descended distribution `θ₀` on the Lie
algebra `m` of the connected centralizer `M` of a semisimple element, with `J₀` the invariant
distributions whose support is compact modulo conjugation, Howe's theory gives
`j_{Λ*}(θ̂₀) ∈ j_{Λ*}(J₀)`: the restrictions of `θ̂₀` and of some `T ∈ J₀` to the
`Λ*`-invariant test functions coincide. Fourier inversion then shows that `θ₀` agrees on Clozel's
lattice `Λ` with the Fourier transform of an element of `J₀`, and "Theorem 3 of [8]"
(Harish-Chandra's Theorem 4.4) gives the local integrability of `θ₀` near `0`. The Fourier
transform there is defined by `χ(B(X, Y))` for a nondegenerate invariant form `B` on `m`.

## Not stated here

Clauses (2) and (3) of Theorem 4.4 (local constancy on the regular set, local boundedness of
`|η|^{1/2} F`), Howe's finiteness theorem, the local expansion by nilpotent orbital integrals
(Theorem 5.11), the specialization to orbital distributions, and anything in positive
characteristic.
