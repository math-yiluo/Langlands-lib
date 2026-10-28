# Rectangular Schwartz action and raw Fourier data

This module constructs the scalar matrix model at the beginning of JPSS Section 6.1 on the actual space `Matrix (Fin n) (Fin (n + 1)) K`. It supplies coordinates, right translations, the raw last-column partial Fourier integrals with both signs, and the raw full Fourier integral. The full transform and the right action also work in arbitrary rectangular dimensions `r` and `s`.

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983), 367–464, Section 6.1, printed pages 427–428 (one-based PDF pages 62–63). The registered source is `jpss-1983-rankin-selberg`, retained at `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`, SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. Both scanned pages were visually checked. No source-specific errata file was present at `notes/errata/jpss-1983-rankin-selberg.md` in the workspace, current Library, or shared project notes.

On page 427 the source sets `t = r + 1`. Our `n` is its `r = t - 1`. The first `n` columns are the square block `x`, and the last column is `y`. The source's test-function action evaluates `Φ` at `mg`; its last-column transform uses the conjugate character. Page 428, formula (6), defines the full Fourier transform with a plus-sign trace pairing. The entry sum below expresses that pairing without introducing a transpose convention into the API.

The finite-coordinate homeomorphism, rank-general versions of the entry pairing and right action, opposite-sign partial companion, and complex-linear maps into all functions are derived API packaging. The support, convergence and elementary action proofs are internal consequences of the actual definitions and the existing measure and test-function infrastructure; JPSS does not present this Lean packaging as separate results.

## Coordinates and last-column slices

`rectangularFirstColumns m` is `fun i j => m i j.castSucc`, and `rectangularLastColumn m` is `fun i => m i (Fin.last n)`. `rectangularJoin x y` is the actual matrix `[x,y]`, defined by `Fin.lastCases`. Its `castSucc` and `last` evaluation lemmas identify every entry. The two projection-after-join laws and `rectangularJoin_split` prove both inverse laws.

For any topological space `K`, `rectangularSplit` bundles these maps as a homeomorphism from the matrix space to `Matrix (Fin n) (Fin n) K × (Fin n → K)`. Continuity is proved on every coordinate. The lemmas `rectangularSplit_apply` and `rectangularSplit_symm_apply` expose its maps. No nonempty-rank assumption is used, so the same construction covers `n = 0`.

For a Hausdorff space `K`, `rectangularSlice Φ x` is the actual Schwartz–Bruhat function `u ↦ Φ (rectangularJoin x u)`. Local constancy follows from continuity of the fixed-first-block inclusion. Compact support requires a separate argument: if the slice is nonzero at `u`, then `[x,u]` lies in the support of `Φ` and its last-column projection equals `u`. Thus the slice's support lies in the last-column projection of `tsupport Φ`. That projection is compact by continuity and is closed by Hausdorffness. `HasCompactSupport.intro` proves the slice has compact support. This proof does not infer compactness of a preimage from continuity alone.

## Right action

Assume `K` is a field with a topology and `IsTopologicalRing K`. For any `r s : Nat` and `g : Langlands.GeneralLinear s K`, `rectangularHomeomorph g` sends the actual matrix `m` to `m * g.val`. Its inverse uses `g⁻¹`. Matrix associativity and the unit inverse laws prove the inverse identities; continuity follows from continuity of matrix multiplication by a constant.

`rectangularTranslate g` reuses `Hecke.TestFunction.pullback` to give a complex-linear equivalence on the actual rectangular Schwartz–Bruhat space. Its evaluation lemma states `rectangularTranslate g Φ m = Φ (m * g.val)`. The identity and composition lemmas prove

`rectangularTranslate (g * h) Φ = rectangularTranslate g (rectangularTranslate h Φ)`.

`rectangularSchwartzRepresentation` bundles precisely this action as a representation. The construction follows the published `rowHomeomorph`, `rowTranslate` and `rowSchwartzRepresentation` pattern and imports that infrastructure. Specializing `r = n` and `s = n + 1` gives the JPSS Section 6 test space and group.

## Full Fourier data

The measure is always the existing `Langlands.RankinSelberg.rectangularMeasure μ r s` built from the supplied `μ : AdditiveHaarMeasure K`. No new scalar measure or normalization is chosen. `rectangularPairing a b` is the plus-sign entry sum `∑ i, ∑ j, a i j * b i j`. The raw integral is

`rectangularFourierIntegral ψ μ f b = ∫ a, f a * ψ.complex (rectangularPairing a b) ∂rectangularMeasure μ r s`.

Here `ψ` is an actual `UnitaryAdditiveCharacter K`. The field topology is assumed to satisfy `IsTopologicalRing K`, and `K` has a measurable-space structure. For convergence and the complex-linear map, sufficient additional hypotheses are `SigmaFinite μ.measure` and `BorelSpace (Matrix (Fin r) (Fin s) K)`. The matrix measurable-space structure is the existing product structure induced from `K`; the Borel-space compatibility is explicit. No separate local compactness or second-countability assumption is needed once the supplied Haar measure and these hypotheses are available.

`rectangularFourierIntegrand_integrable` proves convergence on actual Schwartz inputs. The entry pairing is continuous, so the integrand is continuous. Multiplication by the character leaves its support contained in the Schwartz support. The iterated finite product measure is finite on compact sets, using sigma-finiteness of the scalar input, and continuous compactly supported functions are integrable. `rectangularFourierTransform` bundles the resulting map into all complex functions as a complex-linear map. Additivity uses convergence of both summands; scalar compatibility uses `integral_const_mul`.

## Partial Fourier data and signs

`partialFourierIntegral ψ μ f m` integrates in the last-column variable against the existing `rowMeasure μ n`. Its evaluation on `[x,y]`, given by `partialFourierIntegral_join`, is exactly

`∫ u, f (rectangularJoin x u) * ψ.complex (-(∑ i, y i * u i)) ∂rowMeasure μ n`.

Thus the default partial transform uses the inverse character from page 427. `partialFourierPlusIntegral` is the opposite-sign companion, and `partialFourierPlusIntegral_join` displays the same formula without the minus sign. These raw integrals accept arbitrary complex-valued functions on the actual matrix space; convergence is asserted only for Schwartz inputs under the hypotheses below.

For partial convergence and linearity, assume a topological field as above, `T2Space K`, `SigmaFinite μ.measure`, and the explicit compatibility `BorelSpace (Fin n → K)` for the row measurable space. `partialFourierIntegrand_integrable` and `partialFourierPlusIntegrand_integrable` combine the proved compact support of the fixed-first-block slice with continuity of the corresponding character kernel. Finite-on-compactness of `rowMeasure μ n` then gives integrability. `partialFourierTransform` and `partialFourierPlusTransform` are complex-linear maps from actual rectangular Schwartz functions into all complex functions, with direct evaluation lemmas. Their additivity and scalar proofs use the same Bochner integral laws as the full transform.

The codomains of all three transforms are spaces of all functions. This unit supplies no assertion or assumed certificate of preservation of Schwartz space, inversion, a self-dual measure, the Fourier-conjugated `rho0` action, covariance, vector-valued Whittaker integrals, or analytic base theorems. In particular, no closure or inversion proposition is used as if it were a proof.
