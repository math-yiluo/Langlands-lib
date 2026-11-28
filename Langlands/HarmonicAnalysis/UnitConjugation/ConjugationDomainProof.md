# Harish-Chandra's Lemma 4.3 for the Lie algebra of `Aˣ`: proof

The module `Langlands.HarmonicAnalysis.UnitConjugation.ConjugationDomainProof` proves the
proposition `Langlands.HarmonicAnalysis.LieAlgebraConjugationDomainStatement.{u, v}` of
`Langlands.HarmonicAnalysis.UnitConjugation.ConjugationDomainStatement` as the theorem
`Langlands.HarmonicAnalysis.lieAlgebraConjugationDomain`, with the universes of the field and
of the algebra independent. The statement is used unchanged and no hypothesis is added.

For a nonarchimedean local field `F` of characteristic zero, a finite-dimensional semisimple
`F`-algebra `A` with its module topology and a compact set `ω ⊆ A`, the theorem gives a compact
set `ω₀ ⊆ A` and a set `D ⊆ A` which is open and closed, invariant under every conjugation
`X ↦ u X u⁻¹` by a unit `u`, and satisfies `ω ⊆ D ⊆ conjugationSaturation ω₀`.

## Source and route

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions`, §4, Lemma 4.3 (Lemma 10), printed
p. 31 (PDF p. 46). Harish-Chandra's proof takes representatives of the conjugacy classes of
Cartan subalgebras, uses that every orbit closure contains a semisimple element and applies
Lemma 2.6 at such an element.

The proof here is special to `G = GL₁(A)` and does not follow that route. The domain `D` is cut
out by bounds on the coefficients of the characteristic polynomial of left multiplication. The
inclusion `D ⊆ ω₀^G` comes from the conjugacy of integral elements into a fixed compact set,
which is proved through the Wedderburn–Artin decomposition of `A` and the ultrametric absolute
value on the division algebras that occur. This allows finite products and division algebras
that are not split.

## Declarations

In the namespace `Langlands.HarmonicAnalysis.ConjugationDomain`:

- `charpolyCoefficients F X : Fin (Module.finrank F A) → F`, the coefficients of
  `T ^ 0, …, T ^ (n - 1)` in the characteristic polynomial `χ_X` of left multiplication
  `Algebra.lmul F A X` on the `n`-dimensional `F`-vector space `A`.
- `aeval_charpoly_lmul`: `χ_X (X) = 0`. Cayley–Hamilton (`LinearMap.aeval_self_charpoly`) gives
  `χ_X (lmul X) = lmul (χ_X (X)) = 0`, and `Algebra.lmul` is injective.
- `charpolyCoefficients_conjugation`: the coefficients of `u X u⁻¹` and `X` agree, because
  left multiplication by `u X u⁻¹` is the conjugate of left multiplication by `X` by the linear
  equivalence `Units.mulLeftLinearEquiv F A u` (`LinearEquiv.charpoly_conj`).
- `continuous_charpolyCoefficients`: for a topological field `F` and the module topology on `A`,
  each coefficient is the evaluation of the universal coefficient polynomial
  `Matrix.charpoly.univ` at the entries of the matrix of `lmul X` in the basis
  `Module.finBasis F A` (`Matrix.charpoly.univ_coeff_eval₂Hom`, `LinearMap.charpoly_toMatrix`).
  The entries are linear in `X`, hence continuous for the module topology
  (`IsModuleTopology.continuous_of_linearMap`), and polynomial evaluation is continuous.
- `exists_isCompact_conj_of_integral`: let `F` be a complete, locally compact, nontrivially
  normed field with ultrametric distance, and `A` a finite-dimensional semisimple `F`-algebra with
  a topological ring structure for which scalar multiplication is continuous. Then there is a
  compact `K ⊆ A` such that for every `Y ∈ A` and every monic `p : F[X]` with `‖p.coeff i‖ ≤ 1`
  for all `i` and `aeval Y p = 0`, some unit `u` has `u Y u⁻¹ ∈ K`.

## Proof of `exists_isCompact_conj_of_integral`

1. Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite` gives an
   `F`-algebra isomorphism `e : A ≃ₐ[F] B` with `B = Π i, Matrix (Fin (d i)) (Fin (d i)) (Dᵢ)`,
   where each `Dᵢ` is a division ring with a finite-dimensional `F`-algebra structure (not
   necessarily central).
2. Each `Dᵢ` is given the norm `CentralDivision.regularAbsoluteValue F Dᵢ`,
   `x ↦ ‖Algebra.norm F x‖ ^ (1 / [Dᵢ : F])`, through `CentralDivision.regularNormedRing` and
   `CentralDivision.regularNormedAlgebra`; this makes `Dᵢ` a finite-dimensional normed `F`-space,
   proper by `FiniteDimensional.proper` since `F` is locally compact. Hence
   `KB = {M ∈ B | ‖M i a b‖ ≤ 1 for all i, a, b}` is compact (`isCompact_univ_pi`,
   `isCompact_closedBall`). With the product topology `B` is a finite-dimensional Hausdorff
   topological `F`-vector space, so the linear map `e.symm` is continuous
   (`LinearMap.continuous_of_finiteDimensional`), and `K = e.symm '' KB` is compact.
3. Given `Y` and `p`, each component `Zᵢ = e Y i` satisfies `aeval Zᵢ p = 0`, by
   `Polynomial.aeval_algHom_apply` for `e` and for the evaluation `Pi.evalAlgHom`. For the
   valuation `vᵢ = CentralDivision.regularNormValuation F Dᵢ`,
   `vᵢ (algebraMap F Dᵢ c) = ‖c‖₊ ^ [Dᵢ : F] ≤ 1` for each coefficient `c` of `p`
   (`CentralDivision.regularNormValuation_algebraMap`).
   `LinearAlgebra.DivisionMatrixIntegerConjugation.exists_units_conj_integral_of_aeval` gives
   units `uᵢ` of the matrix rings with `vᵢ ((uᵢ Zᵢ uᵢ⁻¹) a b) ≤ 1`. Since
   `regularAbsoluteValue F Dᵢ x = (vᵢ x) ^ (1 / [Dᵢ : F])`, these entries have norm at most one.
4. The units assemble to a unit `U` of `B` (`MulEquiv.piUnits`), and `U' = e.symm U` is a unit of
   `A` with `U' Y U'⁻¹ = e.symm (U (e Y) U⁻¹) ∈ e.symm '' KB = K`.

## Proof of `lieAlgebraConjugationDomain`

Fix `F`, `A` and `ω`. The topological ring structure of `A` is
`IsModuleTopology.isTopologicalRing F A`, as in the statement. The field `F` is given the norm
`LocalGalois.localNormedField F`, whose topology is the given topology of `F` by definition
(`LocalGalois.localNormedField_topology` is `rfl`), and which is complete and ultrametric
(`localNormedField_complete`, `localNormedField_ultrametric`); `F` is locally compact by
`IsNonarchimedeanLocalField`. Let `K` be the compact set of `exists_isCompact_conj_of_integral`.

1. The continuous function `charpolyCoefficients F` is bounded on the compact set `ω`, say by
   `C` in the sup norm (`IsCompact.exists_bound_of_continuousOn`). Choose `t : F` with
   `0 < ‖t‖ < (max C 0 + 1)⁻¹` (`NormedField.exists_norm_lt`); then `‖t‖ ≤ 1` and
   `‖t‖ * C ≤ 1`.
2. Put `D = {X | ∀ i, ‖t * charpolyCoefficients F X i‖ ≤ 1}` and `ω₀ = t⁻¹ • K` (the image of
   `K` under `Z ↦ t⁻¹ • Z`, compact by continuity of scalar multiplication).
3. `D` is open and closed: it is the finite intersection over `i` of the preimages of the closed
   unit ball of `F`, which is open and closed in the ultrametric space `F`
   (`IsUltrametricDist.isClopen_closedBall`), under continuous maps.
4. `D` is invariant under conjugation by `charpolyCoefficients_conjugation`.
5. `ω ⊆ D`: for `X ∈ ω`, `‖t * cᵢ(X)‖ = ‖t‖ ‖cᵢ(X)‖ ≤ ‖t‖ * C ≤ 1`.
6. `D ⊆ conjugationSaturation ω₀`: let `X ∈ D` and `p = χ_X`, monic of degree
   `n = Module.finrank F A` with `aeval X p = 0`. The polynomial `q = scaleRoots p t`, with
   coefficients `p_i t ^ (n - i)`, is monic (`Polynomial.monic_scaleRoots_iff`) and has the root
   `algebraMap F A t * X = t • X` (`Polynomial.scaleRoots_aeval_eq_zero`). Its coefficients have
   norm at most one: for `i < n`, `‖p_i‖ ‖t‖ ^ (n - i) ≤ ‖t‖ ‖p_i‖ ≤ 1` because `‖t‖ ≤ 1` and
   `n - i ≥ 1`; for `i = n` the coefficient is `1`; for `i > n` it is `0`. Hence some unit `w`
   has `w (t • X) w⁻¹ ∈ K`, so `Z = t⁻¹ • w (t • X) w⁻¹ = w X w⁻¹` lies in `ω₀`, and
   `X = w⁻¹ Z w` lies in `conjugationSaturation ω₀`.
