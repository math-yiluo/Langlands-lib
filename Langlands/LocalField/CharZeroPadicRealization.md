# P-adic realization of a characteristic-zero local field

`Langlands.CharZeroLocalField` turns an arbitrary `F : Type u` with `[Field F]`,
`[ValuativeRel F]`, `[TopologicalSpace F]`, `[IsNonarchimedeanLocalField F]`
and `[CharZero F]` into a `PadicField` with `TopologicalData`. The carrier is
`F` itself, not a replacement field up to isomorphism. The point of the adapter
is to apply the Library's bundled p-adic results to a field presented using the
unbundled hypotheses, as in the square-integrable non-induction step of Task
7882.

## Interface

- `residueChar F` is `ringChar 𝓀[F]`, the characteristic of the residue field,
  **not** the residue cardinality. It is prime by `residueChar_prime`, with
  `fact_residueChar_prime` available for the `Padic` type. This part does not
  require characteristic zero.
- `padicEmbedding F : ℚ_[residueChar F] →+* F` is the continuous extension of the
  rational embedding. As a ring homomorphism between fields it is injective.
  `isEquiv_comap_padicEmbedding` compares the pullback of `valuation F` with
  `Padic.mulValuation` up to valuation equivalence, not pointwise equality of
  numerical norms.
- `padicAlgebra F` is the algebra of this map; it is explicit data, not a
  global algebra instance. `continuousSMul`, `finiteDimensional`,
  `isModuleTopology` and `valuativeExtension` apply to this specific algebra.
- `padicField F` uses `PadicField.ofField F`. `topologicalData F` supplies the
  original topology, valuative relation and local-field certificate, with the
  two new compatibility proofs for that algebra. `padicField_carrier`,
  `padicField_field`, `topologicalData_topology`, `topologicalData_valuativeRel`
  and `topologicalData_localField` express the definitional identifications.
  The uniform structure used in the construction is local to the proof; no
  topology or valuation instance is changed for consumers.

## Implemented construction

1. Put `p = residueChar F`. All integers are integral in `F`. Reducing a
   natural number modulo the maximal ideal shows that it is a unit of the
   valuation ring if it is not divisible by `p`, whereas `p` itself has
   valuation strictly below one. A rational of `p`-adic norm at most one has
   reduced denominator prime to `p`, and therefore has valuation at most one
   in `F` (`valuation_ratCast_le_one`). Given a valuative neighborhood of zero,
   choose `N` such that the valuation of `p^N` is below its radius. A rational
   of `p`-adic norm less than `‖p^N‖` becomes integral at `p` after division by
   `p^N`, so its image lies in the given neighborhood.
2. Give the rationals Mathlib's `WithVal` uniformity for their `p`-adic
   valuation and `F` the uniformity from its additive topological group.
   `uniformContinuous_ratCastWithVal` uses the preceding neighborhood bound
   and the additive-homomorphism criterion. Mathlib supplies completeness of
   `F` for this uniformity; `HarmonicAnalysis.GeneralLocalField.t2Space`
   supplies Hausdorffness. Extend the rational map across the dense uniform
   embedding in `ℚ_[p]` using `IsDenseInducing.extendRingHom`. The resulting
   map is continuous by `uniformContinuous_uniformly_extend`.
3. The closed unit ball in `ℚ_[p]` is also open, so rational points in it are
   dense in it. Closedness of the valuation ring of `F` extends the integral
   rational estimate to this whole ball. Conversely if `‖x‖ > 1`, discreteness
   of the `p`-adic norm gives `‖x⁻¹ / p‖ ≤ 1`. The image of `x⁻¹` then has
   valuation strictly below one, since the image of `p` does. Multiplicativity
   rules out valuation at most one for the image of `x`. Thus the pulled-back
   valuation and `Padic.mulValuation` agree on the at-most-one test.
   `Valuation.isEquiv_of_val_le_one` converts this into equivalence of all
   comparisons, which gives `ValuativeExtension`.
4. Continuity of `padicEmbedding F` and multiplication gives continuous
   scalar multiplication. The locally compact Hausdorff `ℚ_[p]`-vector
   space `F` is finite dimensional by `FiniteDimensional.of_locallyCompactSpace`.
   Mathlib's `isModuleTopologyOfFiniteDimensional` proves that its original
   topology is the module topology. The two packages then copy the stated
   structures and supply the compatibility certificates.

## Provenance and scope

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979 (`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`),
Chapter II, §1, Proposition 1 and Example 1, printed p. 27 (PDF p. 35),
relates completeness and finite residue field to local compactness and
identifies `ℚ_p` as the completion of the rationals. The opening of §5,
printed p. 36 (PDF p. 44), extends the embedding of the integers by
continuity and identifies the characteristic-zero fraction field with a
finite extension of `ℚ_p` for that residue prime. The first part of §2,
Proposition 3, printed pp. 28–29 (PDF pp. 36–37), relates the prolonged
valuation topology of a finite extension to the finite-dimensional product
topology. These are the classical ingredients for the comparison. Lean uses
the rational completion map and topological vector-space finiteness instead
of Serre's rank computation on integer rings. The `PadicField` and
`TopologicalData` packages and their definitional reuse of the supplied
structures are internal to the Library. This module does not compute the
extension degree, compare residue-normalized absolute values, or prove the
representation-theoretic step that will use the adapter.
