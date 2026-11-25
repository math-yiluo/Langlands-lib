# Joint finiteness of actual determinant-band Hilbert orbit coefficients

Lean module: `Langlands.Automorphic.CuspidalHilbertOrbitCoefficientJointFinite`.

This is an internal helper module for the proof of
`Langlands.Automorphic.CuspidalHilbertOrbitCoefficientStatement`. It proves
the last conclusion of that statement, `ArchimedeanGL.IsJointFinite F (r + 1) (C f)`.
It does so for any complex-linear coefficient map `C` that realizes the actual coefficient
integrals and commutes with the genuine enveloping action. It does not construct `C` and
proves nothing about smoothness or differentiation under the integral. The two hypotheses
are exactly the second and third conclusions of the target statement.

The module adds no definitions. Every declaration is a theorem about objects already in
the Library: the band coefficient `CuspidalHilbertOrbitCoefficient.coefficient` and the
quotient maps `OperatorDeterminantSlice.toQuotient` and `OperatorDeterminantSlice.translate`.

## Results

For an operator realization `S` of `GL_n` (no cuspidality, irreducibility or central
character needed):

- `translate_translate`: `translate a (translate b q) = translate (b * a) q`. Positive right
  translations of the rational quotient compose in this order. Proof: write `q` as a
  point and use `translate_point`.
- `toQuotient_compactRepresentation`: the standard infinite compact action of `k` on `S`
  becomes right translation by `ofInfinite k` on the quotient function. Proof: like the
  Library's `toQuotient_finite`, via `point_surjective`, `translate_point`,
  `toQuotient_point` and `evaluate_compactRepresentation`.
- `exists_center_ideal`: every `f : S.Space` has an ideal `I` of the enveloping center
  with finite complex codimension such that
  `S.envelopingAction (centerInclusion z) f = 0` for every `z ∈ I`. Proof: the ambient
  form is automorphic (`isAutomorphicForm_ambient`), so `isCenterFinite_iff_exists_ideal`
  gives a single ideal that kills the center action on every slice. The slice of
  `S.envelopingAction u f` at `y` is `envelopingAction u` applied to the slice of `f`
  (`ambient_envelopingAction`, `finiteSmoothSlice_envelopingAction`). So for `u` in the
  image of `I` every slice vanishes. Every adelic point is
  `ofInfinite (infinite x) * ofFinite (finite x)`, so the continuous function
  `S.toContinuous (S.envelopingAction u f)` is zero. Since `toContinuous` is injective,
  the vector itself is zero.
- `isFiniteVector_compactRepresentation`: every `f : S.Space` is a finite vector of
  `S.compactRepresentation`. Proof: the automorphic condition gives finiteness of the
  standard compact orbit span of the ambient continuous function (`IsInfiniteFinite`).
  The injective linear map `S.toContinuous` sends the compact orbit span of `f` into that
  span (by `Submodule.map_span` and `evaluate_compactRepresentation`, definitionally).
  Hence the orbit span of `f` is finite-dimensional (`FiniteDimensional.of_injective`).

For a cuspidal operator realization `T` of `GL_(r+1)`, `w` in the band `L²` space and
`C : T.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F (r + 1)`:

- `coefficient_compactRepresentation`:
  `coefficient T w (T.realization.compactRepresentation k f) g = coefficient T w f (g * k)`.
  Proof: the integrands agree pointwise, by `toQuotient_compactRepresentation`,
  `translate_translate` and multiplicativity of `AdelicGL.ofInfinite`.
- `compactRepresentation_intertwines`: if `(C f).val g = coefficient T w f g` for all
  `f, g`, then `C (T.realization.compactRepresentation k f)` equals
  `smoothRightAction F (r + 1) k.val (C f)`. Proof: evaluate both sides and apply the
  previous lemma.
- `isJointFinite_of_covariant`: if moreover
  `C (T.realization.envelopingAction a f) = ArchimedeanGL.envelopingAction F (r + 1) a (C f)`
  for every enveloping element `a` and every `f`, then
  `ArchimedeanGL.IsJointFinite F (r + 1) (C f)` holds for every `f`.

Outside the `CuspidalHilbertOrbitCoefficient` namespace:

- `cuspidalHilbertOrbitCoefficientStatement_of_covariant`: the target statement
  `CuspidalHilbertOrbitCoefficientStatement.{u}` follows from the following weaker
  statement. For every number field `F` with compact `AdeleQuotient F`, every `r`, every
  cuspidal operator realization `T` with unitary central character and every band vector
  `w`, all integrands are integrable, and some complex-linear
  `C : T.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F (r + 1)` has the actual coefficient
  values and genuine enveloping covariance. Proof: take `C` from that statement. The only
  missing conclusion of the target is joint finiteness, and `isJointFinite_of_covariant`
  supplies it.

## Proof of `isJointFinite_of_covariant`

1. *Center.* Take `I` from `exists_center_ideal`. For `z ∈ I`, covariance gives
   `centerAction z (C f) = envelopingAction (centerInclusion z) (C f)`, which equals
   `C (T.realization.envelopingAction (centerInclusion z) f) = C 0 = 0`. So `I` lies in the
   kernel of `centerOrbitMap (C f)`. The quotient by that kernel is a quotient of the
   finite-dimensional `EnvelopingCenter ⧸ I` (`Submodule.factor`), and it is isomorphic to
   the range (`quotKerEquivRange`). The range is the center orbit span
   (`centerOrbitSpan_eq_range`), so `IsCenterFinite (C f)` holds.
2. *Compact group.* `compactRepresentation_intertwines` makes `C` an intertwining map
   from `T.realization.compactRepresentation` to the smooth right action restricted to
   `standardInfiniteCompact`. `IsFiniteVector.map` transports the finiteness of
   `isFiniteVector_compactRepresentation`, so `C f` is a finite vector for the standard
   compact group.
3. *Compact Lie algebra.* The Library theorem `compactGroupFiniteDifferential` turns group
   finiteness into `IsCompactLieFinite (C f)`.
4. *Joint.* The Library theorem `separateJointFinite` combines center finiteness and
   compact Lie finiteness into `IsJointFinite (C f)`.

## Notes

Several declarations carry `set_option maxHeartbeats 400000`, `500000` or `800000`. These
limits are finite. They cover the coercion-heavy unfolding of the realization's ambient
functions and, for the reduction theorem, the definitional matching of the local
`AddCommGroup` instances of this module with those of the statement module (both are
`Submodule.addCommGroup _`).
`backward.isDefEq.respectTransparency false` is set as in the Library modules this one
builds on.

The compact action on the quotient uses `OperatorDeterminantSlice.toQuotient_compact`. Compact finiteness uses `OperatorRealization.compactRepresentation_isFiniteVector`.
