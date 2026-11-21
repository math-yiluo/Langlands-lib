# Full field-point lifting through a quasi-étale site arrow

Author: Worker 1004.

## Exact result

`QuasiEtaleSite.geometricPointImageLift` proves the published
`QuasiEtaleSite.GeometricPointImageLiftStatement.{u, v, uL}`. For an arrow
`f : V ⟶ U` of `QuasiEtaleSite X`, a full `L`-valued point of `U` lifts
whenever its ordinary point is in the image of `f.left`. This uses the
ground field, analytic space, and point field universes of the statement,
with `X : LocalizedCategory.{u, v, v} (K := K)` and `L` a complete,
ultrametric, algebraically closed normed extension of the complete
ultrametric ground field `K`. There is no extra separation, compactness,
or nontrivial-valuation hypothesis.

In fact, `pointedFieldPointLift_of_quasiEtale_comp` constructs a lift at any
chosen ordinary preimage for an analytic arrow `f : Y ⟶ U` when some
`g : U ⟶ X` has `f ≫ g` quasi-étale. The lift has the prescribed **full**
point as its image under `f`. This does not assert that `f` is quasi-étale.
For a site arrow, the commuting triangle identifies the composite with
the quasi-étale structure map of `V`. The site theorem uses the range
witness as the chosen preimage and forgets the equality of ordinary points.

## Implemented proof

1. **Change of field and a marked chart.** Changing a field point along
   an isometric bounded `K`-algebra map means postcomposing its chart
   evaluations (`FieldPoint.mapField`); it leaves the ordinary point
   unchanged. It commutes with analytic pushforward: for strong maps
   this is associativity of character composition. For a localized
   morphism, represent it by a right fraction, prelift the point through
   the denominator isomorphism, then use the strong-map law on the
   numerator and denominator. A `ResidueChart` is a chart on a presentation
   of a localized object, transported by an isomorphism, together with
   a marked spectrum point. Its completed-residue character realizes a
   full point over the completed residue field. Any full point over the
   same ordinary point with values in a complete field is obtained from
   this realization by a unique isometric bounded `K`-algebra map: extend
   its chart evaluation using `completedResidueLift`, identify full points
   by their evaluation in that chart, and use
   `completedResidueBoundedAlgHom_ext` for uniqueness.
2. **A witness above the base.** In a strong representative of an étale
   map, the selected point admits a finite full-recognition chart pair
   (`IsFiniteAt.hasFiniteFullRecognitionPairAt`). Let `M` and `E` be the
   completed residue fields of the source spectrum point and its target
   spectrum point in that pair. The canonical source `M`-point maps to
   the canonical target `E`-point after change of values by
   `completedResidueComap : E → M`. This is checked on the full-recognition
   target chart by the evaluation formula and `completedResidueComap_map`,
   then transported back to the saturated presentations. Finiteness
   (`finite_completedResidueComap`) gives algebraicity of this embedding.
   For a localized étale map the witness transports along the arrow
   isomorphism. For a quasi-étale map, choose a chart containing the
   selected ordinary point from the local finite union. Its map factors
   as an affinoid domain embedding followed by an étale map. Restrict the
   étale witness to the chart using pointed lifting for the domain embedding
   (which does not need an algebraically closed value field), then push it
   to the original source. The resulting `FinitePointWitness` retains the
   specified ordinary source point and the equality of its full image
   with the base realization changed along `E → M`.
3. **Match the prescribed point at the intermediate space.** Apply that
   witness to `f ≫ g` at the chosen preimage. The pushforward of its
   `M`-point under `f` and the prescribed `L`-point lie at the same ordinary
   point of `U`. In a chart there with completed residue field `H`, the
   two full points come from embeddings `a : H → M` and `b : H → L`.
   Push the canonical `H`-point along `g`. Its ordinary point is the
   marked base point, by the witness's full image equality and naturality
   of change of field, so it comes from an embedding `c : E → H`.
   The uniqueness in step 1 identifies `a ∘ c` with the witness's `E → M`.
   Thus `E → H → M` forms a scalar tower, and `M` is algebraic over `H`.
   The lemma `exists_isometric_algebraic_extension` extends `b` to an
   isometric map `j : M → L` with `j ∘ a = b`. Change the witness from
   `M` to `L` along `j`. It stays at the chosen ordinary preimage and its
   full image is the prescribed point, by naturality and `j ∘ a = b`.

## Provenance and scope

This is a derived result about the actual localized field-point functor
and site arrows. Berkovich, *Vanishing cycles for formal schemes*, Invent.
Math. **115** (1994), §3, printed pp. 543–544, gives the domain–étale local
form and the quasi-étale site. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces*, Publ. Math. IHÉS **78** (1993), §1.4,
printed p. 30, and Theorem 3.4.1, printed pp. 65–67, give the context for
using completed residue fields, domain restriction, and finiteness on
étale pieces. The Lean proof uses only algebraicity of the finite residue
witness, not separability, and the intermediate-field comparison replaces
an appeal to global quasi-étale right cancellation. The passage from
image lifting to all covering sieves is the separate site-level reduction
in `QuasiEtaleGeometricPointGeometry`.
