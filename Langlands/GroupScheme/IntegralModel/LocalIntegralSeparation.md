# Openness of the integral-point image over a local field

Author: Worker 4686.

This internal helper module proves two facts about a supplied integral model
`M : IntegralModel R K G`: the integral-point image `M.integralPoints` is open
in `G(F)` over a nonarchimedean local field, and the original coordinates of a
model of a connected reductive group are separated by integral sections. All
declarations are in `Langlands.GroupScheme.IntegralModel`. The module sets
`backward.isDefEq.respectTransparency false` and
`backward.isDefEq.respectTransparency.types false`.

## Original coordinates (any fraction field)

Here `R` is an integral domain with fraction field `K`, `G` is a group scheme
over `Spec K` and `M : IntegralModel R K G`. The model is affine over `R`
(private instance from `isAffine_of_isAffineHom`).

* `coordinateAlgHom M g`, for `g : rationalPoints G`, is the `R`-algebra map
  `AffineCoordinateRing R M.group.X →ₐ[R] K` classifying the `K`-valued model
  point `M.genericModelPointEquiv K (rationalCoeffEquiv K G g)`.
  `coordinateAlgHom_apply` identifies its value at `a` with the evaluation of
  the generic coordinate `M.genericCoordinate a` at `g` (published
  `genericModelPointEquiv_evaluation`).
* `mem_integralPoints_iff_of_adjoin_eq_top`: if a set `s` generates the
  original coordinate ring as an `R`-algebra, then `g ∈ M.integralPoints` if
  and only if `coordinateAlgHom M g a` lies in the image of `R` for every
  `a ∈ s`. This sharpens the published
  `mem_integralPoints_iff_genericCoordinates` (all coordinates) because the
  elements mapped into `R` form a subalgebra.
* `flat_affineCoordinateRing`: the original coordinate ring is flat over `R`
  (the model is flat over `Spec R`).
* `genericCoordinate_injective`: restriction of original coordinates to the
  generic group, `M.genericCoordinate`, is injective. It is the map
  `A → K ⊗_R A`, `a ↦ 1 ⊗ a`, composed with the generic identification, and
  `R → K` stays injective after tensoring with the flat module `A`.

## Local fields

Now `F` is a nonarchimedean local field (both characteristics), `G` is affine
over `Spec F`, `M : IntegralModel 𝒪[F] F G`, and `rationalPoints G` carries
the published `rationalPointTopology F G.X`.

* `continuous_coordinateAlgHom_apply`: for each original coordinate `a`, the
  map `g ↦ coordinateAlgHom M g a` is continuous. It is evaluation of the
  generic coordinate, which is continuous for the published point topology
  (`AlgPoint.continuous_eval`, `affineSchemePointHomeomorph`,
  `rationalPointHomeomorph`).
* `isOpen_integralPoints_localField`: `M.integralPoints` is open in
  `rationalPoints G`. The original coordinate ring is of finite type over
  `𝒪[F]`; for a finite generating set `s`, the previous criterion writes
  `M.integralPoints` as the finite intersection over `a ∈ s` of the preimages
  of the open valuation ring `𝒪[F] ⊆ F` (`Valuation.isOpen_integer`) under
  continuous maps.
* `exists_integralSection_apply_ne_zero`: if `IsConnectedReductive G`, every
  nonzero original coordinate `b` takes a nonzero value at some original
  integral section `s : M.integralSections`, that is,
  `affineSchemePointEquiv 𝒪[F] M.group.X 𝒪[F] (rationalPointEquiv 𝒪[F] M.group.X s) b ≠ 0`.
  Proof: the generic coordinate ring `A` of `G` is a smooth `F`-algebra and an
  integral domain (`CharacterLatticeProof.isIntegral_of_smooth`), and the
  generic coordinate of `b` is nonzero by `genericCoordinate_injective`. The
  image of `M.integralPoints` in the space of `F`-algebra maps `A → F` is an
  open neighbourhood of the identity by `isOpen_integralPoints_localField`. The
  published `RingTheory.LocalFieldDensity.localSeparation` (for a smooth
  domain over a complete nontrivially normed field, a nonzero element is
  nonzero at some point of every neighbourhood of every rational point) gives
  an integral point where the generic coordinate of `b` is nonzero. At the integral point
  of `s` the generic coordinate of `b` is the image of the value of `b` at
  `s` (`genericModelPointEquiv_integralPointMap`,
  `affineSchemePointEquiv_changeRing`), so that value is nonzero. The
  normed-field structure on `F` needed by `localSeparation` is built from the
  rank-one valuation of `F` inside the proof.

## Provenance

The module is derived internally from published Library results; it follows no
specific source. The separation result supplies the hypothesis of
`IntegralLinearEmbedding.exists_matrix_coefficients` (in
`IntegralLinearEmbedding/Comodule.lean`) for the coordinate ring of the model.
Openness of `M.integralPoints` is also an input that the Levi step of
`MaximalCompactStatement` may use.
