# Integral points preserve the Lie lattice

Let `R` be a commutative domain with fraction field `K` (`IsFractionRing R K`),
let `G` be a group scheme over `Spec K` that is affine over `Spec K`, and let
`M : IntegralModel R K G` be a supplied integral model with group scheme
`𝒢 = M.group` over `Spec R`. The module
`Langlands.GroupScheme.IntegralModel.LieLattice` constructs the injective
`R`-linear Lie map `M.lieMap : Lie(𝒢) → Lie(G)` and its range, the Lie lattice
`M.lieLattice ⊆ GenericLie R G`. As there, Lie algebras are the Library's actual
dual-number identity kernels `lieKernel`, and the adjoint action is the
Library's `adjoint` (`Lie.Adjoint`): conjugation by a constant dual-number point.

This module proves that the adjoint action of every integral point
`g ∈ M.integralPoints ⊆ G(K)` maps `M.lieLattice` onto itself. It also gives the
resulting representation of `M.integralPoints` on the lattice. Smoothness is not
needed.

## The adjoint action on `GenericLie R G`

Rational points `g : rationalPoints G` are sections over the identity test
object `Spec K`. The adjoint action needs points with coefficients in the
algebra `K`, so `g` is converted by the Library's
`AffineWeil.sectionsCoeffEquiv K G : rationalPoints G ≃* G.affinePoints (CommAlgCat.of K K)`
(`IntegralModel.AffineWeilPoints`).

- `GenericLie.adjoint R g : GenericLie R G →ₗ[R] GenericLie R G` is
  `adjoint G K (AffineWeil.sectionsCoeffEquiv K G g)`, transported to the type
  synonym by `GenericLie.equiv R G` and restricted to `R`-scalars.
  `GenericLie.adjoint_apply` unfolds it, by `rfl`.
- `GenericLie.adjoint_mul`: `adjoint R (g * h) X = adjoint R g (adjoint R h X)`.
- `GenericLie.adjoint_one`: `adjoint R 1 X = X`.

Both follow from multiplicativity of `sectionsCoeffEquiv` and of `adjoint G K`.

## Generic points of integral sections

- `IntegralModel.affineBaseChangeEquiv_eq_symm`: for points of the actual
  generic fibre with coefficients in `K`, the pullback comparison
  `Lie.affineBaseChangeEquiv R K M.group K` used by the Lie kernels equals the
  inverse of the Library's pullback-adjunction comparison
  `affinePointsBaseChangeMulEquiv R K K M.group`. The proof compares the
  underlying morphisms; both are composition with the first pullback projection.
- `IntegralModel.sectionsCoeffEquiv_integralPointMap`: for an integral section
  `x : M.integralSections`, the coefficient point of its generic point
  `M.integralPointMap x ∈ G(K)` is obtained from the `R`-coefficient point
  `AffineWeil.sectionsCoeffEquiv R M.group x` in three steps. First comes
  coefficient change along `R → K` (`Lie.affineMap M.group (Algebra.ofId R K)`),
  then the inverse of `Lie.affineBaseChangeEquiv R K M.group K`, then
  composition with the generic isomorphism `M.genericIso.hom`. The proof
  rewrites with `AffineWeil.sectionsCoeffEquiv_target` and
  `AffineWeil.sectionsCoeffEquiv_baseChangeSectionHom`. After these rewrites
  the two sides agree definitionally, so `congr 1` closes the goal.

## Preservation of the lattice

Assume `[IsAffineHom G.X.hom]`; the Library's
`IntegralModel.generic_isAffineHom M` discharges this hypothesis.

- `IntegralModel.lieMap_adjoint`: for `x : M.integralSections` and
  `X : M.LieModule`,
  `M.lieMap (adjoint M.group R (sectionsCoeffEquiv R M.group x) X) =
  GenericLie.adjoint R (M.integralPointMap x) (M.lieMap X)`.
  So the Lie map intertwines the adjoint action of `x` on `Lie(𝒢)` with the
  adjoint action of its generic point on `Lie(G)`. The proof moves the adjoint
  action past each of the three maps that make up `M.lieMap`. These are
  coefficient change (`adjoint_naturality`), the pullback comparison
  (`Lie.kernelBaseChangeLinearEquiv_adjoint`) and the differential of the
  generic isomorphism (`lieKernelHomLinear_adjoint`). The coefficient points
  are matched by `sectionsCoeffEquiv_integralPointMap`.
- `IntegralModel.adjoint_mem_lieLattice`: if `g ∈ M.integralPoints` and
  `Y ∈ M.lieLattice`, then `GenericLie.adjoint R g Y ∈ M.lieLattice`.
- `IntegralModel.map_adjoint_lieLattice`: if `g ∈ M.integralPoints`, then
  `M.lieLattice.map (GenericLie.adjoint R g) = M.lieLattice`. The reverse
  inclusion applies the previous result to `g⁻¹`, which is again an integral
  point, and uses `adjoint_mul` and `adjoint_one`.

## The representation on the lattice

- `IntegralModel.lieLatticeAdjoint : M.integralPoints →* Module.End R M.lieLattice`
  restricts `GenericLie.adjoint R g` to the lattice for each integral point `g`.
  `lieLatticeAdjoint_apply` gives its value in `GenericLie R G`, by `rfl`.
- `IntegralModel.lieLatticeEquiv_adjoint`: under the Library's
  `M.lieLatticeEquiv : Lie(𝒢) ≃ₗ[R] M.lieLattice`, the adjoint action of an
  integral section `x` on `Lie(𝒢)` corresponds to `M.lieLatticeAdjoint` at the
  integral point `M.integralPointMap x`.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, 13.3.4 (printed p. 471; PDF p. 502), reads: "As `G(K)_{x,r}` is
a normal subgroup of `G(K)^0_x` by Proposition 13.2.5, the conjugation action of
`G` on itself extends (see Corollary 2.10.10) to an action of the group scheme
`𝒢_x^0` on the group scheme `𝒢_{x,r}`, and hence also on the Lie algebra
`𝔤_{x,r}` and its dual `𝔤*_{x,r}`, for all `r ∈ ℝ`."

This module proves a special case of the last step for an arbitrary supplied
model, over an arbitrary domain `R` with fraction field `K`. The acting group is
`M.integralPoints ⊆ G(K)`, the image of the model's own integral sections
`𝒢(R)`. These act by conjugation on `𝒢` itself and hence preserve
`Lie(𝒢) ⊆ Lie(G)` (`map_adjoint_lieLattice`).
For a parahoric model this is the case `r = 0` of KP 13.3.4 on integral points,
where `𝒢_{x,0} = 𝒢_x^0`. The result is stated only for the action of the group
`M.integralPoints`, not as an action of the group scheme `𝒢` on a scheme.
No smoothness is used. KP extends the conjugation action to the group schemes
through Corollary 2.10.10, which assumes the source model smooth; this module
does not construct such an extension. Here the action on `Lie(𝒢)` is
conjugation by constant dual-number points of `𝒢` itself.

The corrections of 1 November 2024 have no entry for §13.3 or for
Corollary 2.10.10.

## Provenance

Derived. That integral points of a group model preserve its Lie lattice under
the adjoint action is a standard fact, used without separate proof in KP 13.3.4.
The Lean route is internal and composed from published Library constructions:
`adjoint` and `adjoint_naturality` (`Lie.Adjoint`),
`Lie.affineBaseChangeEquiv`, `Lie.affineBaseChangeEquiv_left` and
`Lie.kernelBaseChangeLinearEquiv_adjoint` (`Lie.BaseChange`),
`lieKernelHomLinear_adjoint` (`Lie.Functoriality`),
`AffineWeil.sectionsCoeffEquiv`, `AffineWeil.sectionsCoeffEquiv_target` and
`AffineWeil.sectionsCoeffEquiv_baseChangeSectionHom`
(`IntegralModel.AffineWeilPoints`), `affinePointsBaseChangeMulEquiv` and
`affinePointsBaseChangeMulEquiv_symm_left` (`AffinePointBaseChangeSmooth`), and
`IntegralModel.lieMap`, `lieLattice`, `lieLatticeEquiv`
(`IntegralModel.LieLattice`). No external code is adapted.

## Not claimed

- The concave-function group schemes `𝒢_{x,r}`, the action of `𝒢_x^0` on
  `𝒢_{x,r}` for `r > 0`, and the dual lattices `𝔤*_{x,r}` are not formalized.
- No scheme-level action `𝒢 × Lie(𝒢) → Lie(𝒢)` is constructed. Only the action
  of the abstract group `M.integralPoints` is given.
- The induced action of the special fibre or of its reductive quotient on
  `𝔤_{x,r} ⊗ 𝔣` and on `𝔤_{x,r}/𝔤_{x,r+}` (the rest of KP 13.3.4) is not
  formalized.
- The Lie bracket is not treated; `lieLatticeAdjoint` is a representation by
  `R`-linear endomorphisms of the lattice.
