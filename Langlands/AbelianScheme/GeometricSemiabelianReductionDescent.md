# Geometric semiabelian reduction under base change of the valuation ring

The module proves that the predicate `NeronModel.HasGeometricSemiabelianReduction`
of `Langlands/AbelianScheme/PotentialSemistableReductionStatement.lean` can be
tested after a local extension of discrete valuation rings whose residue
extension is algebraic.

## Declarations

- `GeometricSemiabelianDescent.commBaseChangeCompIso`,
  `GeometricSemiabelianDescent.Langlands.GroupScheme.CommGroupScheme.baseChangeIdIso` and
  `GeometricSemiabelianDescent.commBaseChangeEqIso` are the comparison
  isomorphisms for pullbacks of commutative group schemes: pullback along a
  composite is pullback in two steps, pullback along the identity is the
  identity, and pullbacks along equal morphisms agree. The first two wrap
  `GroupScheme.baseChangeCompIso` and `GroupScheme.baseChangeIdIso`, as
  `AbelianScheme.baseChangeCompIso` does for abelian schemes.
- `GeometricSemiabelianDescent.groupIso` is the isomorphism of underlying group
  schemes of an isomorphism of commutative group schemes.
- `SplitSemiabelianPresentation.baseChange` pulls a split semiabelian
  presentation of a commutative group scheme over a field `k` back along any
  morphism `Spec k' ⟶ Spec k` with `k'` algebraically closed.
- `NeronModel.hasGeometricSemiabelianReduction_of_baseChange`: let `V → W` be a
  local homomorphism of discrete valuation rings with fraction fields `K` and
  `L`, such that the residue field of `W` is algebraic over that of `V`. Let `N`
  be a Néron model over `V` of an abelian variety `B` over `K`, let `N'` be a
  Néron model over `W` of an abelian variety `B'` over `L`, and let
  `e : N'.group ≅ N ×_V W` be an isomorphism of commutative group schemes over
  `W`. If `N'.HasGeometricSemiabelianReduction`, then
  `N.HasGeometricSemiabelianReduction`.

## Proofs

`SplitSemiabelianPresentation.baseChange` applies
`SplitSemiabelianPresentation.ofTorusKernel` to the pulled-back abelian variety
`(AbelianScheme.baseChange b).obj P.quotient` and the pulled-back quotient map.
That map is a pullback of the original quotient map
(`RelativeIdentityComponent.overPullback_isPullback`), so it is smooth and
surjective. The kernel of the original map is a split torus through the
presentation's `torusIso`; split tori stay split under base change
(`IsSplitTorus.baseChange`), the kernel commutes with base change
(`kernelBaseChangeIso`), and a split torus is a torus (`IsSplitTorus.isTorus`).

For `NeronModel.hasGeometricSemiabelianReduction_of_baseChange`, write `k̄_V` and
`k̄_W` for the algebraic closures of the residue fields. Since the residue
extension is algebraic, `k̄_W` is an algebraic closure of the residue field of
`V`, and `IsAlgClosure.equivOfAlgebraic` gives an isomorphism `σ : k̄_W ≃ k̄_V`
over that residue field. Let `φ = Spec σ⁻¹ : Spec k̄_W ⟶ Spec k̄_V` and
`ψ = Spec σ : Spec k̄_V ⟶ Spec k̄_W`, so that `ψ ≫ φ` is the identity. The
geometric closed point of `W` followed by `Spec W → Spec V` equals `φ` followed
by the geometric closed point of `V`: on rings both send `v` to the image of its
residue class, because `σ` fixes the residue field of `V` and the residue maps
commute with `V → W` (`IsLocalRing.ResidueField.algebraMap_residue`). With the
comparison isomorphisms, `e` gives an isomorphism from the geometric special
fibre of `N'` to the pullback along `φ` of the geometric special fibre of `N`,
and then an isomorphism `β` from the pullback along `ψ` of the geometric special
fibre of `N'` to the geometric special fibre of `N`.

Let `i' : J' ⟶ N'.geometricSpecialFibre` be the representative of the identity
component and `P'` the split semiabelian presentation of `J'` supplied by the
hypothesis. The geometric special fibre of `N'` is smooth, being a pullback of
the smooth Néron model, so `RelativeIdentityComponent.smoothExistence` gives a
geometrically connected representative of its identity component, and
`IsRelativeIdentityComponent.geometricallyConnected` transfers geometric
connectedness to `J'`. Then `IsRelativeIdentityComponent.baseChange` shows that
the pullback of `i'` along `ψ` represents the identity component of the pulled
back fibre, and `IsRelativeIdentityComponent.comp_iso` transports it along `β`.
The pair `((CommGroupScheme.baseChange ψ).obj J', (CommGroupScheme.baseChange ψ).map i' ≫ β.hom)`
with the presentation `P'.baseChange ψ` is the required witness.

## Relation to the sources

The descent of the semiabelian property is the observation in Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §7.3, printed p. 178 (PDF
p. 185), that semi-abelian reduction can be checked over the algebraic closure
of the residue field, used with the compatibility of Néron models with
extensions of ramification index one (§7.2, Theorem 1 and Corollary 2) in the
reduction to a strictly Henselian base of Grothendieck, SGA 7 I, Exposé IX,
3.4.0. The Lean theorem assumes the isomorphism of the model over `W` with the
base change of `N` and uses only that the residue extension is algebraic.
