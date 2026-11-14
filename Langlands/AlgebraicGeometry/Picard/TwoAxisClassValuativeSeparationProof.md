# Valuative separation (F6) for the two-axis class presheaf

Worker 386 wrote this module for Task 6296. It proves the published proposition
`Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassValuativeSeparationStatement`
as the theorem
`Langlands.AlgebraicGeometry.Picard.noetherianTwoAxisClassValuativeSeparation`,
in every universe `u`.

The target says: for every noetherian ring `R` and every Library abelian scheme
`A` over `Spec R`, the two-axis class presheaf `classPresheaf A` satisfies
Murre's condition `ValuativeSeparation`. That is, for every discrete valuation
ring `V` and every `f : Spec V ⟶ Spec R`, the class restriction along
`algebraOverBase f (FractionRing V)` is injective.

## Helpers (namespace `TwoAxisRigidifiedLineBundle`)

- `carrierIso`: an isomorphism of two-axis-rigidified line bundles gives an
  isomorphism of their underlying module sheaves (carriers). It is the image of
  the isomorphism under the inclusion of the full subcategory and the forgetful
  functor `TwoAxisRigidifiedModule.forget`.
- Local instances: for every abelian scheme `C`, the self-product structure
  morphism `(mumfordProduct C).hom` is smooth, universally closed, separated and
  geometrically connected. It equals `pullback.fst ≫ C.X.hom`. These instances are
  copied from the Library module `MumfordProductGenericExtension`, where they are
  also local.
- `compProductInv_hom`: `compProductInv A b ≫ compProductHom A b = 𝟙`. The
  published `compProductHom_inv` proves the composite in the other order. The
  proof uses pullback extensionality and the projection lemmas
  `cartesianSelfProductMap_fst` and `cartesianSelfProductMap_snd`.
- `compPullbackIso`: for `T : Over S`, `b : W ⟶ T.left` and a module sheaf `N` on
  the self-product of `abelian A T`, an isomorphism between the pullback of `N`
  along `mumfordProductBaseChangeMap (abelian A T) b` and the pullback along
  `compProductInv A b` of the pullback of `N` along
  `productMap A (compTestHom b)`. It composes the module-pullback identity,
  composition and congruence isomorphisms, using `compProductInv_hom` and the
  published `compProductHom_baseChangeMap`.

## Injectivity over valuation rings

`classesPullback_injective_valuationRing` works for an arbitrary valuation domain
`R` (any rank), any supplied fraction field `K` with its given algebra structure,
and any `i₂ : Spec R ⟶ S`. It proves that `classesPullback A` along
`compTestHom (Spec.map (algebraMap R K))` from `Over.mk i₂` is injective. Proof:

1. Take classes of rigidified bundles `L` and `M` with equal images.
   `Quotient.exact` gives an isomorphism of their relative pullbacks.
   `carrierIso` turns it into an isomorphism of the pullbacks of the carriers
   along `productMap A (compTestHom b)`, where `b = Spec.map (algebraMap R K)`.
2. Conjugating by `compPullbackIso` gives an isomorphism `ψ` of the pullbacks of
   the carriers along the canonical map
   `q := mumfordProductBaseChangeMap B b`, where `B := abelian A (Over.mk i₂)`.
3. Apply `nonempty_iso_of_generic_iso` (module `GenericLineBundleInjectivity`)
   with `p := (mumfordProduct B).hom`, this `q`, and the published inputs:
   - the cartesian square `isPullback_mumfordProduct_generic K B`;
   - sectionwise injectivity `mumfordProduct_generic_app_injective K B`;
   - projectivity
     `affineClosedFibreSectionProjectivity_of_integralFibreProjectivity`,
     applied to the published theorem
     `Langlands.CommutativeAlgebra.integralFibreProjectivity`.
   The carriers are locally free of rank one (`L.property`, `M.property`). This
   gives an isomorphism of the carriers of `L` and `M`.
4. The published `nonempty_iso_of_carrierIso` upgrades it to an isomorphism of
   rigidified bundles, and `Quotient.sound` gives equality of classes.

## The target

`noetherianTwoAxisClassValuativeSeparation` introduces `R`, `A`, `V` and `f`.
A discrete valuation ring is a valuation ring through a Mathlib instance. The
presheaf map along `algebraOverBase f (FractionRing V)` is definitionally
`classesPullback A` along `compTestHom (Spec.map (algebraMap V (FractionRing V)))`
from `Over.mk f`. So the target is
`classesPullback_injective_valuationRing A V (FractionRing V) f`. The noetherian
hypothesis on `R` is not used.

## Provenance

The provenance is internal: the module composes published Library results with
`GenericLineBundleInjectivity`. Murre's condition (F6) is the separation part of
the valuative criterion for the Picard functor. Its classical proof uses the
fact that line bundles on a smooth proper scheme over a discrete valuation ring
are determined by their generic fibre. That fact is proved here through
`nonempty_iso_of_generic_iso`, and holds over any valuation ring.

The common helper `TwoAxisRigidifiedLineBundle.compProductInv_hom` is imported from `TwoAxisValuationClassSurjectivity`.
