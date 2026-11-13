# Two-axis classes over valuation rings and valuative existence of representers

Worker 198 wrote this internal module for Task 5678. It works in namespace
`Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle`, in every
universe. Throughout, `A` is a Library abelian scheme over an arbitrary scheme
`S`. `abelian A T`, `productMap A h` and `carrierMap A h` are the published
base-change constructions of `TwoAxisRigidifiedClassPresheaf`.

## Surjectivity from extension

`classesPullback_surjective_of_extension` takes a morphism `h : T' ⟶ T` in
`Over S`. Its hypothesis: every actual line bundle `D` on the self-product of
`abelian A T'` with trivial restrictions to both unit axes admits an actual line
bundle `E` on the self-product of `abelian A T`. This `E` must have trivial
restrictions to both unit axes and a module-sheaf isomorphism
`(productMap A h)* E ≅ D`. The conclusion is surjectivity of the published class
restriction `classesPullback A h`.

Proof: take a class with representative `D'`. Extend its underlying bundle. Give
the extension a compatible rigidification with the published
`nonempty_twoAxisRigidification`. Its relative pullback has carrier
`(productMap A h)* E`. `nonempty_iso_of_carrierIso` upgrades the carrier
isomorphism to a rigidified isomorphism with `D'`.

## Iterated base change

For `T : Over S` and `b : W ⟶ T.left`, `compTestHom b` is the test-scheme map
`Over.mk (b ≫ T.hom) ⟶ T` given by `b`. `compCarrierIso A b` is the explicit
isomorphism of carriers
`abelian A (Over.mk (b ≫ T.hom)) ≅ (baseChange b).obj (abelian A T)`.
Its forward map is the pullback lift of `carrierMap A (compTestHom b)` and the
structure morphism. Its inverse is the composite of the two first projections and
the second projection. The simp lemmas record its projections. In particular it
lies over `W`. `unitSection_compCarrierIso` and its inverse version show that it
matches the unit sections. The proof uses the published `unit_naturality` and
`unit_fst`.

`compProductHom` and `compProductInv` are the induced maps of self-products,
built with the published `cartesianMumfordProductMap`.
`compProductHom_baseChangeMap` proves
`compProductHom A b ≫ mumfordProductBaseChangeMap (abelian A T) b =
productMap A (compTestHom b)`. `compProductHom_inv` proves
`compProductHom A b ≫ compProductInv A b = 𝟙`.

`extension_compTestHom` transfers an extension property for the canonical map
`mumfordProductBaseChangeMap (abelian A T) b` to the extension hypothesis above,
for `h = compTestHom b`. Proof:

1. Pull `D` back along `compProductInv`. The published axis-comparison lemmas
   `mumfordSection_cartesianMumfordProductMap` and
   `twoAxisSecond_cartesianMumfordProductMap` give trivial axes.
2. Extend the result with the hypothesis.
3. Normalize the extension with the published `twoAxisTrivialExtensionOfExtension`,
   which makes both total-space axes trivial and keeps an actual restriction
   isomorphism.
4. Compose module-pullback comparisons along the two displayed equations.

## Valuation rings and representers

`classesPullback_surjective_valuationRing` takes any valuation domain `R`, any
supplied fraction field `K` with its given algebra structure, and any
`i₂ : Spec R ⟶ S`. It proves surjectivity of class restriction along
`compTestHom (Spec.map (algebraMap R K))` from `Over.mk i₂`. The extension input
is the published unconditional `valuationRingTwoAxisExtension`, applied to
`abelian A (Over.mk i₂)`.

`valuativeExistence_of_representableBy` takes any `q : Y ⟶ S` and any
representation `e : (classPresheaf A).RepresentableBy (Over.mk q)`. It proves
Mathlib's `ValuativeCriterion.Existence q`. Given a valuative square, the top map
gives a class over the fraction field via `e.homEquiv`. The preceding
surjectivity lifts it to a class over the valuation ring. `e.homEquiv.symm`
turns that class into the lift, and `e.homEquiv_comp` with injectivity of
`e.homEquiv` gives both triangle equations.
`discreteValuativeExistence_of_representableBy` restricts this to the published
`DiscreteValuativeCriterion.Existence q`.

No separatedness, finiteness or unramifiedness of `q` is used, and no
representer is constructed. The provenance is internal composition of published
Library results. Raynaud, LNM 119, proof of XI 1.5, printed p.162, uses the same
consequence of extension over traits; this module proves it for the Library's
presheaf.
