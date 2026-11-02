# Steps 5 and 7 of the dual-side Euler reduction

Author: Worker 943.

This module is for task `6b1ab3e8-b3b0-4567-9251-7566e7a6dba3`, which proves
`Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`. Its contract splits the
route into seven steps. This file proves two of them, Step 5 and Step 7, from published
Library results and Mathlib. It has no hypotheses beyond the ones stated in each lemma.
Steps 1-4 (the coefficient rewrite and the direct images of the twisted Poincaré pullback)
are in `Langlands.AlgebraicGeometry.Picard.MumfordDualDirectImages`, Step 6 (the kernel fibre
dimension) is in `Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibreSections`, and the
assembly is in `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerFromPrerequisites`.

The module compiles: `lean_check` diagnostic `85546967-27ed-45d8-bb36-799254d7eff3`,
0 errors, 0 warnings.

## Step 5: `Langlands.AlgebraicGeometry.Modules.DerivedSections.eulerCharacteristic_comp_eq_of_concentrated`

Let `K` be a field, `p : X ⟶ Y` a morphism of schemes, `s : Y ⟶ Spec K`, `Q` an
`𝒪_X`-module, and `g` a natural number. Assume:

- `hzero`: for every `n ≠ g`, the higher direct image `(higherDirectImage p n).obj Q` is a
  zero object;
- `hsupp`: `(higherDirectImage p g).obj Q` has finite closed support;
- `hQ`: `Q` has finite cohomology along `p ≫ s`.

Then
`eulerCharacteristic (p ≫ s) Q hQ = (-1)^g * finrank K (Γ_s(R^g p_* Q))`,
where `Γ_s` is `relativeGlobalSections s`.

This is the Leray computation in the proof of EvdGM (9.11) (literature id
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, PDF p.136): when all direct images
but one vanish and the remaining one is supported on finitely many closed points, the
cohomology of `Q` is the global sections of that one direct image, shifted to degree `g`.

Proof. Every `R^q p_* Q` has finite closed support: for `q = g` this is `hsupp`, and
otherwise a zero object has finite closed support (`HasFiniteClosedSupport.of_isZero`).
The Library theorem `finiteClosedSupportLeray` then gives, for every `n`, an isomorphism
between the `n`-th cohomology of `Q` along `p ≫ s` and `Γ_s(R^n p_* Q)`. After unfolding
`eulerCharacteristic` as a finite sum, `finsum_eq_single` at `g` leaves two goals. In degree
`g` the isomorphism gives the equality of dimensions. In degree `n ≠ g`, `Γ_s` is additive
(the instance is supplied explicitly in the proof, as in the Library's
`instAdditiveRelativeGlobalSectionsOf`), so it sends the zero object `R^n p_* Q` to a zero
module, of dimension `0`.

## Step 7: `Langlands.AbelianScheme.finrank_eq_of_fieldDualSchemeGeometry`

Assume `FieldDualSchemeGeometryStatement` (the published statement that over a field the
chosen dual is smooth, proper and geometrically connected). Let `K` be a field, `A` an
abelian scheme over `Spec K` with a chosen dual `dualScheme A hA`, and `f : A.X ⟶ dualScheme A hA`
a morphism over the base whose underlying scheme map is finite and flat. Then for any two
points `y, y'` of the dual, `f.left.finrank y = f.left.finrank y'`.

Proof. The geometry statement gives geometric connectedness of the dual over `Spec K`.
Since `Spec K` is a one-point space, Mathlib's
`GeometricallyConnected.connectedSpace_of_subsingleton` makes the dual a connected space.
The dual is locally of finite type over a field, hence locally Noetherian, so the finite
flat map `f.left` is locally of finite presentation. Mathlib's
`Scheme.Hom.isLocallyConstant_finrank` says `f.left.finrank` is locally constant, and a
locally constant function on a preconnected space takes the same value at any two points
(`IsLocallyConstant.apply_eq_of_preconnectedSpace`).

In the contract's route, Step 7 turns the origin value computed in Step 6 into the value at
an arbitrary point `y`, which the target statement quantifies over.
