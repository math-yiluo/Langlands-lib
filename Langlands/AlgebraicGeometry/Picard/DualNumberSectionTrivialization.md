# Global sections not killed by epsilon trivialize first-order deformations

This helper module works on the published actual first-order thickening
`DualNumberThickening.thickening f = pullback f (dualNumberProjection k)` of a
scheme `X` with a morphism `f : X ⟶ Spec k`, for any field `k`. Its declarations
are in namespace `Langlands.AlgebraicGeometry.Picard.DualNumberThickening`. It
imports `Picard/DualNumberAffineFrames` and `Modules/SectionCoefficients`.

## Declarations

- `globalEpsilon f : Γ(thickening f, ⊤)` is the image of `ε` under the global
  ring map of the structure morphism `structureMap f` to `Spec k[ε]`:
  `((Scheme.ΓSpecIso _).inv ≫ (structureMap f).appTop) ε`.
- `globalEpsilon_restrict f U`: restricted to `projection f ⁻¹ᵁ U`, it is the
  published `epsilonSection f U`. This holds by `rfl`.
- `epsilonSection_mul_sectionMap_of_fst_eq_zero f U z hz`: for
  `z : DualNumber Γ(X, U)` with `z.fst = 0`,
  `epsilonSection f U * sectionMap f U z = 0`. In `DualNumber Γ(X, U)`,
  `ε * z = 0` is checked coordinatewise. The published `sectionMap_eps` and
  multiplicativity of the ring map `sectionMap f U` then give the claim.
- `exists_coefficient_affineNormalizedFrame U hU L e s`: let `U` be an affine
  open of `X`, `L` a line bundle on `thickening f`, and
  `e : (pullback (closedPoint f)).obj L.obj ≅ structureModule X` a trivialization
  along the zero section. Then for every global section `s` of `L` there is
  `z : DualNumber Γ(X, U)` with two properties. First, the restriction
  `sectionRes L.obj s (projection f ⁻¹ᵁ U)` equals
  `sectionMap f U z • affineNormalizedFrame f U hU L e`. Second, `z.fst` is the
  restriction to `U` of `reducedCoefficient f ⊤ L.obj e s`.
- `isIso_sectionHom_of_globalEpsilon_smul_ne_zero hX L e s hs`: assume every
  global function of `X` is zero or a unit (`hX`). Let `L` and `e` be as above,
  and let `s` be a global section of `L` with `globalEpsilon f • s ≠ 0` (`hs`).
  Then `sectionHom L.obj s : structureModule (thickening f) ⟶ L.obj`, the
  morphism sending `1` to `s`, is an isomorphism.

## Implemented proofs

`exists_coefficient_affineNormalizedFrame`. The published normalized frame
`u = affineNormalizedFrame f U hU L e` is a frame on `projection f ⁻¹ᵁ U`
(`affineNormalizedFrame_isFrame`). Surjectivity of multiplication by `u` on that
open writes the restricted section as `a • u`; restricting `u` along the identity
is the identity. Take `z = (sectionEquiv f U).symm a`. The first property follows
from `sectionEquiv_apply`. For the second, `reducedCoefficient_smul` and
`reducedCoefficient_affineNormalizedFrame` give
`reducedCoefficient (a • u) = reductionMap f U a * 1`. The published
`reductionMap_sectionEquiv` identifies `reductionMap f U a` with `z.fst`.
`reducedCoefficient_naturality` along `U ≤ ⊤` identifies the left side with the
restriction of the global reduced coefficient.

`isIso_sectionHom_of_globalEpsilon_smul_ne_zero`. Every point of the thickening
lies in `projection f ⁻¹ᵁ U` for some affine open `U`, by
`iSup_affineOpens_eq_top`. Let `c = reducedCoefficient f ⊤ L.obj e s`.

- If `c = 0`, the proof shows `globalEpsilon f • s = 0`, contradicting `hs`.
  The sheaf `L.obj.presheaf` satisfies `TopCat.Sheaf.eq_of_locally_eq'` on the
  cover by the opens `projection f ⁻¹ᵁ U`. On each of them, `Scheme.Modules.map_smul`
  and `globalEpsilon_restrict` give the restriction
  `epsilonSection f U • (sectionMap f U z • u)`, with `z.fst = 0`. This is `0`
  by `smul_smul` and the previous lemma.
- If `c` is a unit, then on each affine `U` the first coordinate `z.fst`, the
  restriction of `c`, is a unit. So `z` is a unit
  (`TrivSqZeroExt.isUnit_iff_isUnit_fst`), and so is `sectionMap f U z`. By the
  published `isFrameOn_smul_unit`, `sectionMap f U z • u`, which is the
  restriction of `s`, is a frame on `projection f ⁻¹ᵁ U`. For every smaller open
  `W`, `sectionHom_app` and `sectionRes_res` identify `(sectionHom L.obj s).app W`
  with multiplication by the restriction of that frame. So it is bijective, and
  `le_trivializationOpen_of_bijective` puts `projection f ⁻¹ᵁ U` inside the
  published `trivializationOpen L.obj s`. Hence that open is `⊤`.
  `bijective_sectionHom_app_of_le` makes every component bijective, and
  `Scheme.Modules.Hom.isIso_iff_isIso_app` with
  `ConcreteCategory.isIso_iff_bijective` concludes.

## Provenance and scope

This is an internal helper for the proof of
`AlgClosedFieldPoincareTangentSectionsStatement`. It formalizes the local step of
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, (9.5), printed p.128
(PDF p.132), in the first-order case: a section of a deformation of a trivial
line bundle whose reduction is a nowhere-vanishing function trivializes the
deformation. Here a nonzero constant reduction is detected by `ε • s ≠ 0`. There
is no finiteness, separation or properness assumption on `X`; the only
hypothesis on `X` is that its global functions are zero or units.
