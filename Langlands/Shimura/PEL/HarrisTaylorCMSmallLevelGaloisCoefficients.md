# Galois actions on arithmetic coefficients of actual small CM levels

This is an internal construction on the existing represented CM schemes. It
identifies their actual geometric tower with its generic base-change construction,
constructs its Galois action, and applies that action to coefficients pulled back
from the arithmetic base. The comparison, tower action, coefficient transitions
and cohomology are constructed here or by the imported published generic APIs.
None is supplied as arbitrary output data.

The module uses the namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. Its arithmetic carriers, schemes
and coefficient ring have universe zero. Write

- `small = D.rationalInvolution.LevelSufficientlySmall`;
- `G = D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`;
- `Fbar = AlgebraicClosure F` and `Gamma = Fbar ≃ₐ[F] Fbar`;
- `T = cmSchemeTower ... q` and `Tbar = cmGeometricSchemeTower ... q`.

The level category is the existing `SmallCMLevel D`, the full transporter
subcategory on sufficiently small compact open levels of `G`. The arithmetic
data retain the CM extensions, rational scalar towers, unitary datum `D`,
CM-compatible signature charts `C`, and the named tensor, Picard, duality,
polarization, Weil-transition and torsion inputs. The parameter `q` is the exact
`CMRepresentabilityStatement` about the already defined CM moduli presheaves,
with representing isomorphisms, smoothness and projectivity. It does not choose
unconstrained schemes. Both towers use exactly the representation witnesses
selected from this same `q`.

## Actual base maps and comparison

`cmSmallLevelArithmeticStructure` is the natural transformation
`s : T ⟶ const (Spec F)` whose components are the structure morphisms of
`representedCMOverTower`. Naturality for every transporter is its over-category
morphism law.

`cmSmallLevelBaseChangeIso` constructs an isomorphism from
`RestrictedLevelTowerGalois.baseChangeTower F Fbar s` to `Tbar`. Both objects at a
level are the same scheme fiber product

`T(U) ×[Spec F] Spec Fbar`.

Its components are identity isomorphisms. Naturality is proved by equality after
each pullback projection, using the actual maps of `cmGeometricOverTower`. Thus
no comparison isomorphism is an input.

`cmSmallLevelArithmeticGeometricStructure` is the natural transformation
`p : Tbar ⟶ const (Spec F)` obtained by composing `cmGeometricProjection` with
`s`. The theorem with suffix `_eq` proves that it also equals the geometric
structure map to `Spec Fbar` followed by `cmGeometricFieldMap`. The proof is the
pullback condition. The comparison theorem with suffix `_projection` proves
that the constructed base-change isomorphism preserves the first projections
to `T`.

These constructions use `q` and its original inputs, without the additional
map-etaleness or rigidity premises introduced below.

## Actual Galois tower action

`cmSmallLevelGaloisAut σ` transports the generic `towerGaloisAut s σ` through
the constructed comparison. `cmSmallLevelGaloisAut_hom_app` proves that its map
at level `U` is exactly

`EtaleGaloisAction.baseChangeMap (s.app U) σ`.

This is the base-change automorphism acting on the algebraic-closure factor
with the spectrum convention of `EtaleGaloisAction`. Its action on the first
projection is the identity.

`cmSmallLevelGaloisAction` is the group homomorphism

`Gamma →* (Aut Tbar)ᵐᵒᵖ`.

The opposite automorphism group records contravariance. The identity and
multiplication laws are proved componentwise from `baseChangeMap_one` and
`baseChangeMap_comp`. `cmSmallLevelGaloisAction_over` proves

`(cmSmallLevelGaloisAction σ).unop.hom ≫ p = p`.

It uses the first-projection equation, so the action is over `Spec F`. There is
no assertion that these automorphisms fix the geometric structure map to
`Spec Fbar`.

## Arithmetic inverse-image coefficients

The remaining constructions retain `RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, rigidity `CMGeometricCoarseRigidity` at
every small CM level, and `DominantUnramifiedEtaleStatement`. The existing
`cmSmallLevelTowerEtale` theorem derives etaleness of every original geometric
transporter under exactly these inputs. Each construction installs this result
locally. Etaleness of the structural maps to `Spec F` is not required by the
arbitrary-morphism inverse-image functor.

For a commutative ring `R : Type` and an actual small-etale module sheaf `M` on
`Spec F`, `cmSmallLevelArithmeticCoefficients M` is the compatible coefficient
diagram on `Tbar.op` constructed by `canonicalCoefficients R p M`. The object
formula is

`M_U = (EtaleInverseImage.inverseImage (p.app U) R).obj M`.

For `k : U ⟶ V`, the transition on `k.op` restricts `M_V` along the actual map
`Tbar.map k` and maps it to `M_U`. The theorem with suffix `_map` identifies it
with `LevelTowerCohomology.restrictionProjectionIso` for these two structure
maps, this transporter, and its naturality triangle. The generic inverse-image
comparison supplies the identity and composition laws.

`cmSmallLevelArithmeticCoefficients_trivial` proves the full property
`cmSmallLevelTrivialCoefficients`. The scheme identity for each element of its
level comes from `cmGeometricSchemeTower_restrictedSelfArrow`. Congruence of
the constructed projection comparisons then identifies the coefficient map
with the identity transition after the required restriction transport. This
proves a sheaf-level identity for these coefficients; no additional
coefficient-triviality premise is assumed.

`cmSmallLevelArithmeticCoefficientsFunctor` sends base sheaves into this full
subcategory of level-trivial coefficient diagrams. Its object is the diagram
just described, and its morphism at `U` is inverse image of the base-sheaf
morphism along `p.app U`, as the two accompanying formulas show.

## Smooth cohomology and commuting actions

`cmSmallLevelArithmeticCohomologyFunctor d` takes ordinary degree-`d`
small-etale cohomology with the constructed coefficients, forms the colimit
over shrinking sufficiently small level inclusions, and supplies its smooth
`G` action. Ordinary cohomology here means the right-derived global-sections
functor of `EtaleDerivedSections`.

Rational finite dimensionality of `A` is derived locally from `D.finite` over
`F`, the number-field instance for `F`, and `Module.Finite.trans F A`. This
supplies the existing actual smallness closure instances used by the generic
smooth-colimit construction. It is not a separate finiteness premise.

The object theorem identifies this functor with
`cmSmallLevelSmoothCohomology` for exactly
`cmSmallLevelArithmeticCoefficients M` and its proved triviality. Consequently
its colimit uses the actual ordered inclusion index already constructed for
these CM levels. The transporter category supplies the finite-adelic action.

`cmSmallLevelGaloisCohomologyFunctor d` has type

`ModuleSheaf (Spec F) R ⥤ Action (SmoothRep R G) Gamma`.

It specializes `RestrictedLevelTowerCohomology.automorphismActionFunctor` to
the same actual tower, the constructed map `p`, the proved actual scheme
self-arrow identity, and `cmSmallLevelGaloisAction` with its proved over-base
property. The components of a tower automorphism are scheme isomorphisms and
hence etale, as required for cohomological pullback. Functoriality in `M` and
the Galois group laws are inherited from that generic construction.

The `_obj_V` theorem and `cmSmallLevelGaloisCohomologyForgetIso` identify its
underlying smooth representation and functor with the arithmetic cohomology
functor above. The latter natural isomorphism is the identity.

`cmSmallLevelGaloisCohomologyFunctor_ρ` identifies the action of `σ` with
`smoothCanonicalPullback` along its actual tower automorphism over `Spec F`.
`cmSmallLevelGaloisCohomology_ρ_ι_apply` gives its value on a class represented
at level `U`: pull back that class along
`(cmSmallLevelGaloisAction σ).unop.hom.app U`, apply the constructed
projection-coefficient comparison, and insert it into the colimit at the same
level `U`. Its proof evaluates the generic `canonicalPullback_ι` equality on
the class. The earlier `_hom_app` theorem identifies this scheme map with the
actual `baseChangeMap (s.app U) σ`.

`cmSmallLevelGaloisCohomology_commutes` proves pointwise that this Galois
operator commutes with each `g : G`. It is the intertwining identity of its
morphism in `SmoothRep R G`. Thus both actions concern the same actual module,
and their compatibility is proved.

## Provenance and retained obligations

This unit is an internal consequence of the existing CM over-towers, their
pullback projections and scheme self-arrow identity, and the generic
`RestrictedLevelTowerCanonicalCoefficients` and `RestrictedLevelTowerGalois`
constructions. It asserts no additional theorem from external literature.
Its comparison is constructed from the identical actual fiber products;
its coefficients and cohomology use the existing small-etale sheaf functors.

`Gamma` is used as an algebraic group here. No topology on it, continuity of
its action, or adic limit is constructed. The coefficient input is a sheaf
on `Spec F`. This unit does not construct the general nonconstant Harris
coefficient system from an algebraic representation, its lattice descent, or
an all-level comparison for that system. Arbitrary sheaves on `Spec Fbar`
remain the distinct input of `HarrisTaylorCMSmallLevelBaseCoefficients`.

Exact representability, the named geometric hypotheses, existence of the
required global arithmetic datum, small-level nonemptiness, and the source's
canonical-model and reflex-field comparisons remain separate obligations.
There is no unconditional representability, identification of `F` as a reflex
field, compactly supported cohomology, or whole-task completion claim here.
