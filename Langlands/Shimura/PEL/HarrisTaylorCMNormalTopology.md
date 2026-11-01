# Quotient topology of original CM normal projections

This module proves that the original CM normal forgetting morphism is a
topological quotient map and an open map. It constructs an order isomorphism
between the open sets of the actual coarse scheme and the residual-invariant
open sets of the actual fine scheme. The forward map is literal preimage
under the original forgetting morphism; the inverse is literal image.
The results are conditional on the exact existing representing witnesses
and the named infrastructure and relative-dual assertions below.

## Arithmetic, infrastructure and representing hypotheses

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic parameters
are a totally real number field `E`, a CM number field `F` quadratic over
`E`, a datum `D : CentralSimpleUnitaryData E F A n`, an imaginary quadratic
CM field `L` mapping to `F`, and a complex embedding `τ₀ : L →+* ℂ`.
The signature charts `C` use the constructed Harris CM section. The Lean
context explicitly retains the algebra structures and scalar towers over
`ℚ`, `E` and `F`. The inherited moduli use the normalized Harris–Taylor
reflex structure, positive auxiliary involution, polarization and
Weil-pairing conventions.

The named infrastructure inputs are pullback-tensor preservation,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback stability, the Mumford-bundle assertion and
universal base change; dual-abelian base-change naturality; polarization
base-change stability; relative finite Weil-transition compatibility;
the actual rational/profinite-integer/adele comparison; and torsion finite
etaleness. Their exact proposition types are the Lean binders. In
particular, torsion finite etaleness concerns abelian-scheme torsion,
and supplies no etaleness assertion about the forgetting morphism.

`R` supplies the existing `CMLevelRepresentation` at every
`SmallCMLevel D`. Each witness consists of an actual admissible scheme
over `Spec F`, smoothness, projectivity through an actual projective-space
closed immersion, and a representing natural isomorphism from lifted
Yoneda to the fixed small-level class presheaf. The transitions are the
already constructed Yoneda-induced morphisms of
`representedCMSchemeTower ... R`.

The representing test category is
`ComponentwiseAdmissibleCMBaseCategory`: locally Noetherian schemes over
`Spec F` whose actual connected-component schemes are admissible CM
bases. All over-category morphisms between those objects are retained.
The presheaf is the existing product of unpointed compatible class towers
over those components. Its rational-isogeny classes retain a representative
satisfying the determinant and numerical dimension tests jointly. No
invariance of dimension under arbitrary rational isogenies is assumed.
This remains a restricted test category; the contribution supplies no
comparison theorem with the full source moduli problem.

The quotient-map theorem, saturation and openness theorems, image
construction, inverse laws and order isomorphism additionally take
`RelativeDualSchemeExistenceStatement.{0}` and
`RelativeDualSchemeGeometryStatement.{0}`. These assert universal dual
scheme existence and the smooth, proper, geometrically connected geometry
of dual witnesses over the specified quasi-separated bases. Their use
here is inherited from the existing original-projection surjectivity and
point-fiber transitivity proofs: those proofs admit the actual
algebraically closed field-test spectra using
`admissibleCMBase_iff_dualGeometry`. The two propositions assert no
quotient, openness or etaleness property of the level morphisms.
Defining the invariant opens and the preimage map needs neither of these
two additional assertions.

## Original schemes, projection and residual action

Write `X_V` and `X_U` for the objects of
`representedCMSchemeTower ... R` at the fine and coarse small levels,
with the explicit inclusion
`hVU : V.obj.subgroup ≤ U.obj.subgroup`. Set

```
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
Q = SmallCMResidualGroup D U V,
ρ = representedCMNormalQuotientAction ... R U V hVU.
```

The morphism `p` is exactly the tower map at `smallCMInclusion D hVU`.
The group `Q` is the quotient of `U.obj.subgroup` by
`V.obj.subgroup.subgroupOf U.obj.subgroup`; the normality instance refers
to that subgroup of `U`. The action retains the original opposite-group
and inverse-right conventions: a representative `g` acts by the level
transporter with element `g⁻¹`. It is an action by actual scheme
morphisms, and each `ρ(g)` is the hom of the scheme automorphism
`ρ.ρAut g`. The original invariance equation is
`ρ(g) ≫ p = p`.

In set formulas below, `p` and `ρ(g)` denote their underlying point
functions. The Lean code exposes the latter through
`(Scheme.Hom.toLRSHom (ρ.ρ g)).base`. No scheme or point function is
replaced by a newly chosen quotient model.

## Quotient map, saturation and openness

`representedCMNormalProjection_isQuotientMap` uses properness of the
original projection to obtain a closed map on underlying points. That
properness was proved in `HarrisTaylorCMFiniteEtale` from the representing
schemes' actual projectivity and the transition equation over `Spec F`;
it needs no etaleness premise. The original projection is continuous
because it is a scheme morphism, and
`representedCMSchemeTower_map_surjective` proves its underlying
surjectivity under the displayed relative-dual inputs. Mathlib's
closed-continuous-surjective criterion then gives `Topology.IsQuotientMap p`.
This declaration explicitly omits the normality assumption, since an
inclusion of small levels suffices for this conclusion.

For every set `s` of actual fine-level points,
`representedCMNormalProjection_preimage_image` proves

```
p ⁻¹' (p '' s) = ⋃ g : Q, ρ(g) '' s.
```

For a point on the left, choose `z ∈ s` with `p z = p x`.
The existing `representedCMNormalPoint_exists_translate` gives an
actual residual element `g` with `ρ(g)(z) = x`. That theorem was proved
from original kernel-comparison surjectivity using actual scheme
pullback points and actual coproduct summands. It requires neither
injectivity nor invertibility of the comparison. Conversely, a point
`ρ(g)(z)` with `z ∈ s` lies on the left by the original projection
invariance equation.

`representedCMNormalProjection_isOpenMap` now tests openness of `p '' s`
by its preimage, using the proved quotient topology. The saturation
formula identifies this preimage with the union of the translates of
`s`. Each translate is open because the actual scheme automorphism
`ρ.ρAut g` induces a homeomorphism. The union is open, so `p '' s`
is open. This argument uses no finite-fiber criterion and no etaleness
or rigidity premise.

## Concrete invariant opens and inverse maps

`representedCMNormalInvariantOpens` is the subtype

```
{W : X_V.Opens // ∀ g : Q, ρ(g) ⁻¹' (W : Set X_V) = (W : Set X_V)}.
```

It inherits the partial order from the actual open subsets of `X_V`.
`representedCMNormalOpenPullback` sends a coarse open `W` to
`p ⁻¹' W`. Continuity proves this preimage open, and
`ρ(g) ≫ p = p` proves its invariance. This definition uses only the
original infrastructure, representing witnesses, inclusion and normal
residual action.

Under the two relative-dual assertions,
`representedCMNormalOpenDescend` sends an invariant fine open `W` to
`p '' W`. The preceding open-map theorem proves that this literal image
is an open subset of the original coarse scheme.

`representedCMNormalOpenPullback_descend` proves that pulling back this
image returns `W`. For `p x ∈ p '' W`, choose `z ∈ W` with
`p z = p x`. Original point-fiber transitivity gives
`ρ(g)(z) = x`, and the defining invariance of `W` shows `x ∈ W`.
The other containment uses `x` itself as an image witness.
The proof uses subtype and open-set extensionality.

`representedCMNormalOpenDescend_pullback` proves that the image of the
preimage of a coarse open is that original coarse open. It applies
`Set.image_preimage_eq` with the independently proved surjectivity of
the same original `p`.

`representedCMNormalOpensOrderIso` packages these two constructions and
inverse laws as

```
X_U.Opens ≃o representedCMNormalInvariantOpens ... R U V hVU.
```

The order equivalence is proved using the surjectivity criterion for
inclusions between preimages: `p ⁻¹' W ⊆ p ⁻¹' Z` if and only if
`W ⊆ Z`. The theorems
`representedCMNormalOpensOrderIso_apply_coe` and
`representedCMNormalOpensOrderIso_symm_apply_coe` are reflexive set
identities with the literal original preimage and image.

## Identical chosen tower

Given `q : CMRepresentabilityStatement ...`, the final declarations
substitute exactly `chosenCMLevelRepresentation ... q` for `R`. This
is the family defining the existing `cmSchemeTower ... q` and
`cmNormalQuotientAction ... U V hVU q`. There is no additional choice of
representing schemes or transition maps.

`cmNormalProjection_isQuotientMap`,
`cmNormalProjection_preimage_image` and
`cmNormalProjection_isOpenMap` give the quotient topology, saturation
formula and openness directly for
`(cmSchemeTower ... q).map (smallCMInclusion D hVU)`.
The quotient-map specialization again omits normality.

`cmNormalInvariantOpens`, `cmNormalOpenPullback`,
`cmNormalOpenDescend`, `cmNormalOpenPullback_descend` and
`cmNormalOpenDescend_pullback` are the same subtype, functions and
inverse laws for these identical witnesses.
The entry definition `cmNormalOpensOrderIso` is the resulting order
isomorphism on the opens of the original chosen coarse scheme.
`cmNormalOpensOrderIso_apply_coe` and
`cmNormalOpensOrderIso_symm_apply_coe` identify its forward carrier and
inverse carrier reflexively with preimage and image under the original
chosen forgetting map and use the same chosen residual action.
The exact `q` and the relative-dual premises remain inputs.

## Source, provenance and remaining obligations

The source conventions are Harris and Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91,
one-based PDF pp.98–99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage defines sufficiently small full-adelic compact-open levels
through a torsion-free local projection, extends the moduli problem by
the product over connected components, and specifies polarized CM
frame-orbit classes up to isogeny with rational polarization multiplier.
It gives right frame-composition transitions and separately asserts
smooth projective representability, finite-etale forgetting and the
normal-level Galois cover with group `U/V`.

This contribution is an internal topology deduction from the displayed
formal premises and existing constructions. Its proof uses original
properness and surjectivity, original point-fiber transitivity and
projection invariance, homeomorphisms induced by the residual scheme
automorphisms, and ordinary image/preimage identities. This route is
not presented as the source's proof of its full covering theorem.

The formal conclusion concerns underlying topological spaces and their
open sets. It supplies no categorical quotient in schemes or
structure-sheaf invariant comparison. Applicable division/global
representability, the full source-moduli comparison, rigidity from
source smallness, etaleness of the original projection, invertibility of
the original kernel comparison under these inputs alone, canonical-model
comparisons, uniformization and actual coefficient-system descent
remain obligations. The conditional kernel-isomorphism and torsor
constructions requiring original etaleness are not used to prove it.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
