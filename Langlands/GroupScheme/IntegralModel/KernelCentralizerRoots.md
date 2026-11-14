# Dynamic integral models in character-kernel centralizer components

This derived construction assembles the Library's arbitrary-base dynamic
representability, smoothness, connectedness and three-factor cell results with
its full-character-kernel centralizer root comparisons. It supplies actual
dynamic integral models and identifies their field-fibre root functors, with
the specified maps retained throughout.

The motivating source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), the construction before Theorem 8.2.9 and its proof, printed pages
293–295 (PDF pages 324–326). On printed page 294 the integral cocharacter
produces two opposite unipotents and their centralizer, and the ordered
multiplication is an open immersion. Our ordering is
`U(-χ) × (Z(χ) × U(χ))`; replacing the source's cocharacter by its negative
gives this ordering. The present module derives the model and field comparison
infrastructure from published Library results. It does not prove the residue
radical argument, integral Weyl lifting, translated-cell saturation, the
opposite-factor criterion, or the host depth-zero statement.

## Canonical dynamic integral models

In `IntegralModel.DynamicModels`, let `R` be a commutative domain, `K` its
specified fraction field in the same arbitrary universe, and `M` an integral
model of a `K`-group `G`. Assume that `M.group` is smooth over `R`, and let `χ`
be a group-scheme homomorphism from the integral multiplicative group to
`M.group`. No reductivity or connectedness assumption is imposed here.

`unipotent_affine` and `centralizer_affine` prove affineness of the structural
morphisms of the canonical schemes `Dynamic.Affine.unipotentScheme χ` and
`Dynamic.Affine.centralizerScheme χ`. Their actual closed subgroup inclusions
into the affine model give this property. The corresponding smoothness
instances follow from `dynamicBaseSmoothConnected`. That result also gives
geometric connectedness of the unipotent for every `χ`, and geometric
connectedness of the centralizer when `M.group` has geometrically connected
fibres.

`unipotentGeneric` and `centralizerGeneric` are the actual base changes of
these schemes to `K`. `unipotentModel` and `centralizerModel` use these generic
groups and the identity generic-fibre isomorphism. Smoothness supplies the flat
finite-type requirements of an `IntegralModel`.

`unipotentInclusion` and `centralizerInclusion` extend the actual generic
inclusions, expressed as `M.genericHom` of the canonical integral inclusions.
Their compatibility squares reduce to the identity-composition law.

`unipotent_isRepresentedBy_genericHom` identifies the entire subgroup functor
represented by the generic unipotent inclusion into the specified group `G`.
If `b = Spec.algebraMap R K` and `e = M.genericIso`, this functor is
`(Dynamic.unipotent (Dynamic.baseChangeCocharacter b χ)).comap e.inv`.
The theorem itself needs no smoothness assumption. Its proof base changes
the canonical integral representation, uses `Dynamic.unipotent_baseChange`,
and composes with `e`.

`unipotent_map_integralPoints_eq` proves the exact subgroup equality

```text
image of unipotentModel.integralPoints in G(K)
  = M.integralPoints ∩ points of the preceding generic unipotent functor.
```

Here the point carrier is evaluated at the identity `K`-scheme over `Spec K`;
it is the actual rational-point group. The proof first identifies the generic
range using representation, then applies the closed-subgroup integral-point
intersection theorem. Naturality of the integral inclusion identifies the
resulting range with the image of the source model's integral points.

When `R` is local, `tripleCell` constructs `IntegralTripleCellData` from the
negative unipotent, centralizer and positive unipotent models. Its morphism
is the actual ordered multiplication, with the actual generic groups and
inclusions just described. The constructor `IntegralTripleCellData.ofDynamic`
and the canonical representation proofs supply its open-immersion field.
Locality is retained because the existing triple-cell structure uses a local
base. No residue membership or Weyl element is included in this datum.

## Root comparisons in a full-kernel centralizer component

In `IntegralModel.KernelCentralizerData`, let `T` be a split commutative
integral torus, `i : T.toGrp ⟶ M.group` any torus map, and `a` a character of
`T`. Let `D : KernelCentralizerData M i a` be the constructed data for the
full scheme-theoretic character-kernel centralizer and its smooth relative
identity component. The supporting module constructs such data from splitness
and smoothness of the ambient model. The full character kernel is retained,
including nonprimitive characters and nonreduced kernels.

For any field `k` in the same universe and any base morphism
`b : Spec k ⟶ Spec R`, `D.fibreIso b` identifies the base change of the relative
component with the ordinary identity component of the full-centralizer fibre.
Its torus comparison is the previously established `D.torus_fibreIso`.
No fraction-field or residue-field condition is imposed on `b`.

`cocharacter_fibreIso` proves that the integral cocharacter
`χ = groupHom ν ≫ D.torus hT`, transported through `D.fibreIso b`, is exactly
the base-changed `ν` followed by the canonical torus of the ordinary field
component. Functoriality of base change and `D.torus_fibreIso` prove the
equality.

Assume `0 < latticePairing T a ν`. Pairing compatibility with base change
shows that the field character `a_b` is nonzero
(`character_fibre_ne_zero`). The published
`kernelCentralizerIdentity_dynamicUnipotent_eq_subgroup` and
`kernelCentralizerIdentity_dynamicCentralizer_eq_torusCentralizer` then give:

- `dynamicUnipotent_fibre_eq`: the dynamic unipotent of `χ_b` is the pullback
  along `D.fibreIso b` of the intrinsic `a_b` root functor in the ordinary
  component.
- `dynamicCentralizer_fibre_eq`: the analogous dynamic centralizer is the
  pullback of the centralizer of its entire canonical torus.
- `dynamicUnipotent_fibre_eq_subgroup` and
  `dynamicCentralizer_fibre_eq_torusCentralizer`: the same equalities inside
  the actual relative-component fibre, using its own base-changed torus map.

The transport statements compare functors on all test schemes over `k`.
They require no assumption that `a_b` is an actual root, or that the ambient
torus map is maximal: the reused root-subgroup construction and kernel
comparison apply to the stated nonzero character.

`dynamicUnipotent_fibre_map` proves that the image of this positive dynamic
functor through the actual component inclusion followed by the actual
full-centralizer inclusion is `RelativeRoot.subgroup i_b a_b` in the
original ambient fibre. Nonzeroness and splitness give the character's fpqc
properties. The published intrinsic-root image theorem applies to the
base-changed closed full inclusion. Compatibility of `D.fibreIso b` with the
component inclusion and invariance of image under an isomorphism identify
the resulting image.

`opposite_torusCocharacter` proves over `R` that precomposing `χ` with
inversion is `groupHom (-ν) ≫ D.torus hT`. The negative-root comparison
`dynamicOppositeUnipotent_fibre_eq_subgroup` applies the same field theorem
to `(-a_b,-ν_b)`, whose pairing is positive. The full kernel centralizer and
its canonical torus are unchanged by negating the character.
`dynamicOppositeUnipotent_fibre_map` gives its image as the ambient
`(-a_b)` root functor through the same inclusions.

These field image theorems do not assert an integral closedness property for
the relative-component inclusion into the original model. In particular, the
exact integral intersection theorem above applies within its chosen ambient
model, including `D.model` over a DVR, and is not an asserted equality with
the original `M`'s integral points through that component inclusion.

## Choosing the integral cocharacter

`exists_integralCocharacter_pairing_pos` assumes only `a ≠ 0` in addition to
the domain/fraction-field and split-torus setup. It produces an integral `ν`
with positive `a`-pairing whose generic base change is a generic cocharacter
for the supplied generic ambient torus map. The model's affineness and
finite-type properties suffice; smoothness, locality, the DVR property,
maximality and closedness of `i` are not additional hypotheses.

The proof uses injectivity of split character-lattice base change to keep the
generic character nonzero. The published field theorem
`RelativeRoot.exists_genericCocharacter_pairing_pos` gives a suitable generic
cocharacter. Surjectivity of split cocharacter-lattice base change lifts it to
`R`, and `latticePairing_baseChange` preserves its positive pairing.

Thus, over a DVR, the existing `D.model` and this choice of integral
cocharacter can be supplied directly to the canonical dynamic model and
triple-cell constructors above. The new field comparisons identify both
signs and the centralizer without adding a cocharacter-spreading or root
identification premise.
