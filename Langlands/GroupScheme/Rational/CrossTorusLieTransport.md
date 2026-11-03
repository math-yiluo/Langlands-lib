# Actual Lie weights and roots under cross-torus transport

This is derived internal infrastructure built from the published actual
Lie kernels, their linear target maps, the all-coefficient-algebra weight-space
definition, and the character and cocharacter congruences. Worker 118 identified
the cross-torus interface for apartment consumers. No external structure theorem
is introduced.

Let `R` be a commutative ring object, `S` and `S'` commutative group schemes over
`Spec R`, and `G` and `H` group schemes with affine structural morphisms over that
base. The acting morphisms are `i : S.toGrp ⟶ G` and `j : S'.toGrp ⟶ H`. Fix
isomorphisms `e : S ≅ S'` and `f : G ≅ H` satisfying the exact square

```
i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j.
```

The character identification is the published `characterLattice.congr e`:
`a` is sent to `e.inv ≫ a`. No splitness, smoothness, reducedness, monomorphic
inclusion, connectedness, reductivity, finiteness, or root-membership hypothesis
is required for the weight constructions.

`Lie.targetEquiv f A` is an `A`-linear equivalence between the actual dual-number
identity kernels `Additive (lieKernel G A)` and `Additive (lieKernel H A)` for
every commutative `R`-algebra `A` in universe `u`. Its forward and inverse maps
are exactly `Lie.targetMapLinear f.hom A` and `Lie.targetMapLinear f.inv A`.
The two inverse laws are exposed by `Lie.targetMapLinear_hom_inv` and
`Lie.targetMapLinear_inv_hom`.

The weight-space definition tests every coefficient algebra and every point of
the acting group. `mem_weightSpace_precomp_torus_hom` first preserves this
condition under an arbitrary morphism from a possibly different acting group,
provided the character is precomposed by the same morphism. Combining this with
published differential naturality gives
`lieKernelHomLinear_mem_weightSpace_of_transport`. This forward result needs
only an ambient homomorphism `f`, with the square and acting-group isomorphism.
For an ambient isomorphism,
`lieKernelHomLinear_mem_weightSpace_transport_iff` preserves and reflects weight
membership, and `weightSpace_map_of_transport` gives the exact submodule equality

```
(weightSpace i a).map (Lie.targetMapLinear f.hom R)
  = weightSpace j (characterLattice.congr e a).
```

`weightSpaceTransportEquiv e f h a` is an actual `R`-linear equivalence of these
weight-space carriers. Its maps restrict the same forward and inverse
differentials, as recorded by `weightSpaceTransportEquiv_apply` and
`weightSpaceTransportEquiv_symm_apply`. In particular, this is a comparison of
the published all-test weight spaces, not a comparison of chosen abstract root
models or only the action on the base ring's points.

`roots_mem_of_transport_iff` and `roots_image_of_transport` identify the full
actual character-valued root sets. They use the definition of a root as a
nonzero character with nonzero weight submodule. `rootsTransportEquiv e f h`
restricts exactly `characterLattice.congr e` to a bijection between those root
subtypes. All these results retain the arbitrary commutative affine base.

For a supplied base point `g` with ambient isomorphism `G.innerIso g`,
`weightSpaceTransporterEquiv` uses this same isomorphism. On the underlying
actual dual-number point `X`, its forward formula is
`g_D * X * g_D⁻¹`, where `g_D` is the constant point on the dual-number test.
The inverse formula is `g_D⁻¹ * X * g_D`. These formulas are stated by the two
`weightSpaceTransporterEquiv_*_apply_val` lemmas; no new transporter is chosen.

Over a field `k`, `relativeRoots_image_of_transport` and
`relativeRootsTransportEquiv` specialize to the published `relativeRoots`,
which are the same character-valued Lie roots. Transport the chosen cocharacter
`ν` by `cocharacterLattice.congr e`. The integer pairing is preserved by the
published `latticePairing_congr`. Consequently
`positiveRelativeRoots_mem_of_transport_iff` preserves and reflects positivity,
and `simpleRelativeRoots_mem_of_transport_iff` preserves and reflects
indecomposability in the full positive relative roots. The latter proof
transports both summands and uses additivity and bijectivity of the character
congruence. It therefore includes nonreduced relative-root systems without
replacing them by their reduced roots. Finally,
`isGenericCocharacter_of_transport_iff` preserves and reflects nonzero pairing
with every actual relative root.

The implemented proof reuses `Lie.targetMapLinear` and its adjoint and coefficient
naturality from `Lie.Functoriality`. Reparametrization evaluates an old weight
identity at the image of each new acting-group point; `Lie.characterValue_comp`
identifies its scalar. The inverse square follows by composing with both supplied
inverse isomorphisms. Applying forward transport to that square gives reflection.
The inverse identities on actual dual-number points prove the linear equivalences.
Their submodule-image equality preserves nonvanishing, and the character
congruence preserves zero exactly, giving the root comparison.

The acting and ambient isomorphisms and the commuting square remain supplied
inputs. This file does not prove existence or conjugacy of tori, root-system
realization, root-subgroup representability, or any building, apartment, topology,
or valuation assertion. These comparisons are algebraic inputs for such further
constructions.
