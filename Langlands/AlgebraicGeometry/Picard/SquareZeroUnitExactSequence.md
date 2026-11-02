# The actual square-zero unit-sheaf sequence

This module constructs the categorical kernel of actual unit reduction and
packages the square-zero closed-immersion sequence as a short exact sequence of
abelian-group sheaves. All declarations are in
`Langlands.AlgebraicGeometry.Picard.SquareZeroUnitExactSequence` and are
universe-polymorphic in `u`.

Let `X : TopCat.{u}`, let `F G : X.Presheaf CommRingCat.{u}` have sheaf
proofs `hF hG`, and let `η : F ⟶ G`. Assume
`h U : SquareZeroKernel (η.app U).hom` for every opposite open `U`.
The imported `unitKernelSheaf η hF hG h` has as its sections the actual
units mapped to one by `η`, written additively. The map
`unitKernelι η hF hG h` includes these sections in the actual unit sheaf
`unitsSheaf F hF`. Its composite with `unitsSheafMap η hF hG` is zero,
as recorded by `unitKernelι_comp`.

For an abelian-group sheaf `A`, a map `k : A ⟶ unitsSheaf F hF`, and a
proof `hk` that its composite with reduction is zero, `unitKernelLift`
factors `k` through the actual unit-kernel subgroup on each open. The
annihilation equation gives subgroup membership. Naturality follows from
naturality of `k`; `unitKernelLift_ι` proves the factorization equation.
Uniqueness follows from equality after the subgroup inclusion.
`unitKernelι_isKernel` packages these facts as an `IsLimit` of the actual
kernel fork. This universal-property argument itself uses no surjectivity.

Precomposing with the published square-zero isomorphism
`kernelSheafIso η hF hG h` defines

    oneAdd η hF hG h : additiveKernelSheaf η hF hG ⟶ unitsSheaf F hF.

The lemma `oneAdd_app_val` identifies its value on an actual kernel
section `a` with `1 + a` in the section ring. `oneAdd_comp` proves that
reduction kills this map. `oneAdd_isKernel` transports the preceding
kernel universal property through `kernelSheafIso`, using
`IsKernel.isoKernel`.

For arbitrary schemes `X Y : Scheme.{u}` and a closed immersion
`i : Y ⟶ X`, assume exactly `hi : i.ker ^ 2 = ⊥`. Here `i.ker` is
Mathlib's ideal-sheaf data. The imported `squareZeroKernel_app` proves
that every actual section-ring kernel of `i.c` is square-zero, including
on nonaffine opens. The specialization `schemeOneAdd i hi` uses this
actual structure-map transformation, the structure sheaf of `X`, and the
pushforward of the structure sheaf of `Y`. Its component formula is
`schemeOneAdd_app_val`.

`schemeUnitSequence i hi` is the `ShortComplex` of sheaves on the
topological space of `X` with terms and maps

    schemeAdditiveKernelSheaf i  --1+a-->  unitsSheaf O_X
                                --reduction-->  unitsSheaf (i_* O_Y).

The last term means the units of the actual pushed-forward ring sheaf:
over `U` it consists of the units of `Γ(Y, i ⁻¹ᵁ U)`, in additive
notation. The second map is the published `unitsReduction i`, rather
than a newly chosen map. `schemeUnitSequence_isKernel` gives its kernel
fork. Finally `schemeUnitSequence_shortExact` combines this kernel
property with the published epimorphism `unitsReduction_epi i ⟨2, hi⟩`.
The kernel gives monicity and exactness; the exponent-two witness gives
nilpotence for the epimorphism. Exactness is sheaf exactness and asserts
no surjectivity on global sections or on arbitrary nonaffine opens.

The provenance is derived from Oort, *Sur le schéma de Picard* (1962),
§6 Lemma 3 and the ensuing unit-sheaf sequence, printed pp.6–7/PDF
pp.7–8 of the retained 15-page scan, registered as
`oort-1962-sur-le-schema-de-picard`, SHA-256
`1322c0cfac1bdd6163122345c60f9a57c5778cc23e6091227a4357678c5a2d30`.
Oort gives the additive identification of the square-zero ideal with
units congruent to one and the exact multiplicative sheaf sequence.
This module supplies the categorical kernel universal property and the
arbitrary-scheme formulation, using the independently published
`SquareZeroUnitSheaves` and `NilpotentUnitReduction` constructions. No
field, properness, projectivity or splitting hypothesis is needed. The
module does not identify Picard classes with unit-sheaf cohomology,
classify line-bundle deformations, or establish Picard representability.
