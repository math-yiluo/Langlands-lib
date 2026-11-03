# Coherent normalized Jacquet duality from opposite Iwahori contractions

Author: Worker 1004. Worker 127 contributed the structural interface and the
full-modulus reciprocity formulation.

`Langlands.Aubert.General.NaturalNormalizedJacquetDuality` is a data type
containing a chosen family of isomorphisms and its bundled naturality law.
The noncomputable definition
`naturalNormalizedJacquetDualityOfIwahoriContractionsOfReciprocalModulus`
constructs this data from explicit structural premises. Two helper theorems
transport the published stable evaluation pairing to the literal
`normalizedJacquetFunctor` of `General.Parabolic`. This packaging is internal
and derived.

The ambient group is any locally compact nonarchimedean group `G`. The
subgroups `U` and `O` are closed and normalized by the common acting subgroup
`M`. One fixed `g : G` commutes with every element of `M`, and
`Jacquet.HasOppositeIwahoriContractionBasis U M O g` supplies arbitrarily small
compact open subgroups with both contraction orientations, using `g` and
`g⁻¹`. No semidirect decomposition is needed by this transport: the normalized
functors use only closedness and normalizer inputs.

`exists_naturalNormalizedJacquetDuality_of_iwahoriContractions` additionally
assumes that the actual inverse-half Haar characters satisfy
`χU(m) * χO(m) = 1` as complex scalars for every `m : M`.
The corollary
`exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus`
instead assumes
`closedRestrictCharacter U hU M hMU m *
closedRestrictCharacter O hO M hMO m = 1`
in the units of the nonnegative reals. These are the actual Haar scaling
characters on the two subgroups, rather than separately chosen characters.

Write `rU` and `rO` for the resulting actual normalized functors. Each theorem
constructs one family
`E A hA : rU.obj A.contragredient ≅ (rO.obj A).contragredient`
on all admissible smooth complex representations of `G`. For every actual
morphism `f : A ⟶ B` between admissible objects it proves the bundled equation

`rU.map (SmoothRep.contragredientHom f) ≫ (E A hA).hom =
(E B hB).hom ≫ SmoothRep.contragredientHom (rO.map f)`.

Both sides have source `rU.obj B.contragredient` and target
`(rO.obj A).contragredient`. The group universe `uG` and carrier universe `uV`
are independent. Admissibility concerns finite-dimensional fixed spaces;
there is no finite-length or finite-dimensional whole-carrier premise.
The fields `NaturalNormalizedJacquetDuality.iso` and `.naturality` store
exactly this family and equation. The noncomputable constructor uses
`Classical.choose` on the full-modulus existence theorem and
`Classical.choose_spec` for the naturality field.

The implemented argument first forms
`Jacquet.stablePairingDataOfIwahoriContractions`.
`StablePairingData.admits_of_iwahoriContractions` supplies its stable-image
and kernel conditions from admissibility and both contraction orientations.
`StablePairingData.exists_isStablePairing` then gives a stable pairing `b`.
Its `IsStablePairing.exists_equiv` gives the equivariant equivalence on
coinvariants, using the identity continuous equivalence of the literal group
`M` and the reciprocal scalar characters.

`Jacquet.Localization.trivialEquiv` identifies each actual localized quotient
at the trivial character with the coinvariant quotient used by `b`.
`twistEquiv` and `SmoothRep.contragredientIso` transport the lower comparison
to smooth functionals. This produces an isomorphism whose evaluation is
exactly `b` on the two quotient representatives. The proof chooses these
isomorphisms simultaneously for all admissible objects. It proves the
naturality equation by bundled-morphism extensionality, surjectivity of
`Localization.mk`, and `IsStablePairing.natural`.

For the full-modulus corollary, the composition of the positive square-root
homomorphism on units and the complex embedding is a monoid homomorphism
`F : ℝ≥0ˣ →* ℂˣ`. The actual inverse-half characters are the inverses of
`F` applied to the respective full Haar characters. Multiplicativity of `F`
and the given full-character product identity imply the required
inverse-half scalar product identity.

The substantial transitive proof dependencies are
`stableImageJacquetMap_bijective_of_iwahoriContraction`,
`powerKernelSup_eq_ker_of_iwahoriContraction`,
`compactCompression_stableEvaluationDuality`,
`isAdmissible_smoothContragredient_of_compact_cofinal`, and the stable-pairing
existence, equivalence and naturality results just named. They work for the
abstract group and its given compact open subgroups. The finite-dimensional
stable images come from admissibility. The proof also uses the actual
coinvariant, localization, Haar-character, character-twist and bundled smooth
contragredient definitions.

A recursive inspection of the constructor's type and body, including the
types and values of project constants they reference, reaches 454 project
declarations in 44 modules. None is a classification, character-independence,
geometric-lemma, parabolic-adjointness or cuspidal-support result.
`Jacquet.compressedAction_adjoint` and
`Jacquet.compressedAction_pow_adjoint` occur in this closure; their
adjointness is the evaluation identity for finite averaging operators and
their transposes.

The import graph is broader than that declaration closure.
`Category.Contragredient` imports
`Classification.SupercuspidalContragredientAux` and `Group.GL.CompactOpen`;
among their declarations are the abstract compact-cofinal
`isAdmissible_of_smoothContragredient`, the bidual-based
`isIrreducible_smoothContragredient_iff_of_bidual`, the general-linear
`isSupercuspidal_iff_standard`, and the p-adic general-linear
`GeneralLinear.compactOpen_cofinal`. `General.Parabolic` imports
`CompactCoefficient.GroupTransport`, whose imports reach
`CuspidalSupport.glCuspidalTensorAssociation` for p-adic general-linear
cuspidal tensor factors and `Geometric.weylMinimalRepresentativeUniqueness`
for block permutations. None of these declarations is used by the two
theorems here. No character-independence, geometric-lemma or
parabolic-adjointness module occurs in their project import graph.

The mathematical provenance is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019:
III.5.5 and III.5.7 on page 7 and III.6.2–III.6.3 on pages 7–8. Applying
III.6.3 to the opposite parabolic gives the orientation used here. Coherent
naturality is derived from compatibility of canonical stable lifts with
actual intertwiners and evaluation under pullback. The coefficient field
`ℂ` satisfies the source's field restriction on stable images.

The registered source is `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The original page images were checked for the opposite-radical overbars.
No separate source errata file was found in the inspected notes or source
folder.

Applying this conditional result to the exact rational-point duality target
still requires actual proofs of a common fixed-element opposite Iwahori
contraction basis and full opposite-Haar reciprocity in the canonical
topology, together with the closedness, centrality and normalizer inputs.
This module supplies neither those rational structural results nor the
complete `RationalNaturalJacquetDualityStatement`.
