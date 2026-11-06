# Coherent normalized Jacquet duality from opposite Iwahori contractions

Author: Worker 1004. Worker 127 contributed the structural interface and the
full-modulus reciprocity formulation. Worker 937 generalized the duality family
from admissible objects to arbitrary object classes satisfying the stable-pairing
hypotheses and added the two functor-level isomorphism theorems described in
the section *Beyond admissible objects*.

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
(Since Worker 937's generalization this step sits in the admissible corollary;
the general theorem receives these conditions as a hypothesis.)
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

## Beyond admissible objects

`exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_admits` has
the same structural and inverse-half reciprocity hypotheses, an arbitrary
predicate `S` on `SmoothRep ℂ G`, and a hypothesis `hAdm` that every `A` with
`S A` satisfies
`(Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc hBasis).Admits
A.representation A.isSmooth`. It constructs a family `E A hA` for `hA : S A` with
the same naturality equation for every actual morphism between members of `S`.
Its proof is the argument above with admissibility replaced by `hAdm`, which was
the only use of admissibility. The admissible theorem
`exists_naturalNormalizedJacquetDuality_of_iwahoriContractions` is now the case
`S = SmoothRep.IsAdmissible`, with `hAdm` given by
`admits_of_iwahoriContractions`; its statement is unchanged.

`nonempty_contragredient_normalizedJacquet_iso_of_admits` assumes `Admits` for
every smooth complex representation (carrier universe `uV`) and concludes

`Nonempty (SmoothRep.contragredientFunctor ⋙ rU ≅ rO.op ⋙
SmoothRep.contragredientFunctor)`,

a natural isomorphism of functors on `(SmoothRep ℂ G)ᵒᵖ`. It applies the
previous theorem with the predicate that is always true and assembles the
components with `NatIso.ofComponents`; the naturality square for an opposite
morphism `f` is the bundled equation for `f.unop`.

`nonempty_contragredient_normalizedJacquet_iso_of_splits` derives the same
conclusion from Fitting splittings instead of `Admits`: `hUpperSplit` asks
`Jacquet.CompactCompressionSplits A.representation A.isSmooth K hK g` for every
smooth `A` and every compact open `K` with `IsIwahoriContraction K U M O g`, and
`hLowerSplit` asks the same for `g⁻¹` when `IsIwahoriContraction K O M U g⁻¹`.
It applies `StablePairingData.admits_of_iwahoriContractions_of_splits` to each
object, using `hUpperSplit` on the bundled smooth contragredient
`A.contragredient` and `hLowerSplit` on `A`. No finite-dimensionality or
admissibility premise appears. In Renard 2026, VI.9.1, the Proposition gives
such splittings for every smooth representation (via Appendix C.II); that
proposition is not proved here and both splitting families remain hypotheses.

The noncomputable definition `contragredientNormalizedJacquetIsoOfSplits` has
exactly the hypotheses of `nonempty_contragredient_normalizedJacquet_iso_of_splits`
and returns the natural isomorphism

`SmoothRep.contragredientFunctor ⋙ rU ≅ rO.op ⋙ SmoothRep.contragredientFunctor`

itself, chosen with `Classical.choice` from that theorem. It is the
functor-level form of Renard 2026, VI.9.6, (VI.9.6.2), `r_{P̄}(Ṽ) ≃ (r_P V)~`, for
the abstract pair `U`, `O` with the displayed structural, reciprocity and
splitting hypotheses. Renard derives (VI.9.6.2) from second adjointness and
the Casselman pairing; here it is derived from the stable pairing directly.
The provenance is derived. The definition proves no splitting, reciprocity or
contraction-basis result for rational points of a reductive group.

## Full-modulus corollary

For the full-modulus corollary, the composition of the positive square-root
homomorphism on units and the complex embedding is a monoid homomorphism
`F : ℝ≥0ˣ →* ℂˣ`. The actual inverse-half characters are the inverses of
`F` applied to the respective full Haar characters. Multiplicativity of `F`
and the given full-character product identity imply the required
inverse-half scalar product identity.

The substantial transitive proof dependencies of the admissible theorem are
`powerKernelSup_isCompl_stableImage` (the Fitting splitting of finite-dimensional
fixed spaces), the splitting consequences
`compactCompression_stableEvaluationDuality_of_splits` and
`stableImageJacquetMap_bijective_of_splits` of `Jacquet.CompressionSplittingDuality`,
`powerKernelSup_eq_ker_of_iwahoriContraction`,
`isAdmissible_smoothContragredient_of_compact_cofinal`, and the stable-pairing
existence, equivalence and naturality results just named. (Before Worker 937's
change, the route used `stableImageJacquetMap_bijective_of_iwahoriContraction`
and `compactCompression_stableEvaluationDuality` instead of the two splitting
consequences.) They work for the abstract group and its given compact open
subgroups. The finite-dimensional fixed spaces come from admissibility. The proof also uses the actual
coinvariant, localization, Haar-character, character-twist and bundled smooth
contragredient definitions.

A recursive inspection of the constructor's type and body, including the
types and values of project constants they reference, reached 454 project
declarations in 44 modules before Worker 937's generalization; the added
dependencies are the elementary linear-algebra module
`Jacquet.CompressionSplittingDuality` and its imports. None is a classification, character-independence,
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
for block permutations. None of these declarations is used by the
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

Applying these conditional results to the exact rational-point duality targets
still requires actual proofs of a common fixed-element opposite Iwahori
contraction basis and full opposite-Haar reciprocity in the canonical
topology, together with the closedness, centrality and normalizer inputs.
This module supplies neither those rational structural results nor the
complete `RationalNaturalJacquetDualityStatement`.
