# Renard VI.2.1: cuspidality implies compact restriction to the norm kernel

`Langlands.Aubert.General.rationalCuspidalCompactRestriction.{u,v}` proves the
exact published
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalCompactRestrictionStatement.{u,v}`.
The field and representation carrier universes are independent. The statement,
its hypotheses and its imported files are unchanged. The action is that of the
actual rational-point group, with `rationalPointTopology F G.X`, and restriction
is to the actual `Plancherel.rationalCommonNormKernel G` with its subgroup
topology. Every smooth functional of the restricted dual is covered.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 edition, VI.2.1, printed pp.137–139 / PDF pp.143–145. The source ID is
`renard-2026-representations-groupes-reductifs-padiques`, content SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implemented route bounds support directly inside the norm kernel.

## Implemented proof

For each proper subset of the actual simple roots, cuspidality makes the
normalized Jacquet quotient subsingleton. Its actual carrier is the quotient by
the trivial-character relation span, so every vector belongs to that span.
Span induction constructs a finite set of actual radical elements sufficient
to kill a translated coefficient once their conjugates fix its functional.

The literal uniformizer translates `e(x) f`, for a finite subset of the actual
torus centralizer, form a lattice model with lower pairing bound zero. Existing
actual contraction applies to integral directions annihilating the selected
wall. Finite representatives for bounded wall pairings and shifts along a
standard cocharacter reduce the required wall contraction to that result. The
finite-root gap argument then proves that every nonzero coefficient on this
cone has all simple-root pairings bounded above. Finiteness of compact orbits
on a smooth vector and on a smooth dual vector makes the bound uniform over
both translates in the compact subgroup supplied by the target.

The actual relative roots and the restrictions of actual rational characters
span the rationalized full character lattice. Equality of simple-root pairings
gives equality on the relative-root span; equality of the ambient valuation of
uniformizer powers gives equality on all restricted group characters. Spanning
and the integral perfect pairing distinguish the lattice parameters. Thus a
bounded integral box with fixed ambient valuation contains finitely many
parameters.

The given finite Cartan cover writes every point as `k₁ f e(x) k₂`. A compact
subgroup lies in the norm kernel, so for a point in that kernel the ambient
valuation of `e(x)` is forced by the finite factor `f`. Only finitely many
middle factors can contribute. Compactness of their products with the two
compact subgroup factors, and closedness of the norm kernel, give compact
support in the subgroup topology. Finally, openness of the actual norm kernel
identifies its full smooth dual with the ambient smooth dual and supplies the
functional needed by the bound.

The internal assembly lemma
`compactSmoothDualCoefficients_normKernel_of_jointDetection` takes joint
detection as an intermediate hypothesis. The final theorem discharges it with
`rationalCartanJointDetection`; it adds no premise to the published target.

## Structural and local-point inputs

The following module names are under `Langlands.`. Their named declarations are
proved or constructed Library interfaces used in the argument. The new helper
modules are included with this proof and documented by their paired Markdown.

| Module | Declarations and use |
| --- | --- |
| `Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement` | The immutable target and `RationalPointFamily.FiniteCartanCovering`, used exactly as published. |
| `Representation.Aubert.General.RationalParabolicDecomposition` | `RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement` supplies the actual family in the target. |
| `Representation.Aubert.General.RationalEndpoint` | `RationalPointFamily.levi_univ_eq_top` identifies the full Levi with the rational-point group. |
| `Representation.Aubert.General.RationalPointFamily` | `centralizerPoints_le_levi`, `rootSet_subset`, and `val_mem_rootSet` identify the literal centralizer factors and root indices. |
| `GroupScheme.Rational.RootFiniteness` | `HasRelativeRootSystem.finite_simpleRelativeRoots` and `simpleRelativeRootFintype` give the finite actual index set. |
| `Representation.Jacquet.Localization` | `mk_eq_zero` and `relations_one` convert vanishing of the normalized quotient carrier to the genuine untwisted relations. |
| `Representation.Jacquet.Coinvariants` | `relations` and `relations_eq_span` supply the actual quotient kernel and its generators. |
| `Representation.Aubert.General.RationalCartanLatticeModel` | `uniformizerPowers`, `simpleRootPairing`, `uniformizerPowers_mem_levi`, `commute_uniformizerPowers`, and `uniformizerPowers_conj_mem` supply actual torus elements, integer pairings, centrality and contraction. |
| `BruhatTits.SpecialCompact.StandardBasisProperty` | `SimultaneousStandardBasisAt` is the target's hypothesis supplying the compatible standard split components and common compact-open basis used by contraction. |
| `GroupScheme.Rational.StandardLeviLieWeights` | `isCentral_standardLeviTorusFactor_of_annihilates`, used in the actual contraction proof, identifies annihilating directions as central in the actual Levi. |
| `GroupScheme.Rational.SplitComponentCocharacters` | `IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters`, used inside the published contraction proof, factors the same integral annihilating direction through the compatible component. |
| `Representation.Aubert.General.CartanLatticeContraction` | `exists_finite_pairing_reps` and `IsCartanLatticeModel.eventually_wall_contraction` provide the finite wall translates and eventual contraction. |
| `Representation.Smooth.Admissibility.JacquetCartan` | `JacquetCartanDatum.finite_image_of_isCompact` gives finite compact orbits. Only this orbit lemma is used; its admissibility theorem is not invoked. |
| `Representation.Smooth.SmoothPart.BasicProof` | `isSmooth_smoothPart` and `isSmoothVector_apply`, with `smoothInclusion`, apply the orbit lemma to the entire smooth dual. |
| `Representation.MatrixCoefficient.LawsProof` | `matrixCoefficient` and `matrixCoefficient_apply` fix the actual evaluation and translation convention. |
| `GroupScheme.Rational.RelativeSimpleRootBasis` | `ratSpan_simpleRelativeRoots_eq_relativeRootSpan` generates the actual relative-root span; `HasRelativeRootSystem.neg_mem_relativeRoots` supplies negation stability. |
| `GroupScheme.Rational.RelativeRootsCharacterSpan` | `relativeRootsRestrictedCharactersSpan`, equivalently `IsConnectedReductive.relativeRootSpan_sup_restrictionRange_eq_top`, supplies joint spanning on the full character space. |
| `GroupScheme.Rational.RelativeReflectionPairing` | `rationalCocharacterEvaluation` and `rationalCocharacterEvaluation_toRat` turn equality of pairings into equality of linear functionals. |
| `Geometry.Building.CocharacterUniformizerProof` | `CocharacterUniformizer.latticePairing_isPerfPair` separates integral cocharacters of the actual split torus. |
| `Geometry.Building.CocharacterUniformizerEvaluation` | `CocharacterUniformizer.rationalCharacterValuation_latticeSection` gives the actual ambient-character evaluation formula, and `CocharacterUniformizer.characterNorm_latticeSection` turns the weak cone inequalities into nonnegative pairings. |
| `Geometry.Building.CocharacterUniformizer` | `CocharacterUniformizer.CAplus` and its actual `latticeSection` supply the literal integral parameters in the cover. |
| `Representation.Plancherel.RationalCharacterValuation` | `rationalCharacterValuation`, its character-restriction law and `rationalCharacterValuation_ker` give the fixed ambient valuation fiber and its actual kernel. |
| `Representation.Plancherel.RationalCharacterTopology` | `compactSubgroup_le_rationalCommonNormKernel` and `isClosed_rationalCommonNormKernel` give the compact-subgroup containment and closed kernel used in support compactness. |
| `Representation.Plancherel.RationalNormKernelSmoothDual` | `isSmoothVector_dual_rationalNormKernel_iff` transfers every smooth functional of the restricted dual to the ambient dual. |
| `BruhatTits.SpecialCompact.Properties` | The target's `SpecialCompactProperties` contains `IsCompactOpenMaximal`; its compactness clause is used for the same geometric subgroup. |
| `Geometry.Building.SpecialCompact` | `KPApartmentData.specialCompactSubgroup` is the unchanged geometric subgroup in the target. |

The new internal modules are `CuspidalCoefficientVanishing`,
`CuspidalCartanPairingBound`, `RationalCuspidalCartanBound`,
`CartanSupportReduction`, `RationalCartanSupportReduction`, and
`RationalCartanJointDetection`, all under
`Langlands.Representation.Aubert.General`. Together they implement the finite
relation witnesses, the uniform pairing bound, the fixed-fiber compactness
argument and the actual joint-detection proof described above.

No step assumes admissibility, irreducibility, finite dimension, a nonzero
representation, a nonempty root set or positive relative rank. In relative rank
zero the root box has no coordinates and joint detection uses restricted
characters. All field arguments use the target's nonarchimedean local-field
instances and therefore retain mixed and equal characteristic, split and
nonsplit groups, and non-quasi-split groups.
