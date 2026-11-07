# Native Jacquet fixed-module finiteness from the remaining structural targets

This internal reduction constructs actual finite ordered intersection geometry and proves

```lean
RepresentedParabolicDoubleCosetStatement.{u} ->
  ArbitraryParabolicQuotientCompactStatement.{u} ->
    RationalSupercuspidalJacquetFamilyFiniteStatement.{u, uV}
```

The two structural assertions remain hypotheses. This is a proved conditional reduction to the unchanged published native Jacquet finiteness statement, not a proof of that statement without premises. No representation admissibility, fixed-module finiteness or representation-filtration conclusion is assumed. The complete rational-norm algebra, full universal induced carrier, normalized native coefficient quotient, literal dynamic output Levi, field/group universe `u` and independent inducing-carrier universe `uV` are retained.

## Finite adapted representatives with the required ordering

`RepresentedParabolic.exists_orderedIntersectionDataOfKnownCocharacters` takes two original parabolic/Levi/radical triples, with their original structural and multiplication witnesses, known cocharacters realizing those triples on every relative test scheme, and `RepresentedParabolicDoubleCosetStatement`. The ambient rational-point group is locally compact, nonarchimedean, Hausdorff and sigma compact in its canonical topology; the field is Hausdorff. Connected reductivity is explicit.

The structural hypothesis supplies finiteness of the actual double-coset quotient and a torus-adapted representative in each double coset. The published `Geometric.closedSubgroupOrbitOrdering` first supplies an ordering of the actual double-coset orbits with open initial unions. For each inverse ordered representative, the structural hypothesis supplies a rational point `z` in that same double coset and a maximal split torus factoring through both original Levis, with the target factor conjugated by `z`.

`geometricLemmaIntersectionDatumOfKnownCocharacters` constructs the actual intersection datum at each chosen `z`. The proof then uses `OrderedDoubleCosets.replaceRepresentatives` to replace the ordered representative by `z` inverse. The defining equality of double cosets proves that the orbit itself, its position in the ordering and every initial union are unchanged. Double inversion identifies the new inverse representative with the parameter `z` of the actual datum. Finally `dynamicRealizationOfKnownCocharacters` gives each datum its simultaneous realization in its own fixed common torus. Thus the result constructs the ordered geometry needed by the native support proof, rather than merely listing abstract intersection groups or supplying a representation filtration.

## Native geometry from the two structural assertions

`RationalNormalized.nativeJacquetFiniteOrbitGeometryOfStructural` takes the original compatible root presentation, any supplied geometric radical, a connected-reductive ambient group, a represented output triple already realized by one specified cocharacter, and the two global structural assertions. It returns an actual `NativeJacquetFiniteOrbitGeometry` for these original maps.

The source presentation supplies its split-component cocharacter. The published parabolic and Levi equalities for that cocharacter, together with `range_comp_radical_eq` for the supplied radical, give the three original source identities. The output triple identities are explicit. Therefore the preceding ordered-geometry result applies without the universal `ParabolicDynamicStatement`.

Hausdorffness of the original rational-point group is derived from the affine scheme over the local field. Connected-reductive rational points are second countable; together with the given local compactness this gives sigma compactness. These facts discharge the ordering theorem's topological hypotheses.

For each constructed datum, its original target-intersection map `D.q'` is an actual parabolic of the original target Levi scheme `L`. The latter is connected reductive by its original rational-Levi witness. With `leviPointTopology lQ hlQ`, local compactness and the nonarchimedean group structure are transferred from the original ambient point group by the published Levi-point homeomorphism. `ArbitraryParabolicQuotientCompactStatement`, instantiated at `L` and `D.q'`, then supplies precisely the compactness field of the native geometry record, in that original Levi topology. This step uses a global compactness assertion as a premise; the present module does not prove it.

## Conditional proof of the unchanged global statement

`Plancherel.rationalSupercuspidalJacquetFamilyFinite_of_structural` introduces exactly the binders of the published global statement. It retains the original source point semidirect decomposition, radical closedness, continuous projection, compact inducing quotient and the complex inducing representation. Source admissibility and actual supercuspidality are used by the native orbit theorem. The separate original smoothness and irreducibility premises are retained, although this conditional argument does not need them beyond the stronger supplied admissibility and supercuspidality inputs.

For an arbitrary output cocharacter, the published `Dynamic.affineDecompositionModel` supplies actual affine parabolic, centralizer and unipotent schemes with their original compatible inclusion maps and multiplication isomorphism. Published theorems prove parabolicity of this dynamic parabolic, connected reductivity of its centralizer, and the full geometric-radical predicate. The proved field-extension comparison gives the rational-Levi interface's radical predicate, and these data give the original output Levi its rational-Levi witness. All three ambient range identities are the model's representation identities; none is assumed for this arbitrary output in the final reduction.

The native-geometry constructor now supplies finite ordered actual data, simultaneous realizations and original target quotient compactness from the two structural premises. `outputJacquet_fixedModule_finite_of_geometry` applies to those constructed data. Its conclusion is exactly the target's

```lean
Module.Finite (RationalNormalized.RegularAlgebra r)
  (fixedVectors
    (RationalNormalized.outputJacquetRepresentation r h hU sigma chi)
    J.toSubgroup)
```

The existing normalization characters and coefficient structures are unchanged. The input compactness of the source quotient is exactly the one in the global target. The final extraction works for every open output subgroup, so it also works for every compact open subgroup requested by that target; the target's compactness premise on `J` remains present.

## Provenance and open obligations

The provenance is internal composition of the actual known-cocharacter intersection constructions, the proved finite closed-subgroup orbit ordering and representative replacement, the actual native geometry/fixed-module adapter, and the proved dynamic group-scheme models. The two remaining universal assertions are independent geometric obligations:

| Hypothesis | Content used here |
| --- | --- |
| `GroupScheme.RepresentedParabolicDoubleCosetStatement` | Finiteness of literal parabolic double cosets and existence of representatives with a maximal split torus factoring through the two original Levis. |
| `RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement` | Compactness of the original target-intersection parabolic quotient inside every actual connected-reductive output Levi over a nonarchimedean local field. |

Neither assertion is proved by this module. In particular, the proof does not treat a structural statement declaration as a theorem, infer finite actual geometry from an abstract finite representation filtration, or infer coefficient Jacquet admissibility from complex Jacquet admissibility. Proving both structural hypotheses and then applying this reduction is still required to establish the global finiteness statement without additional premises.
