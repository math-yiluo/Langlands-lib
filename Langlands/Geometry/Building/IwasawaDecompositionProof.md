# Proof of the chamber Iwasawa decomposition

This unit proves the published target
`Langlands.Geometry.Building.IwasawaDecompositionStatement` of
`Langlands/Geometry/Building/IwahoriWeylStatement.lean`. The theorem
`Langlands.Geometry.Building.iwasawaDecomposition` is stated at an arbitrary universe `u`.
Its type is exactly `IwasawaDecompositionStatement.{u}`, so no hypothesis is changed or added.

## What is proved

The target is Kaletha–Prasad Theorem 5.3.3. It quantifies over every nonarchimedean local
field `F` and every affine group scheme `G` over `F`. For every
`P : ParahoricBuildingData G` it assumes that `𝒪[F]` is Henselian, that the residue field
`𝓀[F]` is perfect, and that
`P.apartment.SatisfiesApartmentAxioms P.centralizer` holds. Then, for every chamber `C` of
`P.affineRoots` and every generic cocharacter `ν` of `P.S`, it gives
`P.IwasawaDecomposition C ν`. Every `g ∈ G(F)` is a product `u * n * p`, where
`u ∈ standardUnipotentPoints P.i ν ∅`, `n` is an actual point of the normalizer of `P.S`, and
`p ∈ P.parahoric C`.

## The implemented proof

The proof is one application of the published conditional theorem
`iwasawaDecompositionStatement_of_structuralStatements`, from
`Langlands/Geometry/Building/IwasawaDecompositionReduction.lean`. Each of its seven premises
is a published Library theorem with no hypotheses:

| Premise | Library proof |
| --- | --- |
| `RelativeWeylCoxeterStatement` | `Langlands.GroupScheme.relativeWeylCoxeter` |
| `StandardParabolicEndpointsStatement` | `Langlands.GroupScheme.standardParabolicEndpoints` |
| `RationalBruhatStatement` | `Langlands.GroupScheme.rationalBruhat` |
| `RootRankOneFactorizationStatement` | `Langlands.GroupScheme.rootRankOneFactorization` |
| `RelativeRootSystemStatement` | `Langlands.GroupScheme.relativeRootSystem` |
| `RelativeRoot.DynamicRootOrderedProductStatement` | `Langlands.GroupScheme.RelativeRoot.dynamicRootOrderedProduct` |
| `RelativeRoot.RootSubgroupVectorStatement` | `Langlands.GroupScheme.RelativeRoot.rootSubgroupVector` |

The conditional theorem first builds the relative Tits system
`(G(F), P_∅(F), N(F), S)` from the structural statements, using
`relativeTitsSystemStatement_of_structuralStatements`. It then shows that
`X = P(ν)(F) N(F) P_C` contains `1` and is stable under left multiplication by the Borel
subgroup and by the representatives of the simple reflections, so `X = G(F)`. Stability under
a simple reflection uses KP Lemma 5.3.1 at a chamber. Finally the dynamic limit writes each
point of `P(ν)(F)` as a point of the dynamic unipotent times a point of `Z(F) ⊆ N(F)`.
The Markdown of `IwasawaDecompositionReduction` describes each step.

The literal unipotent factor of the target is `standardUnipotentPoints P.i ν ∅`, not the
dynamic unipotent. The conditional theorem compares the two with the proved Library theorem
`standardUnipotent_empty_eq_dynamic`, which holds for the actual connected reductive group and
maximal split torus of `P`. The parabolic `P_∅(F)` is matched with the dynamic parabolic by
the proved `standardParabolic_empty_eq_dynamic_of_generic`, which uses genericity of `ν`. No
definitional equality between standard and dynamic subgroups is assumed.

The target retains the Henselian and perfect-residue-field hypotheses unchanged. This proof
route does not use them, because the Tits-system argument works with the actual rational
points and the fixed-apartment axioms alone. The proof adds no Iwasawa, Iwahori factorization,
normalizer-coset, building-validity or algebraic-comparison premise.

## Provenance

The statement is KP Theorem 5.3.3 (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
§5.3, book PDF pp. 220–221, printed pp. 189–190). KP Lemma 5.3.1 is on PDF p. 219. The
authors' corrections of 1 November 2024 (PDF p. 30) rewrite the open-cell step of KP's proof
on printed p. 190. The implemented route is different: it is the Tits-system argument of the
published reduction, with the relative Tits system of Borel–Tits 5.15–5.16 obtained from the
proved structural statements above. KP's open-cell step, and thus that correction, is not used.

This unit proves only the chamber decomposition `G(F) = U(F) N(F) P_C` for the minimal
parabolic of a generic cocharacter. It is conditional on actual `ParahoricBuildingData`
satisfying the fixed-apartment axioms. It does not construct such data, and it does not prove
the special-`K_0` Iwasawa decomposition or the replaced Lemma 5.3.5.
