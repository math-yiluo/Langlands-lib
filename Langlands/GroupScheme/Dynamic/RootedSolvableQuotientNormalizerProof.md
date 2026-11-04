# Nonfixed quotient lifts and nonidentity normalizers

This internal prerequisite constructs actual rational quotient lifts and
normalizer points over algebraically closed fields `k : Type u` of every
characteristic. It uses the proved normal-solvable centrality theorem, so none
of its declarations takes `AlgClosedReductiveNormalSolvableTorusStatement` as
an input. Actual quotient geometry and internal torus conjugacy remain
explicit where required. It does not prove positive-root uniqueness.

## Centrality from fixed quotient sections

Let `G` be pseudo-reductive, `i : H → G` have smooth connected affine source,
and `j : P → G` be a closed solvable subgroup. No normality or closedness of
`i` is assumed. Let `q : G → Q` be flat, surjective and quasi-compact. The
fiber law identifies equality of quotient images on every relative scheme
with membership of `g⁻¹h` in the actual range of `j`.

`Dynamic.isCentral_of_all_quotientLifts_fixed` assumes every rational lifted
quotient section `g ≫ q` is fixed, on every scheme test and restriction, under
the action of `H`. For every rational pair `(g,t)` of `G × H`, fixedness of the
quotient image of `g⁻¹` and the fiber law put `g i(t) g⁻¹` in `P`. The product
is smooth, reduced and locally of finite type. The published
`UnipotentAllBorelsEnvelope.exists_factor_of_algClosed_points` result then
factors the actual conjugation morphism through `P`.

The smooth connected normal closure `D` of the image of `i` consequently
factors through `P` by its minimality. The factor is closed because its
composite is the closed inclusion of `D` into `G`, so it is monic and `D` is
solvable. The same closed inclusion makes `D` affine. Its existing smoothness,
connectedness and normality now permit application of
`IsSolvableGroupScheme.isCentral_of_normal_of_isPseudoReductive`. Containment
of the image of `i` in this central normal closure gives full `IsCentral i`.
This establishes scheme-theoretic centrality, including after restrictions to
nonreduced or nonaffine test schemes.

`Dynamic.nonfixedQuotientLiftOfNoncentralSubgroup` takes `¬ IsCentral i` and
selects an actual rational `g` whose quotient section is not fixed, by the
contrapositive of this result. The lift construction requires no properness,
separatedness, torus conjugacy, centralizer containment, or Weyl finiteness.

## Root and normalizer constructions

`Dynamic.nonfixedQuotientLiftOfRelativeRoot` takes a split torus
`i : T → G` with an actual relative root. The published
`not_isCentral_of_relativeRoot` makes `i` noncentral. Geometry of the split
torus supplies the smooth connected affine acting source, so the preceding
construction gives the actual rational nonfixed lift for the same flat exact
solvable quotient. No maximality of `T` or factor through `P` is required
here. The ambient group is affine and pseudo-reductive.

`nonidentityNormalizerOfNoncentralSolvableQuotient` assumes a noncentral
maximal torus, a closed solvable stabilizer `P`, an actual factor
`f : T → P` with `f ≫ j = i`, and `MaximalToriAreConjugate P`. The exact
quotient `q` is smooth, surjective and quasi-compact, and `Q` is proper over
`k`. It constructs the nonfixed rational quotient lift using normal-solvable
centrality, then applies
`nonidentityNormalizerOfNonfixedSmoothProperQuotient`. The result is an actual
rational normalizer point whose class in `relativeWeylGroup i` is not one.
The maximal torus supplies the smooth connected affine source needed for the
lift construction.

`nonidentityNormalizerOfRootedSolvableQuotient` replaces noncentrality by a
split-torus hypothesis and an actual relative root, then applies the preceding
normalizer construction. Neither normalizer constructor needs supplied
representation data, a line-stabilizer realization, a moving point, a nonfixed
section, whole-torus centralizer containment, or Weyl finiteness.

## Provenance and remaining scope

This is internal derivation from existing actual constructions. The
normal-closure proof refines the route in
`Dynamic.NoncentralSolvableQuotientSection` by applying proved normal-solvable
centrality. The root and normalizer compositions refine
`Dynamic.RootedSolvableQuotientNormalizer` in the same way. The final smooth
proper quotient-to-normalizer step is imported from the published geometric
quotient construction. No claim is made here to construct the required
quotient, prove its properness, prove internal conjugacy of maximal tori in
`P`, bound its dimension, or prove the unconditional rank-one uniqueness
statement.
