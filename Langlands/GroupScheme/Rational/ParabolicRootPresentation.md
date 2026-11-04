# Compatible root presentations of specified rational parabolics

Author: Worker 6.

Interface feedback: Workers 1107 and 1220 clarified reuse and the retained
actual-object, root-convention and presentation-independence obligations.

This is a derived construction on the shared `Langlands.GroupScheme` objects.
It records actual choices and their correctness for specified maps
`p : P ⟶ G`, `l : M ⟶ P` and `a : A.toGrp ⟶ M`, and attaches the existing
restricted roots and root-combination cones to those choices. The module
contains the construction and short intrinsic laws.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are V.3.9 and V.3.12–V.3.15, printed pp.112–113,
PDF pp.118–119. VII.2.1, printed p.227, PDF p.233, is the later consumer.

V.3.14 chooses a minimal parabolic contained in a specified parabolic `P = MN`
whose split component contains the specified `A_M`. It then restricts the
simple roots outside the Levi index to `A_M`. V.3.15 forms sums over those
restricted vectors with strictly positive or nonnegative coefficients.
The data and correctness packaging here is implementation content organizing
these choices on actual group schemes. It proves no general structural
existence or conjugacy theorem.

Everything is over an arbitrary field `k : Type u`, with all schemes in the
same geometric universe. `G` has affine structure morphism. There is no
characteristic, perfectness, splitness of `G`, positive rank or `GL_n`
restriction. The wrappers for the finite cones additionally require
`[LocallyOfFiniteType G.X.hom]`. No representation or representation-carrier
universe enters this construction.

## Data and actual compatibility

`ParabolicRootPresentationData A G` consists of an actual commutative group
scheme `T`, a group-scheme morphism `i : T.toGrp ⟶ G`, a cocharacter `ν`,
a character set `J`, and a commutative group-scheme morphism `f : A ⟶ T`.
Underlying data carries no correctness assertions.

The Prop-valued `ParabolicRootPresentationData.IsCompatible d p l a`
requires:

- `IsParabolicSubgroup p`, `IsRationalLeviSubgroup l` and `IsSplitComponent a`
  for the actual specified maps;
- `IsMaximalSplitTorus i`, `IsGenericCocharacter i ν` and
  `J ⊆ simpleRelativeRoots i ν`;
- the equalities of subgroup functors
  `range p = standardParabolic i ν J` and
  `range (l ≫ p) = standardLevi i ν J`, tested on every scheme over `Spec k`;
- the actual factorization `groupHom f ≫ i = a ≫ l ≫ p`;
- minimality of `Dynamic.parabolic (groupHom ν ≫ i)` as an actual parabolic
  functor, and its inclusion in `range p`;
- a cocharacter `ζ` satisfying `IsStandardCocharacter i ν J ζ` and realizing
  both `range p` as its dynamic parabolic and `range (l ≫ p)` as its dynamic
  centralizer.

The last field supplies an actual witness to the standard intersection index.
An empty intersection cannot by itself yield compatible data.
Minimality refers to the dynamic parabolic of the same generic `ν`.
The construction does not identify it with `standardParabolic i ν ∅`;
that endpoint identification is a separate structural comparison.
`exists_minimalParabolic` unpacks the published minimal-functor equivalence to
give an actual minimal subgroup representative with this range and containment.
`exists_standardCocharacter` extracts the standard-cocharacter witness.
The two all-test membership laws rewrite the supplied ranges to the published
standard-intersection membership formulas.

`ParabolicRootPresentation p l a` packages data with this correctness predicate.
The construction does not assert that this type is inhabited for arbitrary
supplied maps.

## Restricted roots and cones

For verified data `r`, `r.restrictedRoots` is the published
`restrictedSimpleRoots i ν J f`. Its membership formula is
`∃ α ∈ simpleRelativeRoots i ν, α ∉ J ∧ 1 ⊗ (f ≫ α) = x`.
`restrictedRoots_eq_empty_iff` says that it is empty exactly when `J`
contains all simple roots.

Under the locally finite type hypothesis, `finite_simpleRoots` applies the
published `IsSplitTorus.finite_simpleRelativeRoots` to the split torus supplied
by maximal splitness. `finite_restrictedRoots` takes the image of the finite
set difference. Thus no extra finiteness or root-system proposition is assumed.
`positiveCone` and `nonnegCone` are exactly the existing
`restrictedRootPositiveCone` and `restrictedRootNonnegCone` with this derived
finiteness witness.

The two membership laws express enumeration-free finite sums over the distinct
restricted vectors, with respectively strictly positive and nonnegative real
coefficients. The empty complementary-root case gives `{0}` for both cones.
The positive cone is contained in the nonnegative cone; the latter contains
zero and is closed under addition and nonnegative scalar multiplication.
The former is closed under addition and strictly positive scalar multiplication.
These laws instantiate the published cone API.

The ambient space remains the full
`RealTorusSpace.Vstar A = ℝ ⊗[ℤ] characterLattice A`, including its central
directions. These are root-span cones. In particular the empty cone index
gives `{0}` in that full space. No coroot-pairing chamber is substituted, and
no quotient by the central directions is taken.

## Factorization and compatible component isomorphisms

`factor_unique` applies the published `eq_of_groupHom_comp_eq` with
`j := l ≫ p`. The torus monomorphism follows from maximal splitness.
It proves uniqueness of the factor `f` for this fixed inclusion.

The positive and nonnegative `image_…_splitComponentIso` laws instantiate the
existing corresponding two-direction pullback theorems. Their inputs are an
actual torus isomorphism `e : A ≅ A'`, the compatibility
`groupHom e.hom ≫ a' = a`, and a factor `f' : A' ⟶ T` with
`groupHom f' ≫ i = a' ≫ l ≫ p`. The cones correspond under real character
pullback along `e.hom` and `e.inv`. They keep `T`, `i`, `ν` and `J` fixed;
they make no comparison between unrelated choices of root presentation.
No split-component existence assertion is used to obtain this transport.

## Retained structural and source comparisons

Existence of a compatible presentation for every specified actual `p,l,a`,
independence across maximal split tori, generic cocharacters and minimal
parabolics, and the comparison of the derived `simpleRelativeRoots` with
Renard's simple indivisible roots of the chosen minimal parabolic remain
separate exact Chapter V statement/proof obligations.
The minimality field and standard-cocharacter realization do not prove that
root-convention comparison. They also do not assert the real-cocharacter
root-annihilator image equality in `StandardLeviSplitCentralDirectionsStatement`.

The published `StandardCocharacterStatement`,
`GenericMinimalParabolicStatement`, standard classification and standard-Levi
central-direction statements are possible structural inputs or proof targets,
not automatically available proofs of these remaining assertions.
The eventual all-parabolic definition of VII.2.1 must retain actual coverage
and these comparisons. A universal condition over possibly absent
presentations alone cannot establish the source definition. This unit defines
no temperedness predicate, admissibility condition, induction theorem or
representation-theoretic equivalence.
