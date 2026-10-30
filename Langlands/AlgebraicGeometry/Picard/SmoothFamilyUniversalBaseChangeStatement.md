# Base change of the actual universal smooth-family property

`SmoothFamilyUniversalBaseChangeStatement` is a `Prop`-valued definition in
universe `u`. It states the following. Let `b : S' → S` be any morphism of
schemes, `A/S` an abelian scheme, `P/S` a parameter scheme and `L` an actual
rigidified family on `P ×_S A`. Suppose `L` satisfies
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`. Then the family
`(baseChangeFamily b A P).obj L` satisfies
`IsUniversalSmoothFamilyOnQuasiSeparatedTests` for the base-changed abelian
scheme `(baseChange b).obj A` over `S'`.

The new parameter scheme is exactly `(Over.pullback b).obj P`, the actual
fibre product `P_{S'} = P ×_S S'` over `S'`. The new family is the existing
explicit composite `baseChangeFamily b A P` from `PoincareBaseChange`. That
functor first pulls `L` back along the parameter projection `P_{S'} → P` and
then changes the ground base with `familyBaseChange`. Its underlying line
bundle is identified with the pullback along
`baseChangeFamilySpaceMap b A P : P_{S'} ×_{S'} A_{S'} → P ×_S A` by
`baseChangeFamilyForgetIso`.

All schemes lie in the same universe. The morphism `b` is arbitrary. There is
no quasi-separatedness hypothesis on `S`, `S'` or `P`. There is also no
open-immersion, flatness, finiteness, reducedness or noetherian assumption.
The statement does not assert that a representer exists. It only transports
a given universal property along base change.

## Meaning of the two occurrences of the predicate

Both occurrences of `IsUniversalSmoothFamilyOnQuasiSeparatedTests` have their
existing meaning from `SmoothFamilyQuasiSeparatedRepresentabilityStatement`.
For an abelian scheme `B` over a base `R` and a family `M` with parameter
`Q/R`, the predicate is the conjunction of two conditions.

- `IsAlgebraicallyTrivialFamilyViaSmoothFamily B M` is a condition on the
  global family itself. The underlying bundle of `M` is moved from `Q ×_R B`
  to `B ×_R Q` with `familyLineBundle`. For every algebraically closed field
  `K : Type u` and every map `Spec K → Q`, the bundle on that geometric fibre
  must satisfy `IsAlgebraicallyTrivialViaSmoothFamily`. That predicate asks
  for an actual smooth, separated, finite-type, geometrically integral
  parameter `C` over `K`, two rational points `c0` and `c1` of `C`, and an
  actual line bundle on `C ×_K B_K`. The bundle must restrict to the trivial
  bundle at `c0` and to the fibre bundle at `c1`, up to line-bundle
  isomorphism.
- The second condition is about quasi-separated tests. Let `T/R` be a test
  whose underlying scheme is quasi-separated, nonreduced tests included. Let
  `q` be a rigidified class over `T` that satisfies the same smooth-family
  condition. Then there is exactly one slice morphism `h : T → Q` such that
  `RigidifiedLineBundle.classifyingMap` sends `h` to `q`, that is, the actual
  pullback of `M` along `h` represents `q`.

In the hypothesis this predicate is applied with `R = S`, `B = A`, `Q = P`
and `M = L`. In the conclusion it is applied with `R = S'`,
`B = (baseChange b).obj A`, `Q = (Over.pullback b).obj P` and
`M = (baseChangeFamily b A P).obj L`. The conclusion therefore asserts two
things about the base-changed family. Its geometric fibres satisfy the
smooth-family condition. It classifies, by a unique actual map into `P_{S'}`,
every smooth-family algebraically trivial rigidified class over every
quasi-separated test over `S'`.

This file contains no proof of the statement.

## Relation to neighbouring statements

- `PicardZeroUniversalBaseChangeStatement` states the same base-change
  transport for `IsUniversalPicardZero`. That predicate uses the Library's
  geometric Picard-zero condition, which is translation invariance on
  geometric fibres. It also classifies on every test scheme. The present
  statement instead uses the explicit smooth-family witness condition, and
  both its hypothesis and its conclusion quantify only over quasi-separated
  tests. Neither statement implies the other directly: the classes and the
  test categories differ, and no comparison between the two fibre
  conditions is asserted here.
- Task `6302965b-461d-4759-82f5-74b5d48bff2d` states base change for the full
  `RigidifiedLineBundle.IsUniversal`. That predicate classifies all
  rigidified families on all test schemes, with no fibre condition. Its
  hypothesis and conclusion are both different from the ones here, so it does
  not give this statement directly either.

## Provenance

This is a derived statement about the Library's existing predicate. It is
not a verbatim theorem of any source. The following passages motivate the
representing functor and its compatibility with base change. Neither source
states this exact Lean theorem.

- Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
  varieties*, thesis revision of 14 March 2021, registered source
  `lan-2008-pel-thesis-revision-2021`, §1.3.2, PDF pp.101–102. Definition
  1.3.2.1, Lemma 1.3.2.2, Theorem 1.3.2.3 and Definition 1.3.2.5 give the
  rigidified Picard-zero functor, its representing dual abelian scheme and
  its universal rigidified Poincare bundle.
- Faltings–Chai, *Degeneration of Abelian Varieties*, registered source
  `provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
  Chapter I §1, printed pp.1–7. Definition 1.4 gives the rigidified relative
  Picard functor. The proof of Theorem 1.9 first reduces to affine bases and
  then to finite-type integer algebras.

Worker 141's accepted source map
`notes/abelian-schemes/relative-picard-source-map.md` records the passages
that were read.

The sources define the zero part by algebraic equivalence on ordinary
residue-field fibres. The Library's smooth-family condition is instead an
explicit geometric-fibre witness condition. This module does not assert any
comparison between the two. The base-change transport stated here is
intrinsic to the Library predicate, so its proof can work directly with the
explicit witnesses. The arbitrary morphism `b` and the unrestricted `S`, `S'`
and `P` come from transporting a supplied universal property by scheme
pullbacks. They do not extend any source existence theorem beyond the
sources' quasi-separated base conventions.

This statement is meant as the base-change ingredient for the
shared-representer proof task `e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`, whose
target is `SmoothFamilyAbelianRepresentabilityStatement`. Following
Faltings–Chai Theorem I.1.9, that proof reduces first to affine bases and
then to finite-type models. Restriction along open immersions `U → S` and
ground-base change from a finite-type model are both special cases of the
arbitrary morphism `b`.

## Future proof obligations

A proof must establish the following points. None of them is proved or
assumed here.

- Geometric fibres of the family. Every geometric point `Spec K → P_{S'}`
  gives a geometric point `Spec K → P` by composing with the projection.
  The geometric fibre of `A_{S'} ×_{S'} P_{S'}` at the first point must be
  identified with the geometric fibre of `A ×_S P` at the second point.
  The fibre bundles must be identified under that comparison.
  `IsAlgebraicallyTrivialViaSmoothFamily` must then be transported along an
  isomorphism of abelian schemes over `Spec K`. The existing
  `isAlgebraicallyTrivialViaSmoothFamily_of_iso` only transports along a
  line-bundle isomorphism on a fixed abelian scheme, so this is a new
  obligation.
- Tests. A test `T → S'` with quasi-separated underlying scheme is also a
  quasi-separated test over `S` through `b`, because quasi-separatedness is a
  property of the test scheme alone. The canonical isomorphism
  `T ×_{S'} A_{S'} ≅ T ×_S A` must identify actual rigidified families, their
  isomorphism classes and their smooth-family conditions. The class
  comparison again needs the geometric-fibre transport above.
- Parameter maps. The slice pullback adjunction identifies maps `T → P_{S'}`
  over `S'` with maps `T → P` over `S`. It must be shown that this
  identification and the class identification are compatible with the
  explicit family `baseChangeFamily b A P`. Unique classification then
  transports.

Useful existing Library names include `baseChangeFamily` and
`baseChangeFamilyForgetIso` (`PoincareBaseChange`),
`familyBaseChangeEquivalence` (`FamilyBaseChangeEquivalence`), and
`baseChangeParameterEquiv` and `baseChangeFamilyPullbackIso`
(`FamilyBaseChangeNaturality`). The argument of the private lemma
`baseChangeFamily_classifyingMap` in `DualAbelianBaseChangeProof` is also
relevant. That lemma is private and cannot be imported, so its argument must
be reproduced or exposed. `PicardZeroUniversalBaseChangeProof` carries out
the analogous Picard-zero argument on all tests.
