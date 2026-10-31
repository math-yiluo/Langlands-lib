# Proof: base change of the actual universal smooth-family property

`Langlands.AbelianScheme.smoothFamilyUniversalBaseChange.{u}` proves the
published `SmoothFamilyUniversalBaseChangeStatement.{u}`. Let `b : S' ⟶ S` be
any morphism of schemes, `A/S` an abelian scheme, `P/S` a parameter scheme and
`L` a rigidified family on `P ×_S A` satisfying
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`. Then
`(baseChangeFamily b A P).obj L` satisfies
`IsUniversalSmoothFamilyOnQuasiSeparatedTests` for `(baseChange b).obj A`, with
parameter scheme `(Over.pullback b).obj P`.

All schemes lie in one universe. The theorem adds no hypothesis on `S`, `S'`,
`b` or `P`. It proves both conjuncts of the predicate and asserts no existence
of universal families.

## Provenance

This is an internal derived consequence of the supplied universal property and
the Library's comparisons of actual scheme and line-bundle pullbacks. It
follows the published Picard-zero proof `picardZeroUniversalBaseChange`
(module `PicardZeroUniversalBaseChangeProof`, private helper
`universalBaseChange_of_geometric`). It also follows the published
`rigidifiedUniversalBaseChange` (module `RigidifiedUniversalBaseChangeProof`).
Two things change. The geometric Picard-zero condition is replaced by the
smooth-family witness condition, and tests are restricted to quasi-separated
ones.

## Auxiliary results in the module

- The imported public lemma `isAlgebraicallyTrivialViaSmoothFamily_pullback_hom`
  from [`SmoothFamilyPullbackProof`](SmoothFamilyPullbackProof.md). Let
  `f : A.X ⟶ B.X` be any slice morphism of abelian schemes over `Spec K`, with
  `K` algebraically closed. If `L` on `B` has a smooth-family witness, then so
  does its pullback along `f.left`. The witness keeps the same parameter `C`
  and marked points `c0` and `c1`, and pulls the family back along
  `C ×_K A → C ×_K B`. The endpoint isomorphisms use the commuting restriction
  maps and `LineBundle.pullbackTrivialIso` at the trivial endpoint.

  Integration exported the existing private `smoothFamilyTriviality_pullback`
  under this public name and removed this module's duplicate proof and product
  helpers. The statement and proof are unchanged.
- `isFibrewiseAlgebraicallyTrivialViaSmoothFamily_pullback_groupIso_iff`. Let
  `e : A.toGrp ≅ B.toGrp` be an actual isomorphism of the underlying group
  schemes of two abelian schemes over `X`, and let `L` be a line bundle on `B`.
  Then the pullback of `L` along `e` satisfies
  `IsFibrewiseAlgebraicallyTrivialViaSmoothFamily` if and only if `L` does.
  Fix a geometric point `s : Spec K ⟶ X`. Base change of `e` along `s` gives an
  isomorphism `d` of the geometric fibres, and `d` commutes with the first
  projections. Hence the fibre of the pulled-back bundle is isomorphic to the
  pullback of the fibre of `L` along `d`. The previous lemma applied to `d.hom`
  gives one direction. Applied to `d.inv`, together with
  `d.inv ≫ d.hom = 𝟙`, it gives the other. This follows the structure of
  `isGeometricallyPicardZero_pullback_groupIso_iff` in
  `PicardZeroFamilyBaseChangeProof`.
- `isAlgebraicallyTrivialFamilyViaSmoothFamily_familyBaseChange_iff`. For
  `T : Over S'` and a rigidified family `L` for `A` over `(Over.map b).obj T`,
  `L` satisfies `IsAlgebraicallyTrivialFamilyViaSmoothFamily` if and only if
  `(familyBaseChange b A T).obj L` does for `(baseChange b).obj A`. The proof
  applies the previous lemma to the published group isomorphism
  `familyBaseChangeGroupIso b A T`. It then transports along the published
  line-bundle isomorphism `familyBaseChangeLineBundleIso b A T L` with
  `isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_iso`.

## The main proof

Write `L'` for `(baseChangeFamily b A P).obj L`. By definition this is
`familyBaseChange b A ((Over.pullback b).obj P)` applied to the relative
pullback of `L` along `baseChangeParameterMap b P`.

- First conjunct (fibre condition). The published `smoothFamilyPullback`
  shows that the relative pullback of `L` along `baseChangeParameterMap b P`
  satisfies the smooth-family condition. The family-level equivalence above
  then transfers the condition to `L'`.
- Second conjunct (classification). Fix `T : Over S'` with quasi-separated
  `T.left` and a smooth-family class `q` over `T`. The proof chooses a
  representative `M` of `q` (`Quotient.inductionOn`) and rewrites both
  classifying-map equations with `RigidifiedLineBundle.classifyingMap_eq_iff`.
  Each equation becomes the existence of an isomorphism of rigidified families.
  Let `F = familyBaseChange b A T` and `G = familyBaseChangeInverse b A T`.
  The family `N = G.obj M` over `(Over.map b).obj T` satisfies the
  smooth-family condition. This follows from the counit isomorphism
  `familyBaseChangeCounitIso`, `isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_iso`
  and the family-level equivalence above. The underlying scheme of
  `(Over.map b).obj T` is `T.left`, so it is quasi-separated. The hypothesis
  therefore gives a unique `g : (Over.map b).obj T ⟶ P` together with an
  isomorphism `eg` from the pullback of `L` along `g` to `N`.

  Let `e = baseChangeParameterEquiv b T P`. The proof takes `e.symm g` as the
  classifying map.

  - Existence. `baseChangeFamilyPullbackIso b A (e.symm g)` identifies the
    pullback of `L'` along `e.symm g` with `F` applied to the pullback of `L`
    along the mate of `e.symm g`. That mate equals `g` by `e.apply_symm_apply`.
    Composing with `F.mapIso eg` and the counit at `M` gives an isomorphism to
    `M`.
  - Uniqueness. Let `k` be a map whose pullback of `L'` is isomorphic to `M`
    by some `ek`. The inverse unit `familyBaseChangeUnitIso`, then `G` applied
    to the inverse of `baseChangeFamilyPullbackIso b A k` composed with `ek`,
    shows that the pullback of `L` along `e k` is isomorphic to `N`.
    Uniqueness of `g` gives `e k = g`. Injectivity of `e` then gives
    `k = e.symm g`.

## Imports

The module imports the statement module and the following, all under
`Langlands.AlgebraicGeometry.Picard`:

- `SmoothFamilyPullbackProof`, for `smoothFamilyPullback` and
  `isAlgebraicallyTrivialViaSmoothFamily_pullback_hom`;
- `PicardZeroFamilyBaseChangeProof`, for `familyBaseChangeGroupIso` and
  `familyBaseChangeLineBundleIso`;
- `FamilyBaseChangeEquivalence`, for `familyBaseChangeInverse` and the unit and
  counit isomorphisms;
- `FamilyBaseChangeNaturality`, for `baseChangeParameterEquiv` and
  `baseChangeFamilyPullbackIso`.
