# The special-stabilizer identity after maximal unramified base change

`Langlands.GroupScheme.IntegralModel.UnramifiedSpecialStabilizerStatement` is a
proposition. Nothing in this module proves it.

## The statement

The proposition is universe polymorphic. At each universe `u` it ranges over:

* every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
  `IsNonarchimedeanLocalField F`, in equal and mixed characteristic;
* every actual group scheme `G` over `Spec F` with a proof
  `hG : IsConnectedReductive G`;
* every supplied `M : IntegralModel 𝒪[F] F G`, with its own generic
  identification, whose full actual special-fibre pullback
  `(GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group` is
  connected reductive.

These are exactly the binders and the special-fibre hypothesis of the
published `BuildingComparisonStatement`. The instance `IsAffineHom G.X.hom` is
derived from `hG`, and the affine instance of the scalar extension is its
pullback; neither is a premise.

Write `L = inertiaFixedField F` for the actual maximal unramified extension
(the Library's separable inertia fixed field, definitionally
`UnramifiedClosure F`), `𝒪_L = fixedFieldIntegers F` for its integers, and
`G_L = baseChanged F L G`. The model `M.baseChangeUnramified` is the published
actual coefficient base change of `M` to `𝒪_L`, with the generic
identification transported from `M.genericIso`. Its subgroup
`M.baseChangeUnramified.integralPoints` is the image of its integral sections
in `rationalPoints G_L`.

The statement quantifies over every supplied
`C : MaximalUnramified.BuildingData F G_L`: building data over `L` for the
constructed integer-valued valuation `MaximalUnramified.valuation F`, with a
maximal split torus of `G_L`, a full `ω`-compatible apartment class and the
actual centralizer. No building axiom is assumed of `C`. The conclusion is that
there is a point `x : C.ReducedBuilding` of the existing quotient (7.6.2) such
that

1. `C.IsSpecialPoint x`: `x` is a translate of the image of a special point of
   the apartment of `C`;
2. `M.baseChangeUnramified.integralPoints = C.oneStabilizer x`, where
   `C.oneStabilizer x` is the intersection of the stabilizer of `x` for the
   existing action of `rationalPoints G_L` with the actual common kernel
   `characterValuationKernel` of the valuations of all rational characters
   (the group `G(L)^1`);
3. `x` is the only point of `C.ReducedBuilding` fixed by every element of
   `M.baseChangeUnramified.integralPoints`.

## Source correspondence

Bruhat–Tits, *Groupes réductifs sur un corps local II* (1984), registered as
`bruhat-tits-1984-reductive-local-groups-ii`:

* Proposition 4.6.31, printed pp. 136–137 / PDF pp. 133–134. Over a Henselian
  discretely valued field with separably closed residue field, such as `L`, a
  smooth model `𝔊` with generic fibre `G` has reductive closed fibre if and
  only if `G` is split and `𝔊 ≅ 𝔊_x` for a special point `x` of the building.
  The model `M.baseChangeUnramified` is smooth with connected reductive closed
  fibre: the Library proves it reductive
  (`IntegralModel.isReductive_baseChangeUnramified`).
* Proposition 4.6.28(i), printed p. 135 / PDF p. 132: `𝔊_x(𝒪)` is the fixer of
  `x` in `G^1`. This gives clause 2.
* Corollary 4.6.29(i), printed p. 136 / PDF p. 133: a closed subset `Ω` of an
  apartment is exactly the fixed-point set of `𝔊_Ω(𝒪)` in that apartment. For
  `Ω = {x}` this is the apartment form of clause 3; Kaletha–Prasad,
  *Bruhat–Tits Theory: A New Approach* (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, uses the building form in
  the proof of Theorem 9.9.3(2), printed p. 381 / PDF p. 412 ("`x` is the
  unique point of `B(G_K)` fixed by `G(K)^0_x`").

The isomorphism in 4.6.31 is of `𝒪_L`-group schemes. When it does not induce
the identity on the generic fibre, clause 2 still holds at the point obtained
by transporting `x` through the induced automorphism of the building. The
statement quantifies over every `C`: its apartment class is unique given the
torus and centralizer (Kaletha–Prasad Proposition 6.2.6, printed p. 216 /
PDF p. 247; the Library's integer-valued rigidity
`IsOmegaCompatible.eq_of_hasOppositeFactorPairs`), so the quotient of `C` is
the building of `G_L`.

The provenance is derived: the statement combines the cited assertions on the
Library's existing quotient, model images and subgroups.

## Intended use

Together with the companion `UnramifiedBuildingDescentStatement`, this
statement implies `SpecialStabilizerStatement`. Given a base-field datum, the
descent statement supplies upstairs data `C`, a Galois action `D` and an
equivariant embedding `e`. Applying this statement to `C` gives `x`. The
published `unramifiedIntegralImage_semilinearAction_eq_of_unique_fixed` uses
clauses 2 and 3 to show that `x` is fixed by the Galois action, so `x = e z`.
The published `integralPoints_eq_compactStabilizer_of_unramified` then gives
`M.integralPoints = P.compactStabilizer z`, and the descent statement makes
`z` special. This deduction is compiled privately; it is not part of this
module.

## Scope

This is a statement. It constructs no building data and proves no
stabilizer identity.
