# Proof: base change of the actual rigidified universal property

`Langlands.AbelianScheme.rigidifiedUniversalBaseChange.{u}` proves the
published `RigidifiedUniversalBaseChangeStatement.{u}`: for any morphism
`b : S' ⟶ S`, if the rigidified family `L` on `A ×_S P` is universal, then
`(baseChangeFamily b A P).obj L` is universal for `A_{S'}` with parameter
scheme `(Over.pullback b).obj P`.

This is an internal derived consequence of the existing universal property and
the published comparisons of actual scheme and line-bundle pullbacks. It
follows the classification half (the part using the hypothesis named
`universal`) of the private helper `universalBaseChange_of_geometric` behind the
published proof `picardZeroUniversalBaseChange` (module
`Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof`), with
the Picard-zero membership conditions removed.

## The implemented proof

Both universality hypotheses are rewritten with
`RigidifiedLineBundle.isUniversal_iff`: a family is universal when every
rigidified family `M` on every test object `T` is isomorphic to the pullback of
the family along a unique parameter map.

Fix `T : Over S'` and a rigidified family `M` for `A_{S'}` over `T`. Let
`F = familyBaseChange b A T` and `G = familyBaseChangeInverse b A T` be the two
directions of the published equivalence of rigidified families. Universality of
`L`, applied to the test object `(Over.map b).obj T` over `S` and the family
`G.obj M`, gives a unique `g : (Over.map b).obj T ⟶ P` with an isomorphism `eg`
from the pullback of `L` along `g` to `G.obj M`.

Let `e = baseChangeParameterEquiv b T P` be the slice pullback adjunction
bijection between maps `T ⟶ P_{S'}` over `S'` and maps `(Over.map b).obj T ⟶ P`
over `S`; its forward map is `baseChangeParameterMate b`. The candidate
classifying map is `e.symm g`.

- Existence. `baseChangeFamilyPullbackIso b A (e.symm g)` identifies the
  pullback of the new family along `e.symm g` with `F` applied to the pullback
  of `L` along the mate of `e.symm g`. The mate equals `g`
  (`e.apply_symm_apply`), which gives an `eqToIso`. Composing with `F.mapIso eg`
  and the counit `familyBaseChangeCounitIso b A T` at `M` gives the required
  isomorphism to `M`.
- Uniqueness. Given `k : T ⟶ P_{S'}` with an isomorphism `ek` from the pullback
  of the new family along `k` to `M`, the inverse of
  `baseChangeFamilyPullbackIso b A k`, then `ek`, then `G`, preceded by the
  inverse unit `familyBaseChangeUnitIso b A T`, show that the pullback of `L`
  along `e k` is isomorphic to `G.obj M`. Uniqueness of `g` gives `e k = g`, and
  injectivity of `e` gives `k = e.symm g`.

The module imports only the statement module, `FamilyBaseChangeEquivalence`
(for `familyBaseChangeInverse` and the unit and counit isomorphisms) and
`FamilyBaseChangeNaturality` (for `baseChangeParameterEquiv`,
`baseChangeParameterMate` and `baseChangeFamilyPullbackIso`), all under
`Langlands.AlgebraicGeometry.Picard`.

All schemes lie in one universe, and every test scheme is allowed, including
nonreduced schemes. The theorem transports a supplied universal family; it
proves no existence of universal families.
