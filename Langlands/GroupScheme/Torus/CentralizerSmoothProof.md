# Smoothness of torus centralizers: proof

Worker 1379.

`Langlands.GroupScheme.torusCentralizerSmooth` proves
`Langlands.GroupScheme.TorusCentralizerSmoothStatement.{u}` for every universe
`u`. The data are a field `k`, a smooth affine group scheme `G` over `Spec k`, a
commutative group scheme `T` with `IsTorus T.toGrp`, a closed subgroup
`i : T.toGrp ⟶ G`, and a closed subgroup `j : C ⟶ G` that represents
`torusCentralizer i`. The goal is `Smooth C.X.hom`.

The statement follows Milne, *Algebraic Groups* (2017), Corollary 13.10. Milne
derives it from the smoothness of fixed loci of actions of groups of
multiplicative type. The Lean proof follows the same idea: it splits the torus
over a field extension, applies the published smoothness theorem for fixed
subgroups of split diagonalizable actions, and descends smoothness back to `k`.
The closedness hypothesis on `i` is not used.

## Steps

1. **Splitting field.** `hT.splittingExtension` (from `Torus/Geometry.lean`)
   chooses a field `K = E.carrier` with a `k`-algebra structure such that the
   base change of `T.toGrp` along `b : Spec K ⟶ Spec k` is a split torus. Its
   field `isSplitTorus` gives a finite type `I` and an isomorphism
   `e : (baseChange b).obj T.toGrp ≅ splitTorus (Spec K) I`.

2. **Descent of smoothness.** `fieldExtension_fpqc k K` shows that `b` is
   surjective, flat and quasi-compact. Mathlib's
   `MorphismProperty.of_pullback_snd_of_descendsAlong`, for the property
   `Smooth`, reduces the goal to smoothness of
   `pullback.snd C.X.hom b`, the structure morphism of the base change of `C`
   to `K`. The same pattern is used for `IsTorus.smooth` in `Torus/Geometry.lean`.

3. **Ambient group after base change.** The base change of `G` to `K` has
   structure morphism `pullback.snd G.X.hom b`. It is smooth and affine because
   both properties are stable under base change (found by instance search).

4. **The base-changed representative.** Over `K`, the base-changed
   homomorphism `(baseChange b).map j` represents the fixed subgroup of the
   conjugation action `AutomorphicAction.conjugation ((baseChange b).map i)`
   of the base-changed torus on the base-changed `G`. Three published
   facts give this:
   `AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer`
   identifies the fixed subgroup with `torusCentralizer` of the base-changed
   `i`; `torusCentralizer_baseChange` (in
   `Torus/MaximalBaseChangeForwardReduction.lean`) identifies that with the
   base change of `torusCentralizer i`; and
   `SubgroupFunctor.IsRepresentedBy.baseChange` transfers the representation
   `hj` along `b`. The acting group is stated as
   `((CommGroupScheme.baseChange b).obj T).toGrp`, because the commutative
   base change is needed to form `torusCentralizer`.

5. **Split diagonalizable case.** `Diagonalizable.splitIso K (AddEquiv.refl
   (I → ℤ))` identifies the diagonalizable group `D(I → ℤ)` with
   `splitTorus (Spec K) I`. Composing `e` with its inverse gives an isomorphism
   of the acting group with `D(I → ℤ)`. The lattice `I → ℤ` is finitely
   generated because `I` is finite. The published
   `Diagonalizable.fixedSubgroup_smooth_of_actingIso`, applied to the proved
   `Diagonalizable.FixedSmooth.fixedSubgroupSmooth` (Conrad–Gabber–Prasad,
   Proposition A.8.10(2)), the smooth affine ambient group from step 3, the
   representation from step 4, and closedness of the base-changed `j`
   (`IsClosedSubgroup.baseChange`), gives smoothness of the base change of
   `C`. Step 2 then finishes the proof.

## Dependencies

The proof imports `Torus/CentralizerSmoothStatement.lean`,
`Torus/MaximalBaseChangeForwardReduction.lean` (for
`torusCentralizer_baseChange`), `Torus/Geometry.lean`,
`Torus/DiagonalizableFixedSmoothProof.lean` and
`Rational/KernelCentralizerSmooth.lean`. It uses no new axioms.
