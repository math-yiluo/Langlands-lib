# Proof of the reduced closed subspace statement

Author: Worker 5067.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceProof`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspace`.

The main theorem is

`reducedClosedSubspace : ReducedClosedSubspaceStatement.{u}`.

It proves the published statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceStatement`, with no added
hypotheses. The statement's saturation hypothesis on the range of `j` is not used: surjectivity
of `f_T` holds for the space `Y_T` constructed below without it.

Imports: the helper module `KernelPairDescent` (submitted with this proof), the statement,
`TupleOrbitInduction` (for `reducedOver`), `FinitePresentationRelationQuotient`,
`SmoothReducedBase` and `Morphisms.FpqcFiniteDescent`.

## Construction

Notation: `h_X` is the functor of points of a scheme `X` over `S` (`schemeYoneda S`), and
`hom f` is the map of presheaves underlying a morphism of algebraic spaces.

Data: `f : U ⟶ Y` finite and surjective, `Y` quasi-compact and quasi-separated, `j : U_T ⟶ U` a
closed immersion with `U_T` reduced.

1. Atlas. `Y` is quasi-compact, so it has an étale surjective atlas `a_Y : h_V ⟶ Y` with `V`
   quasi-compact. The Library's `exists_kernelPair` represents its kernel pair by
   `t, s : R ⟶ V` with `s` étale.
2. `F = h_j ≫ hom f : h_{U_T} ⟶ Y` is finite (`isFinite_map`, `IsFinite.comp`). Its base
   change along `a_Y` is a scheme `W_T` with projections `φ_T : W_T ⟶ U_T` (étale and
   surjective) and `p_T : W_T ⟶ V` (finite). `W_T` is reduced, being étale over the reduced
   `U_T` (`SmoothReducedBase.isReduced_of_smooth_of_isReduced`).
3. `V_T` is the reduced induced closed subscheme of `V` on the closed set `p_T(W_T)`
   (`reducedOver`), with closed immersion `ι : V_T ⟶ V`. The finite map `p_T` factors as
   `q_T ≫ ι`, because `W_T` is reduced (`exists_lift_isClosedImmersion_over`). Then `q_T` is
   finite, since `ι` is separated, and surjective onto `V_T`.
4. `R_T = R ×_{s,V} V_T` with projections `ι_R : R_T ⟶ R` and `s_T : R_T ⟶ V_T`. The
   relation maps `p_T(W_T)` into itself (`mem_range_of_isPullback`), so
   `t ∘ ι_R` factors through `V_T` as `t_T` (again because `R_T` is reduced, being étale over
   `V_T`). Then `t_T, s_T` represent the kernel pair of `h_ι ≫ a_Y`
   (`isPullback_restrict`), and both are étale (`etale_of_isPullback_symm`).
5. `Q` is the algebraic space quotient of `V_T` by this étale equivalence relation
   (`EtaleEquivalenceRelation.ofKernelPair` and the Library's
   `etaleEquivalenceRelationAlgebraicSpaceQuotient`), with étale surjective atlas
   `a : h_{V_T} ⟶ Q` whose kernel pair is again `t_T, s_T`.
6. `h_ι ≫ a_Y` is constant on this kernel pair, so it descends to `i : Q ⟶ Y` with
   `a ≫ i = h_ι ≫ a_Y` (`KernelPairDescent.exists_desc`). `i` is a monomorphism: `t_T, s_T`
   represent the kernel pairs of both `a` and `a ≫ i`
   (`KernelPairDescent.injective_of_isPullback`).
7. `h_{q_T} ≫ a : h_{W_T} ⟶ Q` is constant on the kernel pair of `h_{φ_T}`. This is checked
   after composing with the monomorphism `i`, where it follows from the pullback square
   of step 2. So it descends along the locally surjective `h_{φ_T}`
   (`isLocallySurjective_map`) to `f_T : h_{U_T} ⟶ Q`. Then `f_T ≫ i = F`
   (`KernelPairDescent.hom_ext_of_isLocallySurjective`).

The output is `Y_T = Q` with the morphism `AlgebraicSpace.homMk f_T`.

## Properties

- The square `(φ_T, q_T; f_T, a)` is a pullback. It is the step 2 square with the
  monomorphisms `ι` and `i` cancelled: `isPullback_of_comp_mono` and
  `isPullback_of_comp_mono_right`.
- `Q` is quasi-compact: `V_T` is compact, as a closed subscheme of the compact `V`, and maps
  onto `Q` by `a` (`IsQuasiCompact.of_atlas`).
- `Q` is quasi-separated (`FinitePresentationRelationQuotient.isQuasiSeparated_of_atlas`). This
  needs `(t_T, s_T) : R_T ⟶ V_T × V_T` (products over `S`) to be quasi-compact. Composed with
  `ι × ι`, it equals `ι_R ≫ (t, s)`, which is quasi-compact; so `(t_T, s_T)` is quasi-compact
  by `QuasiCompact.of_comp`. Here `ι_R` is a closed immersion, and `(t, s) : R ⟶ V × V` is
  quasi-compact because `Y` is quasi-separated: `quasiCompact_prodLift_of_isQuasiSeparated`,
  which uses the pullback of the diagonal of `Y` in `isPullback_kernel_diagonal`.
- `f_T` is finite: its base change along the étale surjective atlas `a` is `q_T`, which is
  finite. Finiteness descends along fppf covers (`descendsAlong_isFinite`, from the Library's
  fpqc descent of finiteness in `Morphisms.FpqcFiniteDescent`). The Library's
  `relative_of_isEtale_isSurjective` then applies.
- `f_T` is surjective: its base change `q_T` along `a` is surjective
  (`isSurjective_of_isPullback`).
- Same images (`sameImage_iff_of_mono`, using `f_T ≫ i = h_j ≫ hom f` with `i` a monomorphism):
  - Forward: compose a witness for `f_T` with `j` and `i`.
  - Backward: let a witness for `hom f` be two maps `g, g' : T ⟶ U` and a point `τ` of `T`.
    Restrict to `Spec κ(τ)`, which is reduced and has a single point. Both restrictions land
    in the closed range of `j`, so they factor through `U_T`
    (`exists_lift_isClosedImmersion_over`). The factored maps hit `x` and `x'`, since `j` is
    injective, and agree after `f_T` because `i` is a monomorphism.

## Auxiliary results

- `vanishingIdeal_le_ker`, `exists_lift_vanishingIdeal`: a morphism `g` from a reduced scheme
  whose range lies in a closed set `Z` factors through the reduced induced closed subscheme on
  `Z`. Unlike the Library's `ReducedSubscheme.exists_lift_vanishingIdeal`, `g` need not be
  quasi-compact. A section in the vanishing ideal pulls back to a section with empty basic
  open set, which vanishes on a reduced scheme (`eq_zero_of_basicOpen_eq_bot`).
- `exists_lift_isClosedImmersion`: the same for the range of an arbitrary closed immersion `j`,
  since the kernel of `j` lies in the vanishing ideal of its closed range.
- `exists_lift_reducedOver`, `exists_lift_isClosedImmersion_over`: the same over `S`.
- `isPullback_of_comp_mono`, `isPullback_of_comp_mono_right`: in any category, a monomorphism
  on the top edge of a pullback square can be moved to the right edge, and a common
  monomorphism on the right and bottom edges can be cancelled.
- `over_comp_apply`: `(f ≫ g).left x = g.left (f.left x)`.
- `exists_lift_of_isPullback`: lifting test maps through a pullback square of represented
  presheaves, using that `schemeYoneda S` is fully faithful.
- `isFinite_map`: `h_φ` is finite when `φ.left` is a finite morphism of schemes.
- `IsFinite.comp`: finite maps of presheaves compose.
- The proof reuses `FinitePresentationRelationQuotient.isPullback_kernel_diagonal`,
  exposed from the existing quotient module with its statement and proof unchanged.
  The kernel-pair square of `a` maps to the diagonal square of its target.

## Provenance

Derived. Mathematically, `Q` is the reduced induced closed subspace of `Y` on the closed set
`f(|U_T|)` (Stacks Project, Properties of Algebraic Spaces, Lemma 66.12.3, Tag 03IQ), and
`f_T` is the factorization of `U_T ⟶ Y` through it (Lemma 66.12.4, Tag 03JJ), as described in
`ReducedClosedSubspaceStatement.md`. The Lean proof builds `Q` directly as the quotient of
the reduced closed subscheme `V_T` of an atlas by the restricted étale relation. It identifies
`Q` with a subsheaf of `Y` only through the monomorphism `i`, which the statement does not
record.
