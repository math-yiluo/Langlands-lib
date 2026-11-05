# A fixed split torus containing the full centre, from conjugacy and self-centralization

This module proves the implication
`FixedCenterContainingTorusReductionStatement`: two published Library
propositions that are not yet proved imply the exact target
`FixedCenterContainingTorusStatement`, in every universe `u`. Both inputs are
explicit premises. The module does not prove either of them, and it does not
prove the target unconditionally.

- `MaximalTorusConjugacyStatement` (module `Absolute/BorelStatement`; Milne,
  Theorem 17.10): in a smooth affine group scheme with connected underlying space
  over an algebraically closed field, two maximal tori `j`, `j'` are conjugate by a
  rational point `g`. The conjugacy is an isomorphism `φ` of the tori with
  `j ≫ innerIso g = φ ≫ j'`.
- `AlgClosedMaximalTorusCentralizerStatement` (module
  `Absolute/MaximalTorusCentralizerReduction`; Milne, Proposition 17.61(a), the
  algebraically closed case of Corollary 17.84): a maximal torus of a connected
  reductive group over an algebraically closed field is its own centralizer, as an
  equality of subgroup functors.

## Declarations

- `AutomorphicAction.act_mem_center`: an automorphic action `a` of `S` on `G` takes
  points of the full centre `center G` to points of the centre, on every test
  scheme. It holds because each `a.act s` is a group automorphism of the points over
  every refinement, natural in the test scheme.
- `AutomorphicAction.semidirect_conj_inl_act_inv_of_mem_center`: let `g` be a point of
  the semidirect product `G ⋊ S`, let `s` be its `S`-coordinate under
  `semidirectPointsEquiv`, and let `x` be a central point of `G`. Then, after the
  inclusion `semidirectInl` of the normal factor,
  `g · (s⁻¹ · x) · g⁻¹ = x`. The proof computes in Mathlib's `SemidirectProduct` of
  point groups: the `G`-coordinate of `g` commutes with `x`, and the `s`-action
  cancels `s⁻¹`.
- `FixedCenterContainingTorusReductionStatement` (a `Prop` definition): the
  implication from the two premises above to `FixedCenterContainingTorusStatement`.
- `fixedCenterContainingTorusReduction`: the proof of that implication.

## The proof

Let `k` be algebraically closed, `G` connected reductive over `k`, `S` a split torus,
and `b` an automorphic action of `S` on `G`. Write `H = G ⋊_b S` for
`b.semidirectProduct`.

1. **The fixed torus.** The proved
   `AutomorphicAction.exists_maximalTorus_with_fixed_intersection` gives a maximal
   torus `j : M ⟶ H` through which `S` factors. Its actual intersection
   `T₀ = b.semidirectTorusIntersection j` with the normal factor `G` is a torus.
   The inclusion `T₀ ⟶ G` is a closed subgroup, and `S` fixes the points of `T₀` on
   every test scheme. Over the algebraically closed field `T₀` is split, by
   `torusFiniteGaloisSplitting` and `IsTorus.isSplitTorus_of_finiteGaloisSplitting`.
   The torus `T₀` with this inclusion is the witness, so only centre containment
   remains.
2. **A second maximal torus of `H`.** The proved `maximalTorusExistence` gives a
   maximal torus `i₁ : T₁ ⟶ G`. The composite `T₁ ⟶ G ⟶ H` is a closed torus, so
   `exists_maximalTorus_extension_of_finiteType` extends it to a maximal torus
   `j' : M' ⟶ H` with a factor `f' : T₁ ⟶ M'`.
3. **Conjugacy.** `H` is smooth and affine over `k`. Its underlying space is
   connected because it is the fibre product of `G` and `S` over `Spec k`, and `G` is
   geometrically connected (`GroupScheme.geometricallyConnected_of_connected`). The
   conjugacy premise, applied in `H`, gives a rational point `g` of `H` and an
   isomorphism `φ : M' ≅ M` with `j' ≫ innerIso g = φ ≫ j`.
4. **Centre containment.** Let `x` be a point of `center G` over a test scheme `U`.
   Let `c` be the constant point of `g` over `U` and `s` the `S`-coordinate of `c`. The
   point `y = s⁻¹ · x` is central by `act_mem_center`. The proved
   `center_le_torusCentralizer` puts it in the centralizer of `T₁`. The
   self-centralization premise for `T₁` then gives `y = t ≫ i₁` for some point `t`
   of `T₁`. Since `f' ≫ j' = i₁ ≫ semidirectInl`, the image of `y` in `H` is the
   point `t ≫ f' ≫ j'` of `M'`. Conjugation by `g`
   (`comp_innerIso_hom`) sends it to `c · y · c⁻¹`, which is `x` by
   `semidirect_conj_inl_act_inv_of_mem_center`. The conjugacy identity gives
   `x = (t ≫ f' ≫ φ) ≫ j`. So `x` lies in both `M` and the normal factor, which is
   the intersection, by `range_commutativeSubgroupIntersection`. The commuting
   square `semidirectTorusIntersection_condition`, together with the cancellation
   of the monomorphism `semidirectInl`, writes `x` as a point of `T₀`.

The conclusion holds for every test scheme, including nonreduced ones. No
smoothness or reducedness of the centre is used. The witness torus need not be
maximal in `G`, and the target does not require that.

## Provenance

**Derived.** The target statement comes from Conrad, Gabber and Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition 3.3.10(c)
(printed p.113, PDF p.139) and Corollary A.4.7(2) (printed pp.495–497, PDF
pp.521–523). Their argument factors the action through the adjoint quotient and
lifts a maximal torus from there. This module follows a different, internal
argument. It works in the semidirect product `G ⋊ S` and uses the two cited Milne
results only as the premises above: Theorem 17.10 (printed p.354, PDF p.370) and
Proposition 17.61(a) with Corollary 17.84 (printed pp.372 and 379, PDF pp.388
and 395). The idea is that a maximal torus of `G` contains the centre, that `S`
preserves the centre, and that conjugation by a rational point of `G ⋊ S` carries
a maximal torus through that torus onto a maximal torus containing `S`. On central
points this conjugation acts only through the `S`-coordinate of the point. The
Lean arrangement, the two helper lemmas and the proof are internal.
