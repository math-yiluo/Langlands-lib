/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent

/-!
# Effective descent for projective schemes over an arbitrary base

Let `p : X ⟶ Y` be a surjective finite locally free morphism and let `V` be a scheme over `X`
whose structure morphism is (H-)projective. Every descent datum on `V` relative to `p` is
effective (Stacks 0CCJ).

## Main statements

- `AlgebraicGeometry.IsHProjective.exists_isAffineOpen_superset`: if `f : V ⟶ X` is H-projective
  and `W ⊆ X` is an affine open, every finite set of points of `f⁻¹ W` lies in an affine open of
  `V` (Stacks 01ZY).
- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite_of_fibre`: along a surjective finite
  locally free morphism, descent data are effective as soon as every finite set of points of `V`
  lying over one point of `Y` lies in an affine open (Stacks 0CCI).
- `CategoryTheory.Over.DescentDatum.isEffective_of_isHProjective`: along a surjective finite
  locally free morphism, descent data on H-projective schemes over `X` are effective (blueprint
  `proposition-jacobian-over-ground-field--1`).

## Proof

Finitely many points of `V` over one point `y` of `Y` lie over an affine open `W ∋ y` of `Y`,
hence over the affine open `p⁻¹ W` of `X`. The base change of the closed immersion
`V ⟶ ℙ(n; X)` to `p⁻¹ W` is a closed immersion of the open `V|_{p⁻¹ W}` into `ℙ(n; p⁻¹ W)`, so
the points lie in an affine open (`exists_isAffineOpen_superset_of_isImmersion_of_isAffine`).
This is the criterion of Stacks 0CCI: it gives invariant affine neighbourhoods over affine opens
of `Y`, on which the descent datum is effective by affine descent, and these glue.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Finite sets in projective schemes lie in affine opens** (Stacks 01ZY). Let `f : V ⟶ X` be
H-projective and `W ⊆ X` an affine open. Then every finite set of points of `V` lying over `W`
lies in an affine open of `V`. -/
theorem IsHProjective.exists_isAffineOpen_superset {V X : Scheme.{u}} (f : V ⟶ X)
    [IsHProjective f] {W : X.Opens} (hW : IsAffineOpen W) (s : Set V) (hs : s.Finite)
    (hsW : s ⊆ f ⁻¹ᵁ W) : ∃ U : V.Opens, IsAffineOpen U ∧ s ⊆ U := by
  obtain ⟨n, _, i, _, hi⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  have : IsAffine W := hW
  let U₀ := f ⁻¹ᵁ W
  let j : U₀.toScheme ⟶ ℙ(n; W) := ProjectiveSpace.liftBaseChange (g := W.ι) (f ∣_ W)
    (U₀.ι ≫ i) (by rw [Category.assoc, hi, morphismRestrict_ι])
  have hpb : IsPullback U₀.ι (f ∣_ W) (i ≫ ℙ(n; X) ↘ X) W.ι := by
    rw [hi]
    exact (isPullback_morphismRestrict f W).flip
  have : IsClosedImmersion j := MorphismProperty.of_isPullback
    (ProjectiveSpace.isPullback_liftBaseChange _ hpb _) inferInstance
  have : CompactSpace ℙ(n; W) := QuasiCompact.compactSpace_of_compactSpace (ℙ(n; W) ↘ W)
  have : CompactSpace U₀ := QuasiCompact.compactSpace_of_compactSpace j
  have : QuasiSeparatedSpace U₀ := quasiSeparatedSpace_of_quasiSeparated (j ≫ ℙ(n; W) ↘ W)
  obtain ⟨U, hU, hsU⟩ := exists_isAffineOpen_superset_of_isImmersion_of_isAffine j
    (U₀.ι ⁻¹' s) (hs.preimage U₀.ι.isOpenEmbedding.injective.injOn)
  refine ⟨U₀.ι ''ᵁ U, hU.image_of_isOpenImmersion U₀.ι, fun x hx ↦ ?_⟩
  exact ⟨⟨x, hsW hx⟩, hsU hx, rfl⟩

end AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

/-- **Effective descent along finite locally free morphisms** (Stacks 0CCI). Let `p : X ⟶ Y` be a
surjective finite locally free morphism and let `V` be a scheme over `X` in which every finite set
of points lying over one point of `Y` lies in an affine open. Then every descent datum on `V`
relative to `p` is effective.

(blueprint: `proposition-jacobian-over-ground-field--1`, a step of the proof) -/
theorem isEffective_of_isFinite_of_fibre [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] {V : Over X}
    (hV : ∀ (y : Y) (s : Set V.left), s.Finite → (∀ x ∈ s, (V.hom ≫ p) x = y) →
      ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (D : Over.DescentDatum p V) : D.IsEffective := by
  refine isEffective_of_forall_exists_mem fun v ↦ ?_
  obtain ⟨U, hv, hU, hUa, W, hW, hUW⟩ := D.exists_isInvariant_isAffineOpen_of_fibre hV v
  exact ⟨U, hU, hv, D.isEffective_restrict_of_isAffineOpen hU hUa hW hUW⟩

/-- **Effective descent for projective schemes.** Let `p : X ⟶ Y` be a surjective finite locally
free morphism and let `V` be a scheme over `X` whose structure morphism `V ⟶ X` is H-projective:
it factors as a closed immersion `V ⟶ ℙ(n; X)`, with `n` finite, followed by the projection
`ℙ(n; X) ⟶ X` (in particular this applies when `V ⟶ X` is projective,
`AlgebraicGeometry.IsProjective`). Then every descent datum on `V` relative to `p` is effective.

This is Stacks 0CCJ: finitely many points of `V` over one point of `Y` lie in an affine open
(`AlgebraicGeometry.IsHProjective.exists_isAffineOpen_superset`), which is the criterion
`isEffective_of_isFinite_of_fibre` (Stacks 0CCI).

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem isEffective_of_isHProjective [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] {V : Over X} [IsHProjective V.hom] (D : Over.DescentDatum p V) :
    D.IsEffective := by
  refine D.isEffective_of_isFinite_of_fibre fun y s hs hsy ↦ ?_
  obtain ⟨W, hW, hyW, -⟩ := p.exists_isAffineOpen_mem_free_app y
  refine IsHProjective.exists_isAffineOpen_superset V.hom (hW.preimage p) s hs fun x hx ↦ ?_
  change p (V.hom x) ∈ W
  rw [← Scheme.Hom.comp_apply, hsy x hx]
  exact hyW

end CategoryTheory.Over.DescentDatum
