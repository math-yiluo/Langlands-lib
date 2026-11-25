/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverDescent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Spreading
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Quasi-projectivity descends along field extensions

Over a field `k`, a scheme `X` is quasi-projective precisely when it admits an immersion over
`Spec k` into a projective space `ℙ(β; Spec k)` with finitely many homogeneous coordinates; this
is the form in which quasi-projectivity is phrased here.

## Main definitions

- `AlgebraicGeometry.IsQuasiProjective`: a scheme over a field is quasi-projective if it admits
  an immersion into a projective space.

## Main statements

- `AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_pullback`: if the base change `X_K`
  of a `k`-scheme `X` to a field extension `K / k` is quasi-projective over `K`, then `X` is
  quasi-projective over `k` (Stacks 0BDE).

## Implementation details

The descent follows Stacks 0BDE. The pullback of `𝒪(1)` along the immersion is ample; the
resulting morphism to projective space with affine preimages of the standard opens is defined
over a finite extension `k'` of `k`, and taking norms along `X_{k'} ⟶ X` gives an ample
coordinate cover of `X`, hence an immersion into projective space.

## References

* Stacks Project, Tags 0BDE, 01ZY
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A scheme `X` over a field `k`, with structure morphism `f`, is *quasi-projective* if it
admits an immersion over `Spec k`, that is a locally closed immersion, into a projective space
`ℙ(β; Spec k)` with finitely many homogeneous coordinates; equivalently, an open immersion into
a closed subscheme of such a projective space. -/
def IsQuasiProjective {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop :=
  ∃ (β : Type u) (_ : Finite β) (i : X ⟶ ℙ(β; Spec (.of k))),
    IsImmersion i ∧ i ≫ ℙ(β; Spec (.of k)) ↘ Spec (.of k) = f

/-- **Quasi-projectivity descends along field extensions** (Stacks 0BDE). Let `K / k` be a field
extension and let `X` be a scheme over `k`. If the base change `X_K` admits an immersion over
`Spec K` into a projective space `ℙ(α; Spec K)` with finitely many homogeneous coordinates, then
`X` admits an immersion over `Spec k` into a projective space `ℙ(β; Spec k)` with finitely many
homogeneous coordinates. -/
@[stacks 0BDE]
theorem exists_isImmersion_projectiveSpace_of_pullback {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {α : Type u} [Finite α]
    (j : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ ℙ(α; Spec (.of K)))
    [IsImmersion j] (hj : j ≫ ℙ(α; Spec (.of K)) ↘ Spec (.of K) = pullback.snd _ _) :
    ∃ (β : Type u) (_ : Finite β) (i : X ⟶ ℙ(β; Spec (.of k))),
      IsImmersion i ∧ i ≫ ℙ(β; Spec (.of k)) ↘ Spec (.of k) = f := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hsurj : Surjective φ := surjective_specMap_algebraMap_of_field
  have hflat : Flat φ := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (pullback.fst f φ) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ hsurj
  have : IsAffineHom (pullback.fst f φ) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  -- `X_K` is of finite type over `K`
  have : IsLocallyNoetherian ℙ(α; Spec (.of K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(α; Spec (.of K)) ↘ Spec (.of K))
  have : QuasiCompact j := by
    rw [← j.liftCoborder_ι]
    infer_instance
  have : CompactSpace ℙ(α; Spec (.of K)) :=
    QuasiCompact.compactSpace_of_compactSpace (ℙ(α; Spec (.of K)) ↘ Spec (.of K))
  have : CompactSpace ↥(pullback f φ) := QuasiCompact.compactSpace_of_compactSpace j
  have : QuasiSeparatedSpace ↥(pullback f φ) := quasiSeparatedSpace_of_quasiSeparated j
  have : CompactSpace X := (pullback.fst f φ).surjective.compactSpace (pullback.fst f φ).continuous
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_surjective (pullback.fst f φ)
  have : LocallyOfFiniteType (pullback.snd f φ) := by
    rw [← hj]
    infer_instance
  have : LocallyOfFiniteType f :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback f φ).flip
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ inferInstance
  -- the pullback of `𝒪(1)` is ample on `X_K`, and this descends to a finite extension of `k`
  obtain ⟨γ, hγ, ψ, hψo, hψ⟩ := exists_isAffineOpen_preimage_of_isImmersion j
  obtain ⟨k', _, _, _, Y, π, q, H, ψ', hψ'⟩ :=
    exists_finite_isAffineOpen_preimage_standardOpen f ψ (hψo.trans hj) hψ
  -- taking norms gives an ample coordinate cover of `X`
  obtain ⟨ι, hι, 𝒟, h𝒟⟩ := exists_coordinateCover_of_isPullback H ψ' hψ'
  exact 𝒟.exists_isImmersion f h𝒟

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Finite sets of points of a projective scheme lie in an affine open.** Let `X` be a scheme
with a closed immersion `i : X ⟶ ℙ(α; Spec k)` into a projective space. Then every finite set of
points of `X` is contained in an affine open subscheme (Stacks 01ZY, for projective schemes). -/
@[stacks 01ZY]
theorem exists_isAffineOpen_superset_of_isClosedImmersion {X : Scheme.{u}} {α : Type u}
    (i : X ⟶ ℙ(α; Spec (.of k))) [IsClosedImmersion i] (s : Set X) (hs : s.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  classical
  let φ := i ≫ ProjectiveSpace.toProjInt α (Spec (.of k))
  obtain ⟨m, hm, f, hf, hfS⟩ :=
    ProjectiveSpectrum.exists_homogeneous_notMem_of_finset
      (𝒜 := MvPolynomial.homogeneousSubmodule α (ULift.{u} ℤ)) (hs.image φ.base).toFinset
  have hU₀ := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule α (ULift.{u} ℤ))
    f hf hm
  have : IsAffineHom (ProjectiveSpace.toProjInt α (Spec (.of k))) := by
    have : IsAffineHom (terminal.from (Spec (.of k))) := isAffineHom_of_isAffine _
    exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ this
  refine ⟨φ ⁻¹ᵁ Proj.basicOpen _ f, hU₀.preimage φ, fun x hx ↦ ?_⟩
  exact hfS (φ.base x) (by simpa using ⟨x, hx, rfl⟩)

end AlgebraicGeometry
