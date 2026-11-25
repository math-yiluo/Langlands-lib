/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.QuasiProjective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Abelian varieties are projective

An abelian variety admits a closed immersion into a projective space over the base field, hence
carries an ample invertible module (blueprint `lemma-symmetric-ample-sheaf--1`, Stacks 0BFA), and
the symmetrisation `L ⊗ [-1]^* L` of an ample invertible
module is again ample and is symmetric.

An abelian variety is a group scheme of finite type over `K`, hence quasi-projective: it admits
an immersion into a projective space over `K`
(`AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`, Stacks 0BF7). Being proper, the
immersion is closed (`AlgebraicGeometry.IsClosedImmersion.of_comp_of_isSeparated`), which is the
case `S = Spec K` of Stacks 0B45.

`AlgebraicGeometry.IsVeryAmple` is a genuine definition, and so is the tensor product
`AlgebraicGeometry.Scheme.Modules.tensorObj` (see
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`), through whose tensor powers ampleness is
phrased. So `IsAbelianVariety.exists_isAmple` follows from
`IsAbelianVariety.exists_isClosedImmersion_projectiveSpace`, with `M := j^* 𝒪(1)` and the first
tensor power, together with the identification `M^{⊗ 1} ≅ M`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.symmetrisation`: the symmetrisation `L ⊗ [-1]^* L`.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.exists_isClosedImmersion_projectiveSpace`: abelian
  varieties are projective.
- `AlgebraicGeometry.IsAbelianVariety.exists_isAmple`: abelian varieties carry an ample
  invertible module.
- `AlgebraicGeometry.IsAbelianVariety.isAmple_symmetrisation`,
  `AlgebraicGeometry.IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation`:
  `L ⊗ [-1]^* L` is ample and symmetric.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- The *symmetrisation* `L ⊗ [-1]^* L` of an invertible module `L` on a group scheme: the
smallest symmetric module built from `L`. -/
noncomputable def Scheme.Modules.symmetrisation {A : Over (Spec (.of K))} [GrpObj A]
    (L : A.left.Modules) : A.left.Modules :=
  tensorObj L (overPullback ι[A] L)

/-- Blueprint `lemma-symmetric-ample-sheaf--1`: Abelian
varieties are projective.

Every abelian variety `A` over a field `K` admits a closed immersion into a projective space
over `Spec K` compatible with the structure morphisms. The index type of the projective space
is called `α`; `ι`, the usual name for an index type, is unavailable as an identifier here,
being the token of the inversion notation `ι[A]`.

The proof follows Stacks 0BFA: `A` is a group scheme of finite type over `K`, so it admits an
immersion into a projective space over `K` (Stacks 0BF7), and an immersion of the proper
`K`-scheme `A` into the separated `K`-scheme `ℙ(α; Spec K)` is closed (Stacks 0B45). -/
theorem IsAbelianVariety.exists_isClosedImmersion_projectiveSpace (A : Over (Spec (.of K)))
    [GrpObj A] [IsAbelianVariety A] :
    ∃ (α : Type u) (_ : Finite α) (j : A.left ⟶ ℙ(α; Spec (.of K))),
      IsClosedImmersion j ∧ j ≫ ℙ(α; Spec (.of K)) ↘ Spec (.of K) = A.hom := by
  obtain ⟨α, _, j, hj, hjA⟩ := GrpObj.exists_isImmersion_projectiveSpace A
  refine ⟨α, inferInstance, j, ?_, hjA⟩
  have : IsProper (j ≫ ℙ(α; Spec (.of K)) ↘ Spec (.of K)) := hjA ▸ inferInstance
  exact IsClosedImmersion.of_comp_of_isSeparated j (ℙ(α; Spec (.of K)) ↘ Spec (.of K))

/-- Blueprint `lemma-symmetric-ample-sheaf--1`: Abelian
varieties are projective.

Being projective, an abelian variety carries an ample invertible `𝒪_A`-module, namely the
pullback `j^* 𝒪(1)` of the twisting sheaf along a closed immersion `j` into a projective space:
it is very ample, and equal to its first tensor power. -/
theorem IsAbelianVariety.exists_isAmple (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] :
    ∃ M : A.left.Modules, IsAmple A.hom M := by
  obtain ⟨α, _, j, hj, hjA⟩ := exists_isClosedImmersion_projectiveSpace A
  have hM : IsVeryAmple A.hom (ProjectiveSpace.twistRestrict j 1) :=
    ⟨α, j, inferInstance, hj, hjA, ⟨Iso.refl _⟩⟩
  refine ⟨_, hM.isInvertible, 1, one_pos, ?_⟩
  obtain ⟨β, i, hβ, hi, hiA, ⟨e⟩⟩ := hM
  refine ⟨β, i, hβ, hi, hiA, ⟨e ≪≫ ?_⟩⟩
  rw [tensorPow_succ, tensorPow_zero]
  exact (ρ_ _).symm

/-- Blueprint `lemma-symmetric-ample-sheaf--1`: A symmetric ample module (also
`lemma-symmetric-ample-sheaf--1`).

Let `A` be an abelian variety over `K` and let `L` be an ample invertible `𝒪_A`-module. Then the
symmetrisation `L ⊗ [-1]^* L` is ample: `[-1]` is an automorphism, so `[-1]^* L` is ample, and a
tensor product of ample modules is ample (`AlgebraicGeometry.IsAmple.tensorObj`). -/
theorem IsAbelianVariety.isAmple_symmetrisation (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (L : A.left.Modules) (hample : IsAmple A.hom L) :
    IsAmple A.hom L.symmetrisation := by
  have : IsClosedImmersion ι[A].left := by
    have : IsIso ι[A].left := (Over.forget _).map_isIso ι[A]
    infer_instance
  have h := hample.pullback ι[A].left
  rw [Over.w ι[A]] at h
  exact hample.tensorObj h

/-- Blueprint `lemma-symmetric-ample-sheaf--1`: A symmetric ample module (also
`lemma-symmetric-ample-sheaf--1`).

The symmetrisation `N = L ⊗ [-1]^* L` of an invertible module on an abelian variety is
*symmetric*, that is `[-1]^* N ≅ N`: since `[-1] ∘ [-1] = id`, one has
`[-1]^* N ≅ [-1]^* L ⊗ [-1]^* [-1]^* L ≅ [-1]^* L ⊗ L ≅ N`. -/
theorem IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (L : A.left.Modules)
    [L.IsInvertible] :
    Nonempty (overPullback ι[A] L.symmetrisation ≅ L.symmetrisation) := by
  obtain ⟨e⟩ := nonempty_pullback_tensorObj_iso ι[A].left L (overPullback ι[A] L)
  have h : ι[A].left ≫ ι[A].left = 𝟙 A.left := by
    rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]
  exact ⟨e ≪≫ (Iso.refl _ ⊗ᵢ ((pullbackComp ι[A].left ι[A].left).app L ≪≫
    (pullbackCongr h).app L ≪≫ (pullbackId A.left).app L)) ≪≫ β_ _ _⟩

end AlgebraicGeometry
