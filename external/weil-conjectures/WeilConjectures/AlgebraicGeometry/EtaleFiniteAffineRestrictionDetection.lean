/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Cover.Open
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-! # Finite affine restrictions detect equality after base change
Source: Stacks Project, Tags 01IT, 03Q4 and 00VL.
(blueprint: lem-weil-pbc-etale-finite-affine-restriction-detection). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, Tag 03Q4, finite affine-cover reduction, with Tags 01IT
and 00VL for affine covers and sheaf separatedness.
(blueprint: lem-weil-pbc-etale-finite-affine-restriction-detection).
Proof: W is qcqs because its structure map is qcqs and S is qcqs. Choose a finite
affine open cover of W. Regard its members as étale objects V a over S and the open
immersions as arrows v a to W. Each V a has qcqs structure map: its affine source is
quasi-compact and quasi-separated and S is quasi-separated. For any h : T ⟶ S,
base change preserves the covering, since open immersions and joint surjectivity are
stable under base change. For a sheaf F on T, separatedness on this covering says that
two sections of h*W with equal restrictions to every h*(V a) agree. If W is empty,
choose the empty family; the empty covering gives the same uniqueness assertion.
Only separatedness is asserted; no matching or gluing data are required. -/
theorem etale_finite_affine_restriction_detection
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (W : S.Etale) [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    ∃ (n : ℕ) (V : Fin n → S.Etale) (v : ∀ a, V a ⟶ W),
      (∀ a, IsAffine (V a).left) ∧
      (∀ a, QuasiCompact (V a).hom) ∧
      (∀ a, QuasiSeparated (V a).hom) ∧
      ∀ (T : Scheme.{u}) (h : T ⟶ S)
        (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
        (s t : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W))),
        (∀ a, F.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ h).map (v a)).op s =
          F.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ h).map (v a)).op t) →
        s = t  := by
  classical
  have : CompactSpace W.left :=
    @QuasiCompact.compactSpace_of_compactSpace W.left S W.hom _ inferInstance
  let C := W.left.affineCover.finiteSubcover
  let e : Fin (Fintype.card C.I₀) ≃ C.I₀ := (Fintype.equivFin C.I₀).symm
  let V (a : Fin (Fintype.card C.I₀)) : S.Etale :=
    Scheme.Etale.mk (C.f (e a) ≫ W.hom)
  let v (a : Fin (Fintype.card C.I₀)) : V a ⟶ W :=
    MorphismProperty.Over.homMk (C.f (e a)) rfl
  have haff (a : Fin (Fintype.card C.I₀)) : IsAffine (V a).left := by
    change IsAffine (C.X (e a))
    dsimp [C, Scheme.OpenCover.finiteSubcover, Scheme.affineCover]
    infer_instance
  refine ⟨Fintype.card C.I₀, V, v, haff, ?_, ?_, ?_⟩
  · intro a
    have : IsAffine (V a).left := haff a
    exact @quasiCompact_of_compactSpace (V a).left S (V a).hom
      inferInstance inferInstance
  · intro a
    have : IsAffine (V a).left := haff a
    exact @QuasiSeparated.of_quasiSeparatedSpace (V a).left S (V a).hom inferInstance
  · intro T h F s t heq
    have hcover : Sieve.ofArrows V v ∈ S.smallEtaleTopology W := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff v).mpr
      change (⋃ a, Set.range (C.f (e a))) = Set.univ
      exact (e.surjective.iUnion_comp (fun a ↦ Set.range (C.f a))).trans C.iUnion_range
    have hbase := (Scheme.coverPreserving_overPullback
      (P := @Etale) (Q := @Etale) (le_refl _) h).cover_preserve hcover
    rw [Sieve.functorPushforward_ofArrows] at hbase
    have hh := F.property.hom_ext_ofArrows
      (fun a ↦ (MorphismProperty.Over.pullback @Etale ⊤ h).map (v a)) hbase
      (x := TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ s))
      (y := TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ t)) (fun a ↦ by
        ext z
        exact heq a)
    exact congrArg (fun f ↦ f PUnit.unit) hh


end AlgebraicGeometry
