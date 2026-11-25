/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Cofinal finite affine étale coverings

## References

* Stacks Project, Tag 03Q4, first paragraph
* Stacks Project, Tags 03Q4, 0218 and 0738
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/--
For a quasi-compact and quasi-separated scheme, every jointly surjective étale
family admits a finite affine étale refinement with quasi-compact pairwise
fibre products.
-/
theorem etale_qcqs_cofinal_finite_affine_coverings
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    {A : Type v} (T : A → U.Etale) (f : ∀ a, T a ⟶ Scheme.Etale.mk (𝟙 U))
    (hf : Sieve.ofArrows T f ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U))) :
    ∃ (B : Type w) (_ : Finite B) (a : B → A) (V : B → U.Etale)
      (v : ∀ b, V b ⟶ Scheme.Etale.mk (𝟙 U)),
      (∀ b, IsAffine (V b).left) ∧
      (∀ b, ∃ h : V b ⟶ T (a b), h ≫ f (a b) = v b) ∧
      Sieve.ofArrows V v ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U)) ∧
      (∀ b b', CompactSpace (pullback (C := Scheme.{u}) (V b).hom (V b').hom)) := by
  classical
  have hf' := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp hf
  have hleft (a : A) : (f a).left = (T a).hom := by
    have h := CategoryTheory.MorphismProperty.Over.w (f a)
    change (f a).left ≫ 𝟙 U = (T a).hom at h
    change (f a).left = (T a).hom
    exact (Category.comp_id (f a).left).symm.trans h
  let C : U.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers A (fun a ↦ (T a).left) (fun a ↦ (T a).hom)
      (fun x ↦ by
        have hx : x ∈ ⋃ a, Set.range (f a).left := by rw [hf']; trivial
        obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hx
        rw [hleft] at hy
        change (T a).hom y = x at hy
        exact ⟨a, y, hy⟩)
  let : QuasiCompactCover C.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun a ↦ (C.f a).isOpenMap)
  obtain ⟨D, g, hfin, _⟩ := QuasiCompactCover.exists_hom C
  let : Finite D.I₀ := hfin
  let (b : D.I₀) : Etale (D.f b) := D.map_prop b
  let : Fintype D.I₀ := Fintype.ofFinite D.I₀
  let B := ULift.{w} (Fin (Fintype.card D.I₀))
  let e : B ≃ D.I₀ := Equiv.ulift.trans (Fintype.equivFin D.I₀).symm
  let V (b : B) : U.Etale := Scheme.Etale.mk (D.f (e b))
  let v (b : B) : V b ⟶ Scheme.Etale.mk (𝟙 U) :=
    CategoryTheory.MorphismProperty.Over.homMk (D.f (e b))
  refine ⟨B, inferInstance, (fun b ↦ g.s₀ (e b)), V, v, ?_, ?_, ?_, ?_⟩
  · intro b
    exact inferInstanceAs (IsAffine (Spec (D.X (e b))))
  · intro b
    refine ⟨CategoryTheory.MorphismProperty.Over.homMk (g.h₀ (e b)) (g.w₀ (e b)), ?_⟩
    apply CategoryTheory.MorphismProperty.Over.Hom.ext
    change g.h₀ (e b) ≫ (f (g.s₀ (e b))).left = D.f (e b)
    rw [hleft]
    exact g.w₀ (e b)
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff v).mpr
    change (⋃ b, Set.range (D.f (e b))) = Set.univ
    exact (e.surjective.iUnion_comp (fun i ↦ Set.range (D.f i))).trans D.cover.iUnion_range
  · intro b b'
    exact inferInstanceAs (CompactSpace (pullback (C := Scheme.{u}) (D.f (e b)) (D.f (e b'))))

end AlgebraicGeometry
