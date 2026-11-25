/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- The canonical projection from the base change over `A` to that over `B`.
Source: Stacks Project, Varieties, Tag 0388.
(blueprint: lem-weil-pbc-descended-qc-neighborhood-core). -/
noncomputable def canonicalProjection (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A]
    (B : Subalgebra k A) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  baseChangeMap f
    (Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val B))) (by
      change Spec.map (CommRingCat.ofHom (Subalgebra.val B)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k B)) =
        Spec.map (CommRingCat.ofHom (algebraMap k A))
      rw [← Spec.map_comp]
      congr 1) :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))))

/-- Core finite-coefficient construction for one point and one open.
Source: Stacks Project, Varieties, proof of Tag 0388, lines 811--848.
(blueprint: lem-weil-pbc-descended-qc-neighborhood-core).
The finitely generated subalgebras of `A` form a nonempty directed system with
colimit `A`. Applying `Spec` and base changing by `f` expresses `X_A` as the
inverse limit of the schemes `X_B`, with affine transition maps. Choose an affine
open neighborhood of `x` inside `V`; compact-open descent for this limit gives a
compact open at some stage whose inverse image is exactly that neighborhood. -/
theorem exists_descended_qc_neighborhood_core (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A]
    (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens)
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))))
    (hx : x ∈ V) :
    ∃ (B : Subalgebra k A), B.FG ∧
      ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Opens),
        IsCompact W.1 ∧ x ∈ (canonicalProjection k X f A B) ⁻¹ᵁ W ∧
          (canonicalProjection k X f A B) ⁻¹ᵁ W ≤ V := by
  classical
  let I := {B : Subalgebra k A // B.FG}
  have : Nonempty I := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  let : IsDirectedOrder I := ⟨fun B C ↦ ⟨⟨B.1 ⊔ C.1, B.2.sup C.2⟩,
    show B.1 ≤ B.1 ⊔ C.1 from le_sup_left,
    show C.1 ≤ B.1 ⊔ C.1 from le_sup_right⟩⟩
  let D : Iᵒᵖ ⥤ Scheme.{u} := (CommRingCat.fgSubalgebraDiagramOf k A).op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCoconeOf k A).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec
    (CommRingCat.isColimitFGSubalgebraCocone k A).op
  let T : Iᵒᵖ ⥤ Over (Spec (CommRingCat.of k)) :=
    { obj := fun i ↦ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1)))
      map := fun {i j} g ↦ Over.homMk (D.map g) (by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]
        rfl)
      map_id := fun i ↦ by apply Over.OverMorphism.ext; exact D.map_id i
      map_comp := fun g h ↦ by apply Over.OverMorphism.ext; exact D.map_comp g h }
  let E : Iᵒᵖ ⥤ Scheme.{u} :=
    { obj := fun i ↦ pullback f (T.obj i).hom
      map := fun g ↦ baseChangeMap f (T.map g)
      map_id := fun i ↦ by rw [T.map_id, baseChangeMap_id]
      map_comp := fun g h ↦ by rw [T.map_comp, baseChangeMap_comp] }
  let q : E ⟶ D :=
    { app := fun i ↦ pullback.snd f (T.obj i).hom
      naturality := fun i j g ↦ by simp [E, baseChangeMap, T] }
  let e : Cone E :=
    { pt := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      π :=
        { app := fun i ↦ canonicalProjection k X f A i.unop.1
          naturality := fun i j g ↦ by
            apply pullback.hom_ext
            · simp [canonicalProjection, E, baseChangeMap, T]
            · simp only [Functor.const_obj_obj, Over.mk_left, Over.mk_hom, baseChangeMap,
                Functor.const_obj_map, canonicalProjection, Over.homMk_left,
                Category.id_comp, limit.lift_π, PullbackCone.mk_π_app, Category.assoc,
                limit.lift_π_assoc, cospan_right, T, E]
              change pullback.snd _ _ ≫ c.π.app j =
                pullback.snd _ _ ≫ c.π.app i ≫ D.map g
              rw [c.w g] } }
  let : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  have he : IsLimit e := isLimitOfIsPullbackOfIsConnected q e c
    { hom := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      w := fun i ↦ by simp [e, q, c, canonicalProjection, baseChangeMap, T] }
    (fun i ↦ isPullback_baseChangeMap f _) hc
  have {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (E.map g) := by
    apply MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_baseChangeMap f (T.map g)).flip
    change IsAffineHom (Spec.map _)
    infer_instance
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
  obtain ⟨i, W, hW, hWU⟩ := exists_preimage_eq E e he U hU.isCompact
  refine ⟨i.unop.1, i.unop.2, W, hW, ?_, ?_⟩
  · change x ∈ e.π.app i ⁻¹ᵁ W
    rw [hWU]
    exact hxU
  · change e.π.app i ⁻¹ᵁ W ≤ V
    rw [hWU]
    exact hUV
end AlgebraicGeometry
