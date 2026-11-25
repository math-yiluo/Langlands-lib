/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Descending quasi-compact opens to finitely generated subalgebras

Let `X` be a scheme over a field `k` and `A` a `k`-algebra. Every quasi-compact open of
`X_A = X ×_k Spec A` is the inverse image of a quasi-compact open of `X_{A'}` for some finitely
generated `k`-subalgebra `A' ⊆ A` (Stacks, Tag 0388). We write `X_A` as the limit of the `X_{A'}`
and use the descent of quasi-compact opens along limits with affine transition maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The projection `X_A ⟶ X_B` for a subalgebra `B ⊆ A`. -/
private noncomputable def canonicalProjection (k : Type u) [Field k] (X : Scheme.{u})
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

/-- A point of an open `V ⊆ X_A` has a neighbourhood inside `V` which is the inverse image of
a quasi-compact open of `X_B` for a finitely generated subalgebra `B`. -/
private theorem exists_descended_qc_neighborhood_core (k : Type u) [Field k] (X : Scheme.{u})
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

private theorem exists_descended_qc_neighborhood (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A]
    (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens)
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))))
    (hx : x ∈ V) :
    ∃ (B : Subalgebra k A), B.FG ∧
      ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Opens),
        IsCompact W.1 ∧
        let π := baseChangeMap f
          (Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val B)))
            (by
              change Spec.map (CommRingCat.ofHom (Subalgebra.val B)) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap k B)) =
                Spec.map (CommRingCat.ofHom (algebraMap k A))
              rw [← Spec.map_comp]
              congr 1) :
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))))
        x ∈ π ⁻¹ᵁ W ∧ π ⁻¹ᵁ W ≤ V := by
  obtain ⟨B, hB, W, hW, hxW, hWV⟩ :=
    exists_descended_qc_neighborhood_core k X f A V x hx
  refine ⟨B, hB, W, hW, ?_⟩
  dsimp only
  simpa [canonicalProjection] using And.intro hxW hWV

private noncomputable def subalgebraOverProjection
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] (B : Subalgebra k A) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val B).toRingHom)) (by
    dsimp only [Over.mk_hom]
    rw [← Spec.map_comp]
    rfl)

private noncomputable def subalgebraOverTransition
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {B C : Subalgebra k A} (h : B ≤ C) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k C))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    dsimp only [Over.mk_hom]
    rw [← Spec.map_comp]
    rfl)

private noncomputable def subalgebraProjection
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (B : Subalgebra k A) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  baseChangeMap f (subalgebraOverProjection B)

private noncomputable def subalgebraTransition
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {B C : Subalgebra k A} (h : B ≤ C) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k C))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  baseChangeMap f (subalgebraOverTransition h)

private theorem subalgebraProjection_transition
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {B C : Subalgebra k A} (h : B ≤ C) :
    subalgebraProjection f C ≫ subalgebraTransition f h = subalgebraProjection f B := by
  have hc : subalgebraOverProjection C ≫ subalgebraOverTransition h =
      subalgebraOverProjection B := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Subalgebra.val C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.val B).toRingHom)
    rw [← Spec.map_comp]
    rfl
  change baseChangeMap f _ ≫ baseChangeMap f _ = baseChangeMap f _
  rw [← baseChangeMap_comp, hc]

private theorem subalgebraTransition_quasiCompact
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {B C : Subalgebra k A} (h : B ≤ C) : QuasiCompact (subalgebraTransition f h) := by
  apply MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_baseChangeMap f (subalgebraOverTransition h)).flip
  change QuasiCompact (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))
  infer_instance

/-- A quasi-compact open in a base change to an algebra descends to a finitely generated
subalgebra. Source: Stacks Project, Tag 0388.
(blueprint: `lem-weil-pbc-descend-qc-open-fg-subalgebra`) -/
theorem exists_fg_subalgebra_preimage_eq_of_isCompact (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A] :
    ∀ (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens),
      IsCompact V.1 →
      ∃ (A' : Subalgebra k A), A'.FG ∧
        ∃ (V' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A')))).Opens),
          IsCompact V'.1 ∧
          ∃ (π : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⟶
              (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A')))) ),
            π = baseChangeMap f
              (Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val A')))
                (by
                  change Spec.map (CommRingCat.ofHom (Subalgebra.val A')) ≫
                      Spec.map (CommRingCat.ofHom (algebraMap k A')) =
                    Spec.map (CommRingCat.ofHom (algebraMap k A))
                  rw [← Spec.map_comp]
                  congr 1
                  ) :
                  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
                    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A')))) ∧
            V = (π ⁻¹ᵁ V')  := by
  classical
  intro V hV
  let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let P : Y.Opens → Prop := fun U ↦
    ∃ (B : Subalgebra k A), B.FG ∧
      ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Opens),
        IsCompact W.1 ∧ U = subalgebraProjection f B ⁻¹ᵁ W
  have hbot : P ⊥ := by
    exact ⟨⊥, Subalgebra.fg_bot, ⊥, isCompact_empty, rfl⟩
  have hsup : ∀ U T, P U → P T → P (U ⊔ T) := by
    rintro U T ⟨B, hB, W, hW, rfl⟩ ⟨C, hC, Z, hZ, rfl⟩
    have h₁ : QuasiCompact (subalgebraTransition f (le_sup_left : B ≤ B ⊔ C)) :=
      subalgebraTransition_quasiCompact f _
    have h₂ : QuasiCompact (subalgebraTransition f (le_sup_right : C ≤ B ⊔ C)) :=
      subalgebraTransition_quasiCompact f _
    refine ⟨B ⊔ C, hB.sup hC,
      (subalgebraTransition f le_sup_left ⁻¹ᵁ W) ⊔
        (subalgebraTransition f le_sup_right ⁻¹ᵁ Z),
      (Scheme.Hom.isCompact_preimage _ hW).union
        (Scheme.Hom.isCompact_preimage _ hZ), ?_⟩
    rw [Scheme.Hom.preimage_sup, ← Scheme.Hom.comp_preimage,
      ← Scheme.Hom.comp_preimage, subalgebraProjection_transition,
      subalgebraProjection_transition]
  have hlocal : ∀ x : V, ∃ U : Y.Opens, P U ∧ x.1 ∈ U ∧ U ≤ V := by
    intro x
    obtain ⟨B, hB, W, hW, hx, hle⟩ :=
      exists_descended_qc_neighborhood k X f A V x.1 x.2
    exact ⟨_, ⟨B, hB, W, hW, rfl⟩, hx, hle⟩
  choose U hU hxU hUV using hlocal
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun x : V ↦ (U x).1)
    (fun x ↦ (U x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hfin : ∀ t : Finset V, P (t.sup U) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using hbot
    | @insert x t hxt ih =>
      rw [Finset.sup_insert]
      exact hsup _ _ (hU x) ih
  have hcover : s.sup U = V := by
    apply le_antisymm
    · exact Finset.sup_le fun x _ ↦ hUV x
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact (Finset.le_sup (f := U) hi : U i ≤ s.sup U) hxi
  obtain ⟨B, hB, W, hW, hEq⟩ := hcover ▸ hfin s
  exact ⟨B, hB, W, hW, subalgebraProjection f B, rfl, hEq⟩

end AlgebraicGeometry
