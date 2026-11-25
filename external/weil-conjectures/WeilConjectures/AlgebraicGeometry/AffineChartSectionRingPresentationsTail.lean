/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitData
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Section rings of upper-tail affine charts

Source: Stacks Project, Tag 01ZR, affine reduction, and Tag 01I4.
(blueprint: new-affine-chart-section-ring-presentations-tail).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Paste a cover-chart square with a base-change square, retaining both projections. -/
private noncomputable def chartBaseChangeIso
    {S X : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (b : T' ⟶ T)
    (U : (pullback f T.hom).OpenCover.{u}) (a : U.I₀) :
    (U.pullback₁ (baseChangeMap f b)).X a ≅
      pullback b.left (U.f a ≫ pullback.snd f T.hom) :=
  ((IsPullback.of_hasPullback (baseChangeMap f b) (U.f a)).paste_horiz
    (isPullback_baseChangeMap f b).flip).isoPullback

private theorem chartBaseChangeIso_hom_snd
    {S X : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (b : T' ⟶ T)
    (U : (pullback f T.hom).OpenCover.{u}) (a : U.I₀) :
    (chartBaseChangeIso f b U a).hom ≫ pullback.snd _ _ =
      U.pullbackHom (baseChangeMap f b) a :=
  IsPullback.isoPullback_hom_snd _

private theorem chartBaseChangeIso_hom_fst
    {S X : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (b : T' ⟶ T)
    (U : (pullback f T.hom).OpenCover.{u}) (a : U.I₀) :
    (chartBaseChangeIso f b U a).hom ≫ pullback.fst _ _ =
      (U.pullback₁ (baseChangeMap f b)).f a ≫ pullback.snd f T'.hom :=
  IsPullback.isoPullback_hom_fst _

/-- Apply global sections to a geometric comparison and the colimit leg equation. -/
private theorem section_colimit_compatibility
    {J : Type u} [Category J] (F : J ⥤ CommRingCat.{u})
    {Z W Y D : Scheme.{u}} (β : colimit F ≅ Γ(Z, ⊤))
    (z : W ≅ Z) (e : Y ≅ D) (x : J) (hx : F.obj x = Γ(D, ⊤))
    (π : Z ⟶ D) (hι : colimit.ι F x ≫ β.hom = eqToHom hx ≫ π.appTop)
    {V : Scheme.{u}} (v : V ⟶ W) (l : V ⟶ Y)
    (hp : v ≫ z.hom ≫ π = l ≫ e.hom) (b : F.obj x) :
    v.appTop ((β ≪≫ Scheme.Γ.mapIso z.op).commRingCatIsoToRingEquiv
      ((colimit.ι F x).hom b)) =
    l.appTop ((eqToIso hx ≪≫ Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv b) := by
  have hpΓ := congrArg Scheme.Hom.appTop hp
  simp only [Scheme.Hom.comp_appTop] at hpΓ
  change (colimit.ι F x ≫ β.hom ≫ z.hom.appTop ≫ v.appTop).hom b =
    (eqToHom hx ≫ e.hom.appTop ≫ l.appTop).hom b
  rw [← Category.assoc, ← Category.assoc, hι]
  simp only [Category.assoc]
  exact ConcreteCategory.congr_hom (congrArg (fun h ↦ eqToHom hx ≫ h) hpΓ) b

/-- Representatives of a directed preorder quotient form a cofinal functor. -/
private theorem representative_final {J : Type u} [Preorder J] [IsDirectedOrder J] :
    (OrderEmbedding.ofAntisymmetrization (α := J)).monotone.functor.Final := by
  classical
  let rep := (OrderEmbedding.ofAntisymmetrization (α := J)).monotone.functor
  have hrep (k : J) : toAntisymmetrization (· ≤ ·)
      (rep.obj (toAntisymmetrization (· ≤ ·) k)) =
      toAntisymmetrization (· ≤ ·) k :=
    toAntisymmetrization_ofAntisymmetrization (· ≤ ·) _
  let : IsDirectedOrder (Antisymmetrization J (· ≤ ·)) := ⟨by
    intro x y
    obtain ⟨k, hx, hy⟩ := exists_ge_ge (rep.obj x) (rep.obj y)
    refine ⟨toAntisymmetrization (· ≤ ·) k, ?_, ?_⟩
    · have hh := toAntisymmetrization_mono hx
      change toAntisymmetrization (· ≤ ·) (ofAntisymmetrization (· ≤ ·) x) ≤ _ at hh
      simpa only [toAntisymmetrization_ofAntisymmetrization] using hh
    · have hh := toAntisymmetrization_mono hy
      change toAntisymmetrization (· ≤ ·) (ofAntisymmetrization (· ≤ ·) y) ≤ _ at hh
      simpa only [toAntisymmetrization_ofAntisymmetrization] using hh⟩
  apply (Monotone.final_functor_iff _).mpr
  intro k
  refine ⟨toAntisymmetrization (· ≤ ·) k, ?_⟩
  apply toAntisymmetrization_le_toAntisymmetrization_iff.mp
  change toAntisymmetrization (· ≤ ·) k ≤
    toAntisymmetrization (· ≤ ·) (rep.obj (toAntisymmetrization (· ≤ ·) k))
  rw [hrep]

/-- The actual upper-tail chart rings present the direct and finite-stage chart rings.
Source: Stacks Project, Tag 01ZR, affine reduction, and Tag 01I4.
(blueprint: new-affine-chart-section-ring-presentations-tail).

Proof: The upper tail is directed, as is its antisymmetrization. The quotient class
of a representative is the original class, so the representative functor is final
by the directed-preorder cofinality criterion. Its opposite is initial. Whisker the
explicit limiting upperTailChartCone along this opposite functor. Every object is
a pullback of affine schemes over Spec R(j), so Mathlib's preservesColimit_Γ sends
the opposite cone to a colimit of exactly F. The unique comparison of colimit points
gives β from colimit F to the sections of the cone vertex.

Paste the chart pullback square with the base-change square. Its universal property
gives z from the direct chart to the cone vertex, and e from each finite-stage chart
to the corresponding diagram object. Their two projection equations are fixed by
isoPullback. Their targets are affine, so their sources are affine. Apply Γ to z
and e and compose the former with β to obtain ρ₀ and ρₓ. The initial and finite-stage
equations follow from the second projections: maps in Over.pullback preserve that
projection to U(a). For the last equation, the two maps from the iterated chart to
the stage diagram object have identical first projections by pullbackHom_map and
the baseChangeMap projection equation, and identical second projections by the
formula defining v. Pullback uniqueness equates them. Apply appTop and the colimit
leg equation for β to obtain the required elementwise compatibility. All objects
are the displayed pullbacks; no arbitrary existence witness supplies ring data.
The argument also covers empty charts, zero rings, and equivalent preorder indices. -/
theorem affine_chart_section_ring_presentations_tail
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    :
    let rep := (OrderEmbedding.ofAntisymmetrization
      (α := {k : I // j ≤ k})).monotone.functor
    let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
    let F := rep ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ
    let t := toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})
    let kₜ := rep.obj t
    let s := pullback.snd (Spec.map (R.map (homOfLE kₜ.property))) g
    let r₀ := (colimit.ι F t).hom
    let q₀ := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    IsAffine ((U.pullback₁ q₀).X a) ∧
    ∃ (ρ₀ : ↑(colimit F) ≃+* Γ((U.pullback₁ q₀).X a, ⊤)),
      (∀ b, ρ₀ (r₀ (s.appTop b)) = (U.pullbackHom q₀ a).appTop b) ∧
      ∀ (x : Antisymmetrization {k : I // j ≤ k} (· ≤ ·)) (htx : t ≤ x),
        let k := (rep.obj x).val
        let hjk := (rep.obj x).property
        let q := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        let q₀ := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        let w : p ≫ q = q₀ := by
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op
        let r := (F.map (homOfLE htx)).hom
        let r₁ := (colimit.ι F x).hom
        let Uk : (pullback f (Spec.map
          (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} := U.pullback₁ q
        let V : (pullback f (c.π.app (op i))).OpenCover.{u} := Uk.pullback₁ p
        let v : V.X a ⟶ (U.pullback₁ q₀).X a := pullback.lift (V.f a)
          (Uk.pullbackHom p a ≫ U.pullbackHom q a)
          (by
            dsimp only [V]
            rw [Category.assoc, U.pullbackHom_map,
              ← Category.assoc, Uk.pullbackHom_map, Category.assoc, w])
        ∃ (ρₓ : ↑(F.obj x) ≃+* Γ((U.pullback₁ q).X a, ⊤)),
          (∀ b, ρₓ (r (s.appTop b)) = (U.pullbackHom q a).appTop b) ∧
          IsAffine (Uk.X a) ∧
          (∀ b, v.appTop (ρ₀ (r₁ b)) = (Uk.pullbackHom p a).appTop (ρₓ b)) := by
  classical
  intro rep g F t kₜ s r₀ q₀
  let : IsAffine (U.X a) := ha
  let J := {k : I // j ≤ k}
  let : IsDirectedOrder J := ⟨by
    intro k l
    obtain ⟨m, hk, hl⟩ := exists_ge_ge k.val l.val
    exact ⟨⟨m, k.property.trans hk⟩, hk, hl⟩⟩
  let : rep.Final := representative_final
  let D := upperTailChartDiagram R j g
  let d := upperTailChartCone R c j g
  have hd : IsLimit d :=
    (upperTailChartCone_isLimit (A := U.X a) R c hc j g).some
  let d' := d.whisker rep.op
  have hd' : IsLimit d' := (Functor.Initial.isLimitWhiskerEquiv rep.op d).symm hd
  let : ∀ x, IsAffine ((rep.op ⋙ D).rightOp.obj x).unop := by
    intro x
    change IsAffine (pullback (Spec.map (R.map (homOfLE (rep.obj x).property))) g)
    infer_instance
  let dΓ := Scheme.Γ.mapCocone (coconeRightOpOfCone d')
  have hdΓ : IsColimit dΓ :=
    isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone _ hd')
  let β : colimit F ≅ Γ(d.pt, ⊤) :=
    (colimit.isColimit F).coconePointUniqueUpToIso hdΓ
  have hβ (x) : colimit.ι F x ≫ β.hom = (d.π.app (op (rep.obj x))).appTop :=
    (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hdΓ x
  let b₀ : Over.mk (c.π.app (op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) := Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)
  let z : (U.pullback₁ q₀).X a ≅ d.pt := chartBaseChangeIso f b₀ U a
  let : IsAffine d.pt :=
    @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      c.pt (U.X a) (Spec (R.obj j)) (c.π.app (op j)) g
      (inferInstance : IsAffine c.pt) ha inferInstance
  have hz : IsAffine ((U.pullback₁ q₀).X a) := IsAffine.of_isIso z.hom
  let ρ₀ := CategoryTheory.Iso.commRingCatIsoToRingEquiv (β ≪≫ (Scheme.Γ.mapIso z.op))
  refine ⟨hz, ρ₀, ?_, ?_⟩
  · intro b
    have hs : z.hom ≫ d.π.app (op kₜ) ≫ s = U.pullbackHom q₀ a := by
      change z.hom ≫ ((Over.pullback g).map
        (Over.homMk (U := Over.mk (c.π.app (op j)))
          (V := Over.mk (Spec.map (R.map (homOfLE kₜ.property))))
          (c.π.app (op kₜ.val)) (c.w _))).left ≫ pullback.snd _ _ = _
      simp only [Over.pullback, Over.homMk_left, pullback.lift_snd]
      exact chartBaseChangeIso_hom_snd f b₀ U a
    have hsΓ := congrArg Scheme.Hom.appTop hs
    simp only [Scheme.Hom.comp_appTop] at hsΓ
    change (colimit.ι F t ≫ β.hom ≫ z.hom.appTop).hom (s.appTop b) = _
    rw [← Category.assoc, hβ]
    exact ConcreteCategory.congr_hom hsΓ b
  · intro x htx k hjk q p q₀ w r r₁ Uk V v
    let bx : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) ⟶
        Over.mk (Spec.map (R.map (homOfLE hij))) := Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (show Spec.map (R.map (homOfLE hjk)) ≫ Spec.map (R.map (homOfLE hij)) =
        Spec.map (R.map (homOfLE (hij.trans hjk))) from
        by rw [← Spec.map_comp, ← R.map_comp]; rfl)
    let e : Uk.X a ≅ D.obj (op (rep.obj x)) := chartBaseChangeIso f bx U a
    let : IsAffine (D.obj (op (rep.obj x))) := by
      change IsAffine (pullback (Spec.map (R.map (homOfLE hjk))) g)
      infer_instance
    let ρₓ := CategoryTheory.Iso.commRingCatIsoToRingEquiv (Scheme.Γ.mapIso e.op)
    refine ⟨ρₓ, ?_, IsAffine.of_isIso e.hom, ?_⟩
    · intro b
      have he : e.hom ≫ D.map (rep.map (homOfLE htx)).op ≫ s =
          U.pullbackHom q a := by
        change e.hom ≫ ((Over.pullback g).map
          ((upperTailSpectrumOver R j).map (rep.map (homOfLE htx)).op)).left ≫
          pullback.snd _ _ = _
        simp only [Over.pullback, Over.homMk_left, pullback.lift_snd]
        exact chartBaseChangeIso_hom_snd f bx U a
      have heΓ := congrArg Scheme.Hom.appTop he
      simp only [Scheme.Hom.comp_appTop] at heΓ
      exact ConcreteCategory.congr_hom heΓ b
    · intro b
      have hp : v ≫ z.hom ≫ d.π.app (op (rep.obj x)) =
          Uk.pullbackHom p a ≫ e.hom := by
        apply pullback.hom_ext
        · change v ≫ z.hom ≫ ((Over.pullback g).map
            (Over.homMk (U := Over.mk (c.π.app (op j)))
              (V := Over.mk (Spec.map (R.map (homOfLE hjk))))
              (c.π.app (op k)) (c.w _))).left ≫ pullback.fst _ _ = _
          simp only [Over.pullback, Over.homMk_left, Category.assoc, pullback.lift_fst]
          rw [← Category.assoc z.hom]
          erw [chartBaseChangeIso_hom_fst f b₀ U a]
          simp only [Category.assoc]
          rw [← Category.assoc v]
          erw [pullback.lift_fst]
          erw [chartBaseChangeIso_hom_fst f bx U a]
          erw [Uk.pullbackHom_map_assoc p a]
          simp only [p, baseChangeMap, pullback.lift_snd, Over.homMk_left]
          rfl
        · change v ≫ z.hom ≫ ((Over.pullback g).map
            (Over.homMk (U := Over.mk (c.π.app (op j)))
              (V := Over.mk (Spec.map (R.map (homOfLE hjk))))
              (c.π.app (op k)) (c.w _))).left ≫ pullback.snd _ _ = _
          simp only [Over.pullback, Over.homMk_left, Category.assoc, pullback.lift_snd]
          erw [chartBaseChangeIso_hom_snd f b₀ U a]
          erw [chartBaseChangeIso_hom_snd f bx U a]
          exact pullback.lift_snd _ _ _
      exact section_colimit_compatibility F β z e x rfl
        (d.π.app (op (rep.obj x))) (by simpa only [eqToHom_refl, Category.id_comp] using hβ x)
        v (Uk.pullbackHom p a) hp b

end AlgebraicGeometry
