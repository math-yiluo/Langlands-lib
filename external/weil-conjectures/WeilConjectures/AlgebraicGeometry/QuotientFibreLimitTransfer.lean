/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Quotient closed fibres of directed limits

Source: Stacks Project, Tags 0GS2 and 0A0P.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem ideal_transition
    {A : Type u} [CommRing A] (I : Ideal A)
    {Λ : Type u} [Preorder Λ] (B : Λ ⥤ CommRingCat.{u})
    (α : B ⟶ (Functor.const Λ).obj (.of A)) {i j : Λ} (a : i ⟶ j) :
    I.comap (α.app i).hom ≤ (I.comap (α.app j).hom).comap (B.map a).hom := by
  intro x hx
  change (α.app j).hom ((B.map a).hom x) ∈ I
  have h := ConcreteCategory.congr_hom (α.naturality a) x
  simpa using h ▸ hx

private def quotientDiagram
    {A : Type u} [CommRing A] (I : Ideal A)
    {Λ : Type u} [Preorder Λ] (B : Λ ⥤ CommRingCat.{u})
    (α : B ⟶ (Functor.const Λ).obj (.of A)) : Λ ⥤ CommRingCat.{u} where
  obj i := .of (B.obj i ⧸ I.comap (α.app i).hom)
  map a := CommRingCat.ofHom (Ideal.quotientMap _ (B.map a).hom
    (ideal_transition I B α a))
  map_id i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  map_comp a b := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp

private def quotientProjection
    {A : Type u} [CommRing A] (I : Ideal A)
    {Λ : Type u} [Preorder Λ] (B : Λ ⥤ CommRingCat.{u})
    (α : B ⟶ (Functor.const Λ).obj (.of A)) : B ⟶ quotientDiagram I B α where
  app i := CommRingCat.ofHom (Ideal.Quotient.mk _)
  naturality i j a := by
    apply CommRingCat.hom_ext
    exact (Ideal.quotientMap_comp_mk (ideal_transition I B α a)).symm

private def quotientCoconeMap
    {A : Type u} [CommRing A] (I : Ideal A)
    {Λ : Type u} [Preorder Λ] (B : Λ ⥤ CommRingCat.{u})
    (α : B ⟶ (Functor.const Λ).obj (.of A)) :
    quotientDiagram I B α ⟶ (Functor.const Λ).obj (.of (A ⧸ I)) where
  app i := CommRingCat.ofHom (Ideal.quotientMap I (α.app i).hom le_rfl)
  naturality i j a := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.quotientMap I (α.app j).hom le_rfl
      (Ideal.quotientMap _ (B.map a).hom (ideal_transition I B α a)
        (Ideal.Quotient.mk _ x)) =
      Ideal.quotientMap I (α.app i).hom le_rfl (Ideal.Quotient.mk _ x)
    simp only [Ideal.quotientMap_mk]
    have h := ConcreteCategory.congr_hom (α.naturality a) x
    change (α.app j).hom ((B.map a).hom x) = (α.app i).hom x at h
    exact congrArg (Ideal.Quotient.mk I) h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def quotientCoconeIsColimit
    {A : Type u} [CommRing A] (I : Ideal A)
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (B : Λ ⥤ CommRingCat.{u}) (α : B ⟶ (Functor.const Λ).obj (.of A))
    (hc : IsColimit (Cocone.mk _ α)) :
    IsColimit (Cocone.mk _ (quotientCoconeMap I B α)) := by
  let q := quotientProjection I B α
  let d (s : Cocone (quotientDiagram I B α)) : Cocone B :=
    Cocone.mk s.pt (q ≫ s.ι)
  have kills (s : Cocone (quotientDiagram I B α)) :
      I ≤ RingHom.ker (hc.desc (d s)).hom := by
    intro x hx
    obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep B hc x
    have hyI : y ∈ I.comap (α.app i).hom := by
      change (α.app i).hom y ∈ I
      exact hy ▸ hx
    have h := ConcreteCategory.congr_hom (hc.fac (d s) i) y
    change (hc.desc (d s)).hom ((α.app i).hom y) =
      (s.ι.app i).hom (Ideal.Quotient.mk _ y) at h
    change (hc.desc (d s)).hom x = 0
    rw [← hy]
    change (hc.desc (d s)).hom ((α.app i).hom y) = 0
    rw [h]
    change (s.ι.app i).hom (Ideal.Quotient.mk _ y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hyI, map_zero]
  refine { desc := fun s ↦ (CommRingCat.ofHom
      (Ideal.Quotient.lift I (hc.desc (d s)).hom (kills s))), fac := ?_, uniq := ?_ }
  · intro s i
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Ideal.Quotient.lift I (hc.desc (d s)).hom (kills s))
      (Ideal.quotientMap I (α.app i).hom le_rfl (Ideal.Quotient.mk _ y)) =
      (s.ι.app i).hom (Ideal.Quotient.mk _ y)
    simp only [Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    exact ConcreteCategory.congr_hom (hc.fac (d s) i) y
  · intro s m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨i, y, rfl⟩ := Concrete.isColimit_exists_rep B hc x
    have h := ConcreteCategory.congr_hom (hm i) (Ideal.Quotient.mk _ y)
    have h' := ConcreteCategory.congr_hom (hc.fac (d s) i) y
    change m.hom (Ideal.quotientMap I (α.app i).hom le_rfl
      (Ideal.Quotient.mk _ y)) = (s.ι.app i).hom (Ideal.Quotient.mk _ y) at h
    change (hc.desc (d s)).hom ((α.app i).hom y) =
      (s.ι.app i).hom (Ideal.Quotient.mk _ y) at h'
    change m.hom (Ideal.Quotient.mk I ((α.app i).hom y)) =
      Ideal.Quotient.lift I (hc.desc (d s)).hom (kills s)
        (Ideal.Quotient.mk I ((α.app i).hom y))
    rw [Ideal.quotientMap_mk] at h
    rw [Ideal.Quotient.lift_mk]
    exact h.trans h'.symm

set_option backward.isDefEq.respectTransparency false in
/-- Taking quotients by inverse-image ideals commutes with a directed scheme limit.

Source: Stacks Project, Tag 0GS2, General case, the quotient-ring and closed-fibre
limit paragraphs; Tags 01YW and 01YX for affine inverse limits.
(blueprint: lem-weil-pbc-quotient-fibre-limit-transfer).

Proof: For each index set K_i to the inverse image of I under alpha_i. Naturality
of alpha ensures that every ring transition sends K_i into K_j. Define the quotient
ring diagram using Ideal.quotientMap. Its cocone to A/I is colimiting: represent
elements of A by stage elements, and observe that an element mapping into I already
lies in K_i. Equivalently a compatible family of maps from the quotient stages
induces a unique map from A killing I and hence a unique map from A/I. Apply Spec
and its preservation of these limits. Form D stagewise by pullback of g_i along
Spec(B_i/K_i) to Spec B_i. The naturality squares induce the transition maps and
the cone from the closed fibre of Y. Pullback universality gives the two projection
equations. Limits commute with pullbacks: compatible maps to all D_i are precisely
compatible maps to all X_i and Spec(B_i/K_i) agreeing in Spec B_i. The supplied
limit and colimit identify these with maps to Y and Spec(A/I) agreeing in Spec A,
which proves the limiting property. Each transition factors through the pullback
of X_j to X_i as a closed immersion, followed by a base change of the given affine
transition of Xs, so it is affine. Choose D_i to be the indicated pullback, so the
stage isomorphisms can be identities. This holds for I = top (empty fibres), I = 0,
noninjective alpha_i, and the zero ring; no properness is required. -/
theorem quotient_fibre_limit_transfer
    {A : Type u} [CommRing A] (I : Ideal A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (B : Λ ⥤ CommRingCat.{u}) (Xs : Λᵒᵖ ⥤ Scheme.{u})
    (g : Xs ⟶ B.op ⋙ Scheme.Spec)
    (α : B ⟶ (Functor.const Λ).obj (.of A))
    (p : (Functor.const Λᵒᵖ).obj Y ⟶ Xs)
    (hc : Nonempty (IsColimit (Cocone.mk _ α)))
    (hl : Nonempty (IsLimit (Cone.mk _ p)))
    (ha : ∀ {i j : Λᵒᵖ} (a : i ⟶ j), IsAffineHom (Xs.map a))
    (hw : ∀ i, p.app i ≫ g.app i = f ≫ Spec.map (α.app i.unop)) :
    ∃ (D : Λᵒᵖ ⥤ Scheme.{u})
      (π : (Functor.const Λᵒᵖ).obj
        (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶ D),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      (∀ {i j : Λᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)) ∧
      ∀ i : Λᵒᵖ,
        ∃ e : D.obj i ≅ pullback (g.app i) (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap (α.app i.unop).hom)))),
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ p.app i =
            (π.app i ≫ e.hom) ≫ pullback.fst (g.app i) (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I.comap (α.app i.unop).hom)))) ∧
          (π.app i ≫ e.hom) ≫ pullback.snd (g.app i) (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap (α.app i.unop).hom)))) =
            pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
              Spec.map (CommRingCat.ofHom (Ideal.quotientMap I (α.app i.unop).hom
                le_rfl)) := by
  classical
  let Q := quotientDiagram I B α
  let q := quotientProjection I B α
  let β := quotientCoconeMap I B α
  let S := Q.op ⋙ Scheme.Spec
  let t : S ⟶ B.op ⋙ Scheme.Spec := Functor.whiskerRight (NatTrans.op q) Scheme.Spec
  let r := (Scheme.Spec.mapCone (Cocone.mk _ β).op).π
  let b := (Scheme.Spec.mapCone (Cocone.mk _ α).op).π
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let hB := isLimitOfPreserves Scheme.Spec hc.some.op
  let hQ := isLimitOfPreserves Scheme.Spec (quotientCoconeIsColimit I B α hc.some).op
  have hr (i : Λᵒᵖ) : r.app i ≫ t.app i = z ≫ b.app i := by
    change Spec.map (β.app i.unop) ≫ Spec.map (q.app i.unop) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Spec.map (α.app i.unop)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let D : Λᵒᵖ ⥤ Scheme.{u} :=
    { obj i := pullback (g.app i) (t.app i)
      map a := pullback.map _ _ _ _ (Xs.map a) (S.map a) ((B.op ⋙ Scheme.Spec).map a)
        (g.naturality a).symm (t.naturality a).symm
      map_id i := by
        apply pullback.hom_ext <;> simp
      map_comp a b := by
        apply pullback.hom_ext <;> simp [Category.assoc] }
  let d₁ : D ⟶ Xs :=
    { app i := pullback.fst _ _
      naturality i j a := by simp [D] }
  let d₂ : D ⟶ S :=
    { app i := pullback.snd _ _
      naturality i j a := by simp [D] }
  have hd (i : Λᵒᵖ) : d₁.app i ≫ g.app i = d₂.app i ≫ t.app i :=
    pullback.condition
  let π : (Functor.const Λᵒᵖ).obj (pullback f z) ⟶ D :=
    { app i := pullback.lift (pullback.fst f z ≫ p.app i)
        (pullback.snd f z ≫ r.app i) (by
          rw [Category.assoc, hw i, ← Category.assoc, pullback.condition,
            Category.assoc]
          change pullback.snd f z ≫ (z ≫ b.app i) = _
          rw [← hr i, ← Category.assoc])
      naturality i j a := by
        apply pullback.hom_ext
        · simp only [Functor.const_obj_map, D, Category.assoc,
            pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
          change 𝟙 (pullback f z) ≫ pullback.fst f z ≫ p.app j =
            pullback.fst f z ≫ p.app i ≫ Xs.map a
          rw [Category.id_comp]
          have hp := p.naturality a
          change 𝟙 Y ≫ p.app j = p.app i ≫ Xs.map a at hp
          rw [Category.id_comp] at hp
          rw [hp]
        · simp only [Functor.const_obj_map, D, Category.assoc,
            pullback.map, pullback.lift_snd, pullback.lift_snd_assoc]
          change 𝟙 (pullback f z) ≫ pullback.snd f z ≫ r.app j =
            pullback.snd f z ≫ r.app i ≫ S.map a
          rw [Category.id_comp]
          have hr := r.naturality a
          change 𝟙 (Spec (.of (A ⧸ I))) ≫ r.app j = r.app i ≫ S.map a at hr
          rw [Category.id_comp] at hr
          rw [hr] }
  have hπ₁ (i : Λᵒᵖ) : π.app i ≫ d₁.app i = pullback.fst f z ≫ p.app i :=
    pullback.lift_fst _ _ _
  have hπ₂ (i : Λᵒᵖ) : π.app i ≫ d₂.app i = pullback.snd f z ≫ r.app i :=
    pullback.lift_snd _ _ _
  let hX := hl.some
  let cX (s : Cone D) : Cone Xs := (Cone.postcompose d₁).obj s
  let cQ (s : Cone D) : Cone S := (Cone.postcompose d₂).obj s
  have hcompat (s : Cone D) : hX.lift (cX s) ≫ f = hQ.lift (cQ s) ≫ z := by
    apply hB.hom_ext
    intro i
    have hw' : p.app i ≫ g.app i = f ≫ b.app i := hw i
    change (hX.lift (cX s) ≫ f) ≫ b.app i =
      (hQ.lift (cQ s) ≫ z) ≫ b.app i
    rw [Category.assoc, ← hw', ← Category.assoc, hX.fac,
      Category.assoc, ← hr i, ← Category.assoc, hQ.fac]
    change (s.π.app i ≫ d₁.app i) ≫ g.app i = (s.π.app i ≫ d₂.app i) ≫ t.app i
    simp only [Category.assoc, hd]
  let hD : IsLimit (Cone.mk _ π) :=
    { lift s := pullback.lift (hX.lift (cX s)) (hQ.lift (cQ s)) (hcompat s)
      fac s i := by
        apply pullback.hom_ext
        · change (_ ≫ π.app i) ≫ d₁.app i = s.π.app i ≫ d₁.app i
          rw [Category.assoc, hπ₁, ← Category.assoc, pullback.lift_fst]
          exact hX.fac (cX s) i
        · change (_ ≫ π.app i) ≫ d₂.app i = s.π.app i ≫ d₂.app i
          rw [Category.assoc, hπ₂, ← Category.assoc, pullback.lift_snd]
          exact hQ.fac (cQ s) i
      uniq s m hm := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          apply hX.hom_ext
          intro i
          change (m ≫ pullback.fst f z) ≫ p.app i = _
          rw [Category.assoc, ← hπ₁, ← Category.assoc, hm]
          exact (hX.fac (cX s) i).symm
        · rw [pullback.lift_snd]
          apply hQ.hom_ext
          intro i
          change (m ≫ pullback.snd f z) ≫ r.app i = _
          rw [Category.assoc, ← hπ₂, ← Category.assoc, hm]
          exact (hQ.fac (cQ s) i).symm }
  refine ⟨D, π, ⟨hD⟩, ?_, ?_⟩
  · intro i j a
    have : IsAffineHom (Xs.map a) := ha a
    have : IsAffineHom (t.app i) := by
      change IsAffineHom (Spec.map (q.app i.unop))
      infer_instance
    have : IsAffineHom (t.app j) := by
      change IsAffineHom (Spec.map (q.app j.unop))
      infer_instance
    have : IsAffineHom (d₁.app i) := by
      exact MorphismProperty.pullback_fst _ _ inferInstance
    have : IsAffineHom (d₁.app j) := by
      exact MorphismProperty.pullback_fst _ _ inferInstance
    have : IsAffineHom (D.map a ≫ d₁.app j) := by
      rw [d₁.naturality a]
      infer_instance
    exact IsAffineHom.of_comp (D.map a) (d₁.app j)
  · intro i
    refine ⟨Iso.refl _, ?_, ?_⟩
    · change pullback.fst f z ≫ p.app i = π.app i ≫ d₁.app i
      exact (hπ₁ i).symm
    · change π.app i ≫ d₂.app i = pullback.snd f z ≫ r.app i
      exact hπ₂ i

end AlgebraicGeometry.Scheme
