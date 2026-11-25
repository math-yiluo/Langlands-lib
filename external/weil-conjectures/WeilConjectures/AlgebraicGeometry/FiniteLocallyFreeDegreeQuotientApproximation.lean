/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.DescendFiniteLocallyFree

/-! # Finite locally free degree descent along quotient ideals -/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Hom

private abbrev FGIdeals {A : CommRingCat.{u}} (I : Ideal A) :=
  {J : Ideal A // J ≤ I ∧ J.FG}

private instance {A : CommRingCat.{u}} (I : Ideal A) : OrderBot (FGIdeals I) where
  bot := ⟨⊥, bot_le, Submodule.fg_bot⟩
  bot_le _ := Subtype.coe_le_coe.mp bot_le

private instance {A : CommRingCat.{u}} (I : Ideal A) : IsDirectedOrder (FGIdeals I) where
  directed a b := ⟨⟨a.1 ⊔ b.1, sup_le a.2.1 b.2.1, Submodule.FG.sup a.2.2 b.2.2⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

private def quotientMap {A : CommRingCat.{u}} {I J : Ideal A} (h : I ≤ J) :
    A ⧸ I →+* A ⧸ J :=
  Ideal.quotientMap J (RingHom.id A) (by simpa using h)

private def quotientDiagram {A : CommRingCat.{u}} (I : Ideal A) :
    FGIdeals I ⥤ CommRingCat.{u} where
  obj J := .of (A ⧸ J.1)
  map a := CommRingCat.ofHom (quotientMap (leOfHom a))
  map_id J := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [quotientMap]
  map_comp a b := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [quotientMap]

private def quotientCocone {A : CommRingCat.{u}} (I : Ideal A) :
    Cocone (quotientDiagram I) where
  pt := .of (A ⧸ I)
  ι :=
    { app J := CommRingCat.ofHom (quotientMap J.2.1)
      naturality a b t := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp [quotientDiagram, quotientMap] }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def quotientIsColimit {A : CommRingCat.{u}} (I : Ideal A) :
    IsColimit (quotientCocone I) := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A))
  let m (s : Cocone (quotientDiagram I)) : A →+* s.pt :=
    ((s.ι.app ⊥).hom).comp q.hom
  have hkill (s : Cocone (quotientDiagram I)) : I ≤ RingHom.ker (m s) := by
    intro x hx
    let J : FGIdeals I := ⟨Ideal.span {x}, Ideal.span_le.mpr (by simpa using hx),
      Submodule.fg_span_singleton x⟩
    have h := ConcreteCategory.congr_hom
      (s.w (homOfLE (bot_le : (⊥ : FGIdeals I) ≤ J))) (Ideal.Quotient.mk ⊥ x)
    change (s.ι.app ⊥).hom (Ideal.Quotient.mk ⊥ x) = 0
    have hz : Ideal.Quotient.mk J.1 x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    change (s.ι.app J).hom (Ideal.Quotient.mk J.1 x) =
      (s.ι.app ⊥).hom (Ideal.Quotient.mk ⊥ x) at h
    rw [hz, map_zero] at h
    exact h.symm
  refine
    { desc := fun s ↦ CommRingCat.ofHom (Ideal.Quotient.lift I (m s) (hkill s))
      fac := ?_
      uniq := ?_ }
  · intro s J
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h := ConcreteCategory.congr_hom
      (s.w (homOfLE (bot_le : (⊥ : FGIdeals I) ≤ J))) (Ideal.Quotient.mk ⊥ x)
    change (s.ι.app J).hom (Ideal.Quotient.mk J.1 x) =
      (s.ι.app ⊥).hom (Ideal.Quotient.mk ⊥ x) at h
    change (s.ι.app ⊥).hom (Ideal.Quotient.mk ⊥ x) =
      (s.ι.app J).hom (Ideal.Quotient.mk J.1 x)
    exact h.symm
  · intro s n hn
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h := ConcreteCategory.congr_hom (hn (⊥ : FGIdeals I))
      (Ideal.Quotient.mk ⊥ x)
    change n.hom (Ideal.Quotient.mk I x) =
      (s.ι.app ⊥).hom (Ideal.Quotient.mk ⊥ x) at h
    exact h

private def degreeProperty (r : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ f.IsFiniteLocallyFreeOfDegree r

private instance (r : ℕ) : (degreeProperty r).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    change g.IsFiniteLocallyFreeOfDegree r at hg
    have := hg
    have : IsFinite g' := MorphismProperty.of_isPullback (P := @IsFinite) sq inferInstance
    have : Flat g' := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
    have : LocallyOfFinitePresentation g' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq inferInstance
    have : g'.IsFiniteLocallyFree := ⟨⟩
    exact ⟨fun x ↦ (g.fiberDegree_of_isPullback sq x).trans (hg.fiberDegree_eq _)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem overPullback_degree_iff {X S T R : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (a : R ⟶ T) (r : ℕ) :
    (((Over.pullback a).map
      (Over.homMk (pullback.snd f g) : Over.mk (pullback.snd f g) ⟶
        Over.mk (𝟙 T))).left).IsFiniteLocallyFreeOfDegree r ↔
      (pullback.snd f (a ≫ g)).IsFiniteLocallyFreeOfDegree r := by
  apply (degreeProperty r).arrow_mk_iso_iff
  refine Arrow.isoMk (pullbackLeftPullbackSndIso f g a)
    (asIso (pullback.snd (𝟙 T) a)) ?_
  simp [Over.pullback_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- Finite local freeness of fixed degree after quotienting descends to a finitely
generated subideal of the quotient ideal.

Source: Stacks Project, More on Morphisms, Tag 07RZ, proof, second paragraph,
and Limits, Tag 06AC.
(blueprint: lem-weil-pbc-finite-locally-free-degree-quotient-approximation).

Proof: Base change f along g. Its source is quasi-compact, since f is quasi-compact
and Spec A is quasi-compact, and quasi-separated, since f is separated. The base
change is locally of finite presentation. Order the finitely generated subideals
J of I by inclusion. This is a nonempty directed set: zero is an index and sums
provide upper bounds. The quotient rings A/J form a filtered diagram with colimit
A/I: every class is represented by an element of A, and any relation killed in
A/I is killed at the stage generated by its element of I. Therefore Spec(A/I) is
the inverse limit of Spec(A/J), with affine transition maps. Apply fixed-degree
finite locally free descent (Tag 06AC) to the base change of f along g. It gives
one finitely generated J contained in I at which that base change is finite
locally free of degree r. Pullback associativity identifies this morphism with
pullback.snd f (Spec.map (Ideal.Quotient.mk J) followed by g), as asserted.
The empty quotient (I = top), I = zero, the zero ring, and r = zero are included;
descent is applied to qcqs schemes, without any nonemptiness assumption.
-/
theorem exists_fg_subideal_isFiniteLocallyFreeOfDegree
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [LocallyOfFinitePresentation f] [IsSeparated f]
    (A : CommRingCat.{u}) (g : Spec A ⟶ S) (I : Ideal A) (r : ℕ)
    (hI : (pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g)).IsFiniteLocallyFreeOfDegree r) :
    ∃ J : Ideal A, J ≤ I ∧ J.FG ∧
      IsFiniteLocallyFreeOfDegree
        (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g)) r := by
  classical
  let Q := quotientDiagram I
  let D := Q.op ⋙ Scheme.Spec
  have : ∀ {i j : (FGIdeals I)ᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) :=
    fun a ↦ inferInstanceAs (IsAffineHom (Spec.map (Q.map a.unop)))
  let c := Scheme.Spec.mapCone (quotientCocone I).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (quotientIsColimit I).op
  let i₀ : FGIdeals I := ⊥
  let g₀ : D.obj (op i₀) ⟶ S :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A))) ≫ g
  let X₀ : Over (D.obj (op i₀)) := Over.mk (pullback.snd f g₀)
  let Y₀ : Over (D.obj (op i₀)) := Over.mk (𝟙 _)
  let f₀ : X₀ ⟶ Y₀ := Over.homMk (pullback.snd f g₀)
  have : CompactSpace (D.obj (op i₀)) := inferInstanceAs (CompactSpace (Spec _))
  have : QuasiSeparatedSpace (D.obj (op i₀)) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec _))
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj (op i₀)))
  have : QuasiSeparatedSpace Y₀.left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (op i₀)))
  have : CompactSpace X₀.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g₀)
  have : QuasiSeparatedSpace X₀.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g₀)
  have : LocallyOfFinitePresentation f₀.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f g₀))
  have hcomp : c.π.app (op i₀) ≫ g₀ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g := by
    change Spec.map (CommRingCat.ofHom (quotientMap (bot_le : (⊥ : Ideal A) ≤ I))) ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ⊥)) ≫ g) = _
    rw [← Spec.map_comp_assoc]
    congr 2
  have hd : (((Over.pullback (c.π.app (op i₀))).map f₀).left).IsFiniteLocallyFreeOfDegree r :=
    (overPullback_degree_iff f g₀ _ r).2 (hcomp.symm ▸ hI)
  obtain ⟨J, hJ, hfree⟩ :=
    (descend_finite_locally_free D c hc i₀ X₀ Y₀ f₀ hd.toIsFiniteLocallyFree).2 r hd
  refine ⟨J.1, J.2.1, J.2.2, ?_⟩
  have hstage := (overPullback_degree_iff f g₀ (D.map (homOfLE hJ).op) r).1 hfree
  have hcompJ : D.map (homOfLE hJ).op ≫ g₀ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ g := by
    change Spec.map (CommRingCat.ofHom (quotientMap (bot_le : (⊥ : Ideal A) ≤ J.1))) ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ⊥)) ≫ g) = _
    rw [← Spec.map_comp_assoc]
    congr 2
  exact hcompJ ▸ hstage

end AlgebraicGeometry.Scheme.Hom
