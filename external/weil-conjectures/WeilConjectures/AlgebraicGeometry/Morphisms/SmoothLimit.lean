/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Smoothness descends to a stage of a limit

Let `{Dⱼ}` be a cofiltered system of affine schemes with affine transition maps and
let `Y` be of finite presentation over a stage `Dᵢ`. If the base change of `Y` to `lim Dⱼ` is
smooth, then so is the base change of `Y` to some stage `Dⱼ` (EGA IV 17.7.8).

## Main statements

- `Algebra.Smooth.exists_of_isColimit`: a smooth algebra over a filtered colimit of rings is the
  base change of a smooth algebra over a stage.
- `AlgebraicGeometry.Scheme.exists_smooth_isPullback_of_isAffine`: a smooth affine scheme over
  the limit is the base change of a smooth affine scheme over a stage.
- `AlgebraicGeometry.Scheme.exists_smooth_pullback_snd_of_isLimit`: the main result. The affine
  case compares the given model with a smooth model using
  `AlgebraicGeometry.exists_iso_of_isPullback`; the general case covers `Y` by finitely many
  affine opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

/-- **Smooth algebras over a filtered colimit of rings descend to a stage.** Let `R = colim Rⱼ`
be a filtered colimit of commutative rings and `B` a smooth `R`-algebra. Then there is a stage `j`
and a smooth `Rⱼ`-algebra `Bⱼ` with `B ≃ₐ[R] R ⊗[Rⱼ] Bⱼ`. -/
theorem Algebra.Smooth.exists_of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {s : Cocone F} (hs : IsColimit s)
    (B : Type u) [CommRing B] [Algebra s.pt B] [Algebra.Smooth s.pt B] :
    ∃ (j : J) (Bj : Type u) (_ : CommRing Bj) (_ : Algebra (F.obj j) Bj),
      Algebra.Smooth (F.obj j) Bj ∧
      letI : Algebra (F.obj j) s.pt := (s.ι.app j).hom.toAlgebra
      Nonempty (B ≃ₐ[s.pt] s.pt ⊗[F.obj j] Bj) := by
  classical
  let A : Type u := s.pt
  let : Algebra (ULift.{u} ℤ) A :=
    ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : ∀ i, Algebra (ULift.{u} ℤ) (F.obj i) := fun i ↦
    ((Int.castRingHom (F.obj i)).comp ULift.ringEquiv.toRingHom).toAlgebra
  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ :=
    Algebra.Smooth.exists_subalgebra_fg (ULift.{u} ℤ) A B
  have : Algebra.FiniteType (ULift.{u} ℤ) A₀ := A₀.fg_iff_finiteType.mp hfg
  let R := CommRingCat.of (ULift.{u} ℤ)
  let α : (Functor.const J).obj R ⟶ F :=
    { app := fun i ↦ CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (F.obj i))
      naturality := by
        intro i k h
        ext ⟨x⟩
        change (x : F.obj k) = (F.map h).hom (x : F.obj i)
        simp }
  let j : R ⟶ CommRingCat.of A₀ := CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A₀)
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have hj : j.hom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨i, g, _, hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R F α j s hs hj
      (CommRingCat.ofHom A₀.val.toRingHom) (by
        intro i
        ext ⟨x⟩
        change (x : A) = (s.ι.app i).hom (x : F.obj i)
        exact (map_intCast _ x).symm)
  let : Algebra A₀ (F.obj i) := g.hom.toAlgebra
  let : Algebra (F.obj i) A := (s.ι.app i).hom.toAlgebra
  have : IsScalarTower A₀ (F.obj i) A :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hg)
  refine ⟨i, F.obj i ⊗[A₀] B₀, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨e.trans (Algebra.TensorProduct.cancelBaseChange A₀ (F.obj i) A A B₀).symm⟩

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- **A smooth affine scheme over the limit has a smooth model at a stage.** Let `{Dⱼ}` be a
cofiltered system of affine schemes with affine transition maps and `g : X ⟶ lim Dⱼ` a smooth
morphism from an affine scheme. Then `g` is the base change of a smooth morphism from an affine
scheme to some stage `Dⱼ`. -/
theorem Scheme.exists_smooth_isPullback_of_isAffine {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt) [Smooth g] :
    ∃ (j : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj j) (h : X ⟶ Y),
      IsAffine Y ∧ Smooth p ∧ IsPullback h g p (c.π.app j) := by
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ hc i₀
  have : IsAffine c.pt := isAffine_of_isAffineHom (c.π.app i₀)
  let s := Scheme.Γ.mapCocone c.op
  let hs : IsColimit s := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let : Algebra Γ(c.pt, ⊤) Γ(X, ⊤) := g.appTop.hom.toAlgebra
  have hsmooth : Algebra.Smooth Γ(c.pt, ⊤) Γ(X, ⊤) :=
    ((HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := g)).mp ‹_›).toAlgebra
  let : Algebra s.pt Γ(X, ⊤) := g.appTop.hom.toAlgebra
  have : Algebra.Smooth s.pt Γ(X, ⊤) := hsmooth
  obtain ⟨⟨j⟩, Bj, _, alg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_of_isColimit hs Γ(X, ⊤)
  let : Algebra Γ(D.obj j, ⊤) Bj := alg
  have : Algebra.Smooth Γ(D.obj j, ⊤) Bj := hsm
  let : Algebra Γ(D.obj j, ⊤) Γ(c.pt, ⊤) := (c.π.app j).appTop.hom.toAlgebra
  let e' : Γ(X, ⊤) ≃ₐ[Γ(c.pt, ⊤)] Γ(c.pt, ⊤) ⊗[Γ(D.obj j, ⊤)] Bj := e
  let φ : Γ(D.obj j, ⊤) ⟶ CommRingCat.of Bj :=
    CommRingCat.ofHom (algebraMap Γ(D.obj j, ⊤) Bj)
  have : IsAffine (((Functor.const I).obj c.pt).obj j) := ‹IsAffine c.pt›
  have H := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(D.obj j, ⊤) Γ(c.pt, ⊤) Bj)).flip
  let e₁ : X ≅ Spec (CommRingCat.of (Γ(c.pt, ⊤) ⊗[Γ(D.obj j, ⊤)] Bj)) :=
    X.isoSpec ≪≫ Scheme.Spec.mapIso e'.symm.toRingEquiv.toCommRingCatIso.op
  refine ⟨j, Spec (CommRingCat.of Bj), Spec.map φ ≫ (D.obj j).isoSpec.inv,
    e₁.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom),
    inferInstance, ?_, ?_⟩
  · have : Smooth (Spec.map φ) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance
  · refine H.of_iso' e₁ (Iso.refl _) c.pt.isoSpec (D.obj j).isoSpec (by simp) ?_
      (by simp; rfl) ?_
    · simp only [e₁, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
        Quiver.Hom.unop_op, Category.assoc, ← Spec.map_comp]
      rw [← Scheme.isoSpec_hom_naturality]
      congr 2
      ext x
      exact e'.symm.commutes x
    · exact Scheme.isoSpec_hom_naturality (X := c.pt) (Y := D.obj j) (c.π.app j)

/-- Smoothness of a base change persists under further base change. -/
lemma smooth_pullback_snd_comp {Y Z T T' : Scheme.{u}} (q : Y ⟶ Z) (a : T ⟶ Z) (b : T' ⟶ T)
    [Smooth (pullback.snd q a)] : Smooth (pullback.snd q (b ≫ a)) :=
  (MorphismProperty.cancel_left_of_respectsIso @Smooth (pullbackLeftPullbackSndIso q a b).hom
    _).mp (by rw [pullbackLeftPullbackSndIso_hom_snd]; infer_instance)

/-- The restriction of the base change `Y ×_Z T ⟶ T` to the preimage of an open `U ⊆ Y` is
smooth if and only if the base change `U ×_Z T ⟶ T` is smooth. -/
lemma smooth_preimage_ι_comp_pullback_snd_iff {Y Z T : Scheme.{u}} (q : Y ⟶ Z) (a : T ⟶ Z)
    (U : Y.Opens) :
    Smooth (((pullback.fst q a) ⁻¹ᵁ U).ι ≫ pullback.snd q a) ↔
      Smooth (pullback.snd (U.ι ≫ q) a) := by
  let e : pullback (U.ι ≫ q) a ≅ (pullback.fst q a) ⁻¹ᵁ U :=
    (pullbackRightPullbackFstIso q a U.ι).symm ≪≫ pullbackSymmetry _ _ ≪≫
      pullbackRestrictIsoRestrict (pullback.fst q a) U
  have he : e.hom ≫ ((pullback.fst q a) ⁻¹ᵁ U).ι ≫ pullback.snd q a =
      pullback.snd (U.ι ≫ q) a := by
    simp [e]
  rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom, he]

/-- Affine case of `AlgebraicGeometry.Scheme.exists_smooth_pullback_snd_of_isLimit`. -/
lemma Scheme.exists_smooth_pullback_snd_of_isLimit_of_isAffine {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {i : I} {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ D.obj i) [LocallyOfFinitePresentation p]
    [Smooth (pullback.snd p (c.π.app i))] :
    ∃ (j : I) (f : j ⟶ i), Smooth (pullback.snd p (D.map f)) := by
  have := isAffineHom_π_app _ _ hc i
  obtain ⟨j, Y', p', h, hY', hp', H⟩ :=
    exists_smooth_isPullback_of_isAffine hc (pullback.snd p (c.π.app i))
  let k := IsCofiltered.min i j
  let f₁ : k ⟶ i := IsCofiltered.minToLeft i j
  let f₂ : k ⟶ j := IsCofiltered.minToRight i j
  have H₁ := isPullback_isPullbackLift f₁ (IsPullback.of_hasPullback p (c.π.app i))
  have H₂ := isPullback_isPullbackLift f₂ H
  obtain ⟨k', f', hk'⟩ := exists_iso_of_isPullback hc H₁ H₂
  obtain ⟨e, he, -⟩ := hk' (IsPullback.of_hasPullback _ (D.map f'))
    (isPullbackLift_fst f' H₁) (isPullbackLift_snd f' H₁)
    (IsPullback.of_hasPullback _ (D.map f')) (isPullbackLift_fst f' H₂)
    (isPullbackLift_snd f' H₂)
  refine ⟨k', f' ≫ f₁, ?_⟩
  have : Smooth (pullback.snd (pullback.snd p (D.map f₁)) (D.map f')) := by
    rw [← he]
    infer_instance
  rw [D.map_comp]
  exact (MorphismProperty.cancel_left_of_respectsIso @Smooth
    (pullbackLeftPullbackSndIso p _ _).hom _).mp
    (by rw [pullbackLeftPullbackSndIso_hom_snd]; exact this)

/-- **Smoothness descends to a stage of a limit.** Let `{Dⱼ}` be a cofiltered system of affine
schemes with affine transition maps, `c` a limit cone, and `p : Y ⟶ Dᵢ` of finite
presentation. If the base change `Y ×_{Dᵢ} lim Dⱼ ⟶ lim Dⱼ` is smooth, then so is
`Y ×_{Dᵢ} Dⱼ ⟶ Dⱼ` for some `j ⟶ i`. -/
theorem Scheme.exists_smooth_pullback_snd_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [Smooth (pullback.snd p (c.π.app i))] :
    ∃ (j : I) (f : j ⟶ i), Smooth (pullback.snd p (D.map f)) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have hloc (y : Y) : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U := by
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨U, hU, hyU⟩
  choose U hU hyU using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (U y : Set Y))
    (fun y ↦ (U y).isOpen) (fun y _ ↦ Set.mem_iUnion.mpr ⟨y, hyU y⟩)
  have hstage (y : Y) :
      ∃ (j : I) (f : j ⟶ i), Smooth (pullback.snd ((U y).ι ≫ p) (D.map f)) := by
    have : IsAffine (U y) := hU y
    have : Smooth (pullback.snd ((U y).ι ≫ p) (c.π.app i)) := by
      rw [← smooth_preimage_ι_comp_pullback_snd_iff]
      exact IsZariskiLocalAtSource.comp ‹_› _
    exact exists_smooth_pullback_snd_of_isLimit_of_isAffine hc _
  choose j f hf using hstage
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists (s.image fun y ↦ Over.mk (f y))
  refine ⟨S.left, S.hom, ?_⟩
  have hsup : (⨆ y : s, U y) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun y : s ↦ (pullback.fst p (D.map S.hom)) ⁻¹ᵁ U y)
    ((pullback.fst p (D.map S.hom)).iSup_preimage_eq_top hsup) fun y ↦ ?_
  rw [smooth_preimage_ι_comp_pullback_snd_iff]
  obtain ⟨g⟩ := hS (Finset.mem_image_of_mem _ y.2)
  have hg : g.left ≫ f y = S.hom := Over.w g
  have := hf y
  rw [← hg, D.map_comp]
  exact smooth_pullback_snd_comp _ _ _

end AlgebraicGeometry
