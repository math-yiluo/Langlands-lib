/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.RingTheory.Jacobson.Ring
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Spreading out morphisms to projective space with affine charts

Let `K / k` be a field extension and `X` a quasi-compact quasi-separated `k`-scheme. A morphism
`ψ : X_K ⟶ ℙ(γ; K)` over `K` such that the preimages of the standard opens are affine is defined,
together with the affineness of these preimages, over a finitely generated `k`-subalgebra `A` of
`K`; specialising at a maximal ideal of `A` gives such a morphism over a finite extension `k'`
of `k` (Zariski's lemma). This is the limit argument in the proof of Stacks, Tag 0BDE.

## Main statements

- `CommRingCat.isColimitFGSubalgebraCocone`: a `k`-algebra is the filtered colimit of its finitely
  generated `k`-subalgebras.
- `AlgebraicGeometry.exists_finite_isAffineOpen_preimage_standardOpen`: the spreading out.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section


namespace AlgebraicGeometry

open CommRingCat

lemma ProjectiveSpace.map_preimage_standardOpen {n : Type u} {S T : Scheme.{u}} (h : S ⟶ T)
    (i : n) : ProjectiveSpace.map n h ⁻¹ᵁ ProjectiveSpace.standardOpen n T i =
      ProjectiveSpace.standardOpen n S i := by
  rw [ProjectiveSpace.standardOpen, ← Scheme.Hom.comp_preimage, ProjectiveSpace.map_toProjInt]
  rfl

lemma ProjectiveSpace.liftBaseChange_preimage_standardOpen {n : Type u} {X S T : Scheme.{u}}
    {g : X ⟶ S} (a : T ⟶ X) (b : T ⟶ ℙ(n; S)) (w : a ≫ g = b ≫ ℙ(n; S) ↘ S) (i : n) :
    ProjectiveSpace.liftBaseChange a b w ⁻¹ᵁ ProjectiveSpace.standardOpen n X i =
      b ⁻¹ᵁ ProjectiveSpace.standardOpen n S i := by
  rw [ProjectiveSpace.standardOpen, ProjectiveSpace.standardOpen, ← Scheme.Hom.comp_preimage,
    ProjectiveSpace.liftBaseChange_toProjInt, Scheme.Hom.comp_preimage]

/-- **Spreading out to a finite field extension.** Let `K / k` be a field extension, `X` a
quasi-compact quasi-separated `k`-scheme and `ψ : X_K ⟶ ℙ(γ; K)` a morphism over `K` with affine
preimages of the standard opens. Then there are a finite extension `k'` of `k` and a morphism
`X_{k'} ⟶ ℙ(γ; k')` with affine preimages of the standard opens. -/
theorem exists_finite_isAffineOpen_preimage_standardOpen {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X]
    [QuasiSeparatedSpace X] {γ : Type u} [Finite γ]
    (ψ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ ℙ(γ; Spec (.of K)))
    (hψo : ψ ≫ ℙ(γ; Spec (.of K)) ↘ Spec (.of K) = pullback.snd _ _)
    (hψ : ∀ c, IsAffineOpen (ψ ⁻¹ᵁ ProjectiveSpace.standardOpen γ (Spec (.of K)) c)) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (Y : Scheme.{u}) (π : Y ⟶ X) (q : Y ⟶ Spec (.of k'))
      (_ : IsPullback π q f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
      (ψ' : Y ⟶ ℙ(γ; Spec (.of k'))),
        ∀ c, IsAffineOpen (ψ' ⁻¹ᵁ ProjectiveSpace.standardOpen γ (Spec (.of k')) c) := by
  classical
  have := Fintype.ofFinite γ
  let I := {A : Subalgebra k K // A.FG}
  have : Nonempty I := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirectedOrder I := ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
    show A.1 ≤ A.1 ⊔ B.1 from le_sup_left, show B.1 ≤ A.1 ⊔ B.1 from le_sup_right⟩⟩
  let D : Iᵒᵖ ⥤ Scheme.{u} := (fgSubalgebraDiagramOf k K).op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (fgSubalgebraCoconeOf k K).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (isColimitFGSubalgebraCocone k K).op
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  let i₀ : Iᵒᵖ := Opposite.op ⟨⊥, Subalgebra.fg_bot⟩
  let ρ : CommRingCat.of (⊥ : Subalgebra k K) ≅ CommRingCat.of k :=
    (Algebra.botEquiv k K).toRingEquiv.toCommRingCatIso
  let p : X ⟶ D.obj i₀ := f ≫ Spec.map ρ.hom
  have hring : (CommRingCat.ofHom (⊥ : Subalgebra k K).val.toRingHom :
      CommRingCat.of (⊥ : Subalgebra k K) ⟶ .of K) =
        ρ.hom ≫ CommRingCat.ofHom (algebraMap k K) := by
    ext x
    obtain ⟨r, rfl⟩ := (Algebra.botEquiv k K).symm.surjective x
    simp [ρ]
  have hρK : c.π.app i₀ = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Spec.map ρ.hom := by
    rw [← Spec.map_comp, ← hring]
    rfl
  -- the base change `X_K` as the limit of the `X_A`
  have H1 : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd _ _) p (c.π.app i₀) := by
    rw [hρK]
    exact (IsPullback.of_hasPullback _ _).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (Spec.map ρ.hom)) (by simp) (by simp) (by simp [p]) (by simp)
  let eX := (IsPullback.of_hasPullback p (c.π.app i₀)).isoIsPullback _ _ H1
  let D' := baseChangeDiagram D p
  let c' := baseChangeCone D c p
  have hc' : IsLimit c' := isLimitBaseChangeCone D c p hc
  have : IsNoetherianRing (⊥ : Subalgebra k K) :=
    isNoetherianRing_of_ringEquiv k (Algebra.botEquiv k K).symm.toRingEquiv
  have : IsLocallyNoetherian (D.obj i₀) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of (⊥ : Subalgebra k K))))
  have : LocallyOfFinitePresentation (ℙ(γ; D.obj i₀) ↘ D.obj i₀) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  let a : c'.pt ⟶ ℙ(γ; D.obj i₀) := eX.hom ≫ ψ ≫ ProjectiveSpace.map γ (c.π.app i₀)
  have ha : c'.π ≫ baseChangeDiagramStructure D p =
      (Functor.const _).map (a ≫ ℙ(γ; D.obj i₀) ↘ D.obj i₀) := by
    ext j
    simp only [NatTrans.comp_app, baseChangeDiagramStructure_app, Functor.const_map_app, a,
      Category.assoc, ProjectiveSpace.map_over, reassoc_of% hψo]
    rw [baseChangeCone_π_app_fst_assoc, pullback.condition, IsPullback.isoIsPullback_hom_snd_assoc]
  obtain ⟨j, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D'
    (baseChangeDiagramStructure D p) (ℙ(γ; D.obj i₀) ↘ D.obj i₀) c' hc' a ha
  -- the preimages of the standard opens become affine at a later stage
  have hWaff (cc : γ) : IsAffineOpen
      (c'.π.app j ⁻¹ᵁ (g ⁻¹ᵁ ProjectiveSpace.standardOpen γ (D.obj i₀) cc)) := by
    rw [← Scheme.Hom.comp_preimage, hg₁]
    simp only [a, Scheme.Hom.comp_preimage, ProjectiveSpace.map_preimage_standardOpen]
    exact (hψ cc).preimage eX.hom
  have : IsAffine (D.obj i₀) := inferInstanceAs (IsAffine (Spec _))
  have : QuasiSeparatedSpace ℙ(γ; D.obj i₀) :=
    quasiSeparatedSpace_of_quasiSeparated (ℙ(γ; D.obj i₀) ↘ D.obj i₀)
  have hWc (cc : γ) :=
    QuasiCompact.isCompact_preimage (f := g) _ (ProjectiveSpace.standardOpen γ _ cc).isOpen
      (ProjectiveSpace.isAffineOpen_standardOpen γ (D.obj i₀) cc).isCompact
  have hlater (cc : γ) := exists_isAffineOpen_preimage hc' (i₀ := j) (hWc cc) (hWaff cc)
  choose j' hj' using hlater
  have hthin {a b : Over i₀} (u v : a ⟶ b) : u = v :=
    Over.OverMorphism.ext (Subsingleton.elim _ _)
  obtain ⟨J, hJ⟩ := IsCofiltered.inf_objs_exists
    (insert j (Finset.univ.image fun cc ↦ (j' cc).left))
  let hJj : J ⟶ j := (hJ (Finset.mem_insert_self _ _)).some
  have hJaff (cc : γ) : IsAffineOpen
      (D'.map hJj ⁻¹ᵁ (g ⁻¹ᵁ ProjectiveSpace.standardOpen γ (D.obj i₀) cc)) := by
    let u : J ⟶ (j' cc).left := (hJ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ cc)))).some
    rw [hthin hJj (u ≫ (j' cc).hom), Functor.map_comp, Scheme.Hom.comp_preimage]
    exact (hj' cc).preimage _
  -- specialise at a maximal ideal of the stage `A`
  let A : Subalgebra k K := J.left.unop.1
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let k' := A ⧸ m
  let : Field k' := Ideal.Quotient.field m
  have : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType _).mp J.left.unop.2
  have : Algebra.FiniteType k k' :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  have : Module.Finite k k' := finite_of_finite_type_of_isJacobsonRing k k'
  let φ : CommRingCat.of A ⟶ CommRingCat.of k' := CommRingCat.ofHom (Ideal.Quotient.mk m)
  have hbot : Spec.map φ ≫ D.map J.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ Spec.map ρ.hom := by
    rw [← Spec.map_comp]
    change Spec.map φ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    ext x
    obtain ⟨r, rfl⟩ := (Algebra.botEquiv k K).symm.surjective x
    simp only [ρ, φ, Functor.op_obj, Functor.op_map, fgSubalgebraDiagramOf_map,
      AlgHom.toRingHom_eq_coe, Quiver.Hom.unop_op, CommRingCat.hom_comp,
      ConcreteCategory.hom_ofHom, Algebra.botEquiv_symm_apply, RingHom.coe_comp,
      Function.comp_apply]
    erw [(Algebra.botEquiv k K).commutes r]
    rfl
  let XJ := pullback p (D.map J.hom)
  let Y := pullback (pullback.snd p (D.map J.hom)) (Spec.map φ)
  have hpaste := (IsPullback.of_hasPullback (pullback.snd p (D.map J.hom)) (Spec.map φ)).paste_horiz
    (IsPullback.of_hasPullback p (D.map J.hom))
  have HY : IsPullback (pullback.fst _ _ ≫ pullback.fst p (D.map J.hom))
      (pullback.snd (pullback.snd p (D.map J.hom)) (Spec.map φ)) f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
    rw [hbot] at hpaste
    exact hpaste.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (Spec.map ρ.hom)).symm
      (by simp) (by simp) (by simp [p]) (by simp)
  -- the morphism over `k'`
  let gJ : XJ ⟶ ℙ(γ; D.obj i₀) := D'.map hJj ≫ g
  have hw : pullback.snd (pullback.snd p (D.map J.hom)) (Spec.map φ) ≫ (Spec.map φ ≫ D.map J.hom) =
      (pullback.fst _ _ ≫ gJ) ≫ ℙ(γ; D.obj i₀) ↘ D.obj i₀ := by
    simp only [gJ, Category.assoc, hg₂, baseChangeDiagramStructure_app]
    rw [baseChangeDiagram_map_fst_assoc, ← pullback.condition_assoc, pullback.condition]
  refine ⟨k', inferInstance, inferInstance, inferInstance, Y, _, _, HY,
    ProjectiveSpace.liftBaseChange _ _ hw, fun cc ↦ ?_⟩
  rw [ProjectiveSpace.liftBaseChange_preimage_standardOpen, Scheme.Hom.comp_preimage]
  have : IsAffineHom (pullback.fst (pullback.snd p (D.map J.hom)) (Spec.map φ)) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ (isAffineHom_of_isAffine (Spec.map φ))
  exact (hJaff cc).preimage _

end AlgebraicGeometry
