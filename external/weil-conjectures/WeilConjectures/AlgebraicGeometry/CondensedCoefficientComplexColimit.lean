/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram

/-! # Colimits of the canonical coefficient complexes -/

@[expose] public section
universe v u vI uI
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

private noncomputable def coequalizer_colimit
    {A : Type u} [Category.{v} A] {I : Type uI} [Category.{vI} I]
    (D₀ D₁ K : I ⥤ A) (c₀ : Cocone D₀) (c₁ : Cocone D₁) (c : Cocone K)
    (h₀ : IsColimit c₀) (h₁ : IsColimit c₁)
    (f g : c₀.pt ⟶ c₁.pt) (fᵢ gᵢ : ∀ i, D₀.obj i ⟶ D₁.obj i)
    (q : D₁ ⟶ K) (π : c₁.pt ⟶ c.pt) [Epi π] [∀ i, Epi (q.app i)]
    (hfg : f ≫ π = g ≫ π) (hq : IsColimit (Cofork.ofπ π hfg))
    (hf : ∀ i, c₀.ι.app i ≫ f = fᵢ i ≫ c₁.ι.app i)
    (hg : ∀ i, c₀.ι.app i ≫ g = gᵢ i ≫ c₁.ι.app i)
    (hi : ∀ i, fᵢ i ≫ q.app i = gᵢ i ≫ q.app i)
    (hπ : ∀ i, c₁.ι.app i ≫ π = q.app i ≫ c.ι.app i) : IsColimit c := by
  let t (s : Cocone K) : Cocone D₁ :=
    { pt := s.pt
      «ι» := q ≫ s.ι }
  have ht (s : Cocone K) : f ≫ h₁.desc (t s) = g ≫ h₁.desc (t s) := by
    apply h₀.hom_ext
    intro i
    rw [← Category.assoc, hf, Category.assoc, h₁.fac, ← Category.assoc, hg,
      Category.assoc, h₁.fac]
    change fᵢ i ≫ q.app i ≫ s.ι.app i = gᵢ i ≫ q.app i ≫ s.ι.app i
    rw [← Category.assoc, hi, Category.assoc]
  let d (s : Cocone K) := Cofork.IsColimit.desc hq (h₁.desc (t s)) (ht s)
  have hd (s : Cocone K) : π ≫ d s = h₁.desc (t s) :=
    Cofork.IsColimit.π_desc' hq _ _
  refine
    { desc := d
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply (cancel_epi (q.app i)).mp
    rw [← Category.assoc, ← hπ, Category.assoc, hd, h₁.fac]
    rfl
  · intro s m hm
    apply (cancel_epi π).mp
    rw [hd]
    apply h₁.hom_ext
    intro i
    rw [← Category.assoc, hπ, Category.assoc, hm, h₁.fac]
    rfl

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Scalar-extension coequalizers commute with the final coefficient-ring colimit.
Source: archived `TwoColimit.lean`, coefficient construction, and the defining
coequalizer of `Mod.extendScalars`. Tensor with a fixed object preserves colimits.
The two action maps are compatible with coefficient inclusion. The universal
property of the coefficient colimit therefore descends through their coequalizers.
Forgetting module structure reflects colimits, and complex colimits are degreewise.
(auxiliary; not a blueprint node) -/
theorem nonempty_isColimit_coefficientComplexCocone
    {E F : FiniteIntermediateField ℓ}
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (H : I ⥤ FiniteIntermediateField ℓ) [H.Final]
    (he : ∀ i, E ≤ H.obj i) (hf : ∀ i, F ≤ H.obj i) :
    Nonempty (IsColimit (coefficientComplexCocone X ℓ C H he hf)) := by
  refine ⟨?_⟩
  apply HomologicalComplex.isColimitOfEval
  intro n
  apply isColimitOfReflects (Mod.forget (padicSubfieldRingObj X ℓ E))
  let cS := (padicAlgClRingObjCocone X ℓ).whisker H
  have hS : IsColimit cS :=
    (CategoryTheory.Functor.Final.isColimitWhiskerEquiv H _).symm
      (isColimitPadicAlgClRingObjCocone X ℓ)
  let M := C.X n
  let R := padicSubfieldRingObj X ℓ F
  let S := padicAlgClRingObj X ℓ
  let c₁ := (tensorRight M.X).mapCocone cS
  let c₀ := (tensorRight M.X).mapCocone ((tensorRight R).mapCocone cS)
  let K := coefficientComplexDiagram X ℓ C H he hf ⋙
    HomologicalComplex.eval _ (.up ℤ) n ⋙ Mod.forget (padicSubfieldRingObj X ℓ E)
  let c : Cocone K := (Mod.forget (padicSubfieldRingObj X ℓ E)).mapCocone
    ((HomologicalComplex.eval _ (.up ℤ) n).mapCocone
      (coefficientComplexCocone X ℓ C H he hf))
  let q : c₁.pt ⟶ c.pt := Mod.extendπ (padicSubfieldRingObjToPadicAlgCl X ℓ F) M
  let qi : (H ⋙ Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X ⋙
      tensorRight M.X) ⟶ K :=
    { app i := Mod.extendπ (padicSubfieldRingObjMap X ℓ (hf i)) M
      naturality i j a := by
        change padicSubfieldRingObjMap X ℓ (leOfHom (H.map a)) ▷ M.X ≫
          Mod.extendπ (padicSubfieldRingObjMap X ℓ (hf j)) M = _
        exact (Mod.extendπ_mixedScalarMap
          (padicSubfieldRingObjMap X ℓ (hf i)) (padicSubfieldRingObjMap X ℓ (hf j))
          (padicSubfieldRingObjMap X ℓ (he i)) (padicSubfieldRingObjMap X ℓ (he j))
          (padicSubfieldRingObjMap X ℓ (leOfHom (H.map a)))
          (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _)
          (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _) M).symm }
  have hqi (i : I) : Epi (qi.app i) := by
    dsimp [qi]
    infer_instance
  let f : c₀.pt ⟶ c₁.pt :=
    (S ◁ padicSubfieldRingObjToPadicAlgCl X ℓ F ≫ μ[S]) ▷ M.X
  let g : c₀.pt ⟶ c₁.pt := (α_ S R M.X).hom ≫ S ◁ γ[R,M.X]
  let fi (i : I) : ((padicSubfieldRingObj X ℓ (H.obj i) ⊗ R) ⊗ M.X) ⟶
      (padicSubfieldRingObj X ℓ (H.obj i) ⊗ M.X) :=
    ((padicSubfieldRingObj X ℓ (H.obj i)) ◁ padicSubfieldRingObjMap X ℓ (hf i) ≫
      μ[padicSubfieldRingObj X ℓ (H.obj i)]) ▷ M.X
  let gi (i : I) : ((padicSubfieldRingObj X ℓ (H.obj i) ⊗ R) ⊗ M.X) ⟶
      (padicSubfieldRingObj X ℓ (H.obj i) ⊗ M.X) :=
    (α_ (padicSubfieldRingObj X ℓ (H.obj i)) R M.X).hom ≫
      (padicSubfieldRingObj X ℓ (H.obj i)) ◁ γ[R,M.X]
  have hq : f ≫ q = g ≫ q := Mod.extendπ_condition _ M
  refine coequalizer_colimit _ _ K c₀ c₁ c
    (isColimitOfPreserves _ (isColimitOfPreserves _ hS))
    (isColimitOfPreserves _ hS) f g fi gi qi q hq
    (Mod.isColimitExtendπ _ M) ?_ ?_ ?_ ?_
  · intro i
    change ((padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i)) ▷ R) ▷ M.X ≫
      ((S ◁ padicSubfieldRingObjToPadicAlgCl X ℓ F ≫ μ[S]) ▷ M.X) =
        (((padicSubfieldRingObj X ℓ (H.obj i)) ◁
          padicSubfieldRingObjMap X ℓ (hf i) ≫
          μ[padicSubfieldRingObj X ℓ (H.obj i)]) ▷ M.X) ≫
            (padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i)) ▷ M.X
    rw [← comp_whiskerRight, ← comp_whiskerRight]
    congr 1
    rw [← padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (hf i), whiskerLeft_comp,
      Category.assoc, ← whisker_exchange_assoc, ← tensorHom_def_assoc,
      ← IsMonHom.mul_hom, ← Category.assoc]
  · intro i
    change ((padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i)) ▷ R) ▷ M.X ≫
      (α_ S R M.X).hom ≫ S ◁ γ[R,M.X] =
        ((α_ (padicSubfieldRingObj X ℓ (H.obj i)) R M.X).hom ≫
          (padicSubfieldRingObj X ℓ (H.obj i)) ◁ γ[R,M.X]) ≫
            (padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i)) ▷ M.X
    rw [associator_naturality_left_assoc, Category.assoc, ← whisker_exchange]
  · intro i
    exact Mod.extendπ_condition _ M
  · intro i
    change padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i) ▷ M.X ≫
      Mod.extendπ (padicSubfieldRingObjToPadicAlgCl X ℓ F) M = _
    exact (Mod.extendπ_mixedScalarMap
      (padicSubfieldRingObjMap X ℓ (hf i)) (padicSubfieldRingObjToPadicAlgCl X ℓ F)
      (padicSubfieldRingObjMap X ℓ (he i)) (padicSubfieldRingObjToPadicAlgCl X ℓ E)
      (padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i))
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _) M).symm

end AlgebraicGeometry.ProEtale
