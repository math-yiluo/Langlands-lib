/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVCoverChainSquare
import WeilConjectures.AlgebraicGeometry.Picard.ConeDiagramFullSESPresentation

/-! # Short exact rows for an unrestricted relative cover comparison

## References

* Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY
* Stacks Project, Cohomology, Tags 08BV and 08HZ (the restriction rows), 08FE (open direct-image
  comparison), and 08HY (the base-change mate)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Resolve the relative cover comparison as a map of short exact rows, before
passing from their quotients to mapping cones. -/
theorem relativeMV_cover_rows
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ a.left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ (b U).left ⊞ (b V).left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (b (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom ≫ biprod.fst =
        e₂.hom ≫ biprod.fst ≫ (b U).hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom ≫ biprod.snd =
        e₂.hom ≫ biprod.snd ≫ (b V).hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ (b (U ⊓ V)).hom := by
  dsimp only
  obtain ⟨A, B, A', B', t, t', α, β, hc, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ :=
    relativeMV_cover_chain_square f f' g g' hpull K K' φ U V hcover
  obtain ⟨P, P', m, d₁, d₂, d₃, d₁', d₂', d₃', hP, hP', _, _, _, _, hm₁, hm₂, hm₃⟩ :=
    cone_diagram_full_ses_presentation A B A' B' t t' α β hc
  refine ⟨P, P', m, d₁ ≪≫ e₁, d₂ ≪≫ e₂, d₃ ≪≫ e₃,
    d₁' ≪≫ e₁', d₂' ≪≫ e₂', d₃' ≪≫ e₃', hP, hP', ?_, ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Category.assoc, hα] using
      congrArg (fun k ↦ k ≫ e₁'.hom) hm₁
  · have h := congrArg (fun k ↦ k ≫ e₂'.hom) hm₂
    simp only [Category.assoc] at h
    have hb := congrArg (fun k ↦ d₂.hom ≫ k) hβ
    have hh := h.trans hb
    simpa only [Iso.trans_hom, Category.assoc, biprod.map_fst] using
      congrArg (fun k ↦ k ≫ biprod.fst) hh
  · have h := congrArg (fun k ↦ k ≫ e₂'.hom) hm₂
    simp only [Category.assoc] at h
    have hb := congrArg (fun k ↦ d₂.hom ≫ k) hβ
    have hh := h.trans hb
    simpa only [Iso.trans_hom, Category.assoc, biprod.map_snd] using
      congrArg (fun k ↦ k ≫ biprod.snd) hh
  · simpa only [Iso.trans_hom, Category.assoc, hγ] using
      congrArg (fun k ↦ k ≫ e₃'.hom) hm₃

end AlgebraicGeometry
