/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation

/-! # Pasted squares of presented derived functors

Two pasting identities of natural isomorphisms between presented derived functors follow
from the corresponding identities of the represented ordinary natural isomorphisms.

Source: Stacks Project, Tag 05RU (universal property of localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

open DerivedPresentation

section Paste

variable {A₀ A₁ B₀ B₁ C₀ C₁ E : Type*}
  [Category A₀] [Category A₁] [Category B₀] [Category B₁] [Category C₀] [Category C₁]
  [Category E]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁] [Abelian C₀] [Abelian C₁] [Abelian E]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory B₀]
  [HasDerivedCategory B₁] [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory E]

/-- Two derived transformations representing equal ordinary transformations agree. -/
lemma DerivedRepresents.eq_of_eq {Φ Ψ : DerivedCategory A₀ ⥤ DerivedCategory A₁}
    {F G : A₀ ⥤ A₁} [F.Additive] [G.Additive]
    {p : DerivedPresentation Φ F} {q : DerivedPresentation Ψ G}
    {τ σ : Φ ⟶ Ψ} {τ₀ σ₀ : F ⟶ G} (h : DerivedRepresents p q τ τ₀)
    (h' : DerivedRepresents p q σ σ₀) (e : τ₀ = σ₀) : τ = σ :=
  h.ext' (h'.congr rfl e.symm)

/-- A scalar square through a realization comparison: if all derived pieces are
represented by ordinary pieces satisfying the pasting identity, the derived pieces satisfy
it as well. -/
lemma scalar_paste_app_eq_of_represents
    {N : DerivedCategory A₀ ⥤ DerivedCategory A₁}
    {K₀ : DerivedCategory A₀ ⥤ DerivedCategory C₀} {K₁ : DerivedCategory A₁ ⥤ DerivedCategory C₁}
    {H₀ : DerivedCategory C₀ ⥤ DerivedCategory E} {H₁ : DerivedCategory C₁ ⥤ DerivedCategory E}
    {F₀ : DerivedCategory A₀ ⥤ DerivedCategory B₀} {F₁ : DerivedCategory A₁ ⥤ DerivedCategory B₁}
    {P₀ : DerivedCategory B₀ ⥤ DerivedCategory C₀} {P₁ : DerivedCategory B₁ ⥤ DerivedCategory C₁}
    {Q : DerivedCategory B₀ ⥤ DerivedCategory B₁}
    {n : A₀ ⥤ A₁} {k₀ : A₀ ⥤ C₀} {k₁ : A₁ ⥤ C₁} {h₀ : C₀ ⥤ E} {h₁ : C₁ ⥤ E}
    {f₀ : A₀ ⥤ B₀} {f₁ : A₁ ⥤ B₁} {p₀ : B₀ ⥤ C₀} {p₁ : B₁ ⥤ C₁} {q : B₀ ⥤ B₁}
    [n.Additive] [k₀.Additive] [k₁.Additive] [h₀.Additive] [h₁.Additive] [f₀.Additive]
    [f₁.Additive] [p₀.Additive] [p₁.Additive] [q.Additive]
    (pN : DerivedPresentation N n) (pK₀ : DerivedPresentation K₀ k₀)
    (pK₁ : DerivedPresentation K₁ k₁) (pH₀ : DerivedPresentation H₀ h₀)
    (pH₁ : DerivedPresentation H₁ h₁) (pF₀ : DerivedPresentation F₀ f₀)
    (pF₁ : DerivedPresentation F₁ f₁) (pP₀ : DerivedPresentation P₀ p₀)
    (pP₁ : DerivedPresentation P₁ p₁) (pQ : DerivedPresentation Q q)
    {κ : N ⋙ K₁ ⋙ H₁ ≅ K₀ ⋙ H₀} {κ' : n ⋙ k₁ ⋙ h₁ ≅ k₀ ⋙ h₀}
    {ω₀ : K₀ ≅ F₀ ⋙ P₀} {ω₀' : k₀ ≅ f₀ ⋙ p₀} {ω₁ : K₁ ≅ F₁ ⋙ P₁} {ω₁' : k₁ ≅ f₁ ⋙ p₁}
    {r : N ⋙ F₁ ≅ F₀ ⋙ Q} {r' : n ⋙ f₁ ≅ f₀ ⋙ q}
    {σ : Q ⋙ P₁ ⋙ H₁ ≅ P₀ ⋙ H₀} {σ' : q ⋙ p₁ ⋙ h₁ ≅ p₀ ⋙ h₀}
    (hκ : DerivedRepresents (pN.comp (pK₁.comp pH₁)) (pK₀.comp pH₀) κ.hom κ'.hom)
    (hω₀ : DerivedRepresents pK₀ (pF₀.comp pP₀) ω₀.hom ω₀'.hom)
    (hω₁ : DerivedRepresents pK₁ (pF₁.comp pP₁) ω₁.hom ω₁'.hom)
    (hr : DerivedRepresents (pN.comp pF₁) (pF₀.comp pQ) r.hom r'.hom)
    (hσ : DerivedRepresents (pQ.comp (pP₁.comp pH₁)) (pP₀.comp pH₀) σ.hom σ'.hom)
    (e : ∀ X : A₀, κ'.hom.app X ≫ h₀.map (ω₀'.hom.app X) =
      h₁.map (ω₁'.hom.app (n.obj X)) ≫ h₁.map (p₁.map (r'.hom.app X)) ≫
        σ'.hom.app (f₀.obj X))
    (X : DerivedCategory A₀) :
    κ.hom.app X ≫ H₀.map (ω₀.hom.app X) =
      H₁.map (ω₁.hom.app (N.obj X)) ≫ H₁.map (P₁.map (r.hom.app X)) ≫
        σ.hom.app (F₀.obj X) := by
  have hL := hκ.comp (hω₀.whiskerRight pH₀)
  have h1 := ((hω₁.whiskerRight pH₁).whiskerLeft pN).comp
    ((derivedRepresents_associator pF₁ pP₁ pH₁).whiskerLeft pN)
  have h2 := ((h1.comp (derivedRepresents_associator_inv pN pF₁ (pP₁.comp pH₁))).comp
    (hr.whiskerRight (pP₁.comp pH₁))).comp
    (derivedRepresents_associator pF₀ pQ (pP₁.comp pH₁))
  have hR := (h2.comp (hσ.whiskerLeft pF₀)).comp
    (derivedRepresents_associator_inv pF₀ pP₀ pH₀)
  have h := hL.eq_of_eq hR (by
    ext Y
    simpa using e Y)
  simpa using congrArg (fun τ ↦ τ.app X) h

/-- Compatibility of two base change comparisons with restriction mates: if all derived
pieces are represented by ordinary pieces satisfying the identity, so are the derived
ones. -/
lemma restriction_paste_app_eq_of_represents
    {R : DerivedCategory A₀ ⥤ DerivedCategory A₁}
    {P₀ : DerivedCategory A₀ ⥤ DerivedCategory B₀} {P₁ : DerivedCategory A₁ ⥤ DerivedCategory B₁}
    {G₀ : DerivedCategory B₀ ⥤ DerivedCategory C₀} {G₁ : DerivedCategory B₁ ⥤ DerivedCategory C₁}
    {S₀ : DerivedCategory A₀ ⥤ DerivedCategory C₀} {S₁ : DerivedCategory A₁ ⥤ DerivedCategory C₁}
    {RB : DerivedCategory B₀ ⥤ DerivedCategory B₁}
    {RC : DerivedCategory C₀ ⥤ DerivedCategory C₁}
    {r : A₀ ⥤ A₁} {p₀ : A₀ ⥤ B₀} {p₁ : A₁ ⥤ B₁} {g₀ : B₀ ⥤ C₀} {g₁ : B₁ ⥤ C₁}
    {s₀ : A₀ ⥤ C₀} {s₁ : A₁ ⥤ C₁} {rb : B₀ ⥤ B₁} {rc : C₀ ⥤ C₁}
    [r.Additive] [p₀.Additive] [p₁.Additive] [g₀.Additive] [g₁.Additive] [s₀.Additive]
    [s₁.Additive] [rb.Additive] [rc.Additive]
    (pR : DerivedPresentation R r) (pP₀ : DerivedPresentation P₀ p₀)
    (pP₁ : DerivedPresentation P₁ p₁) (pG₀ : DerivedPresentation G₀ g₀)
    (pG₁ : DerivedPresentation G₁ g₁) (pS₀ : DerivedPresentation S₀ s₀)
    (pS₁ : DerivedPresentation S₁ s₁) (pRB : DerivedPresentation RB rb)
    (pRC : DerivedPresentation RC rc)
    {α : R ⋙ P₁ ≅ P₀ ⋙ RB} {α' : r ⋙ p₁ ≅ p₀ ⋙ rb}
    {β : RB ⋙ G₁ ≅ G₀ ⋙ RC} {β' : rb ⋙ g₁ ≅ g₀ ⋙ rc}
    {γ₀ : P₀ ⋙ G₀ ≅ S₀} {γ₀' : p₀ ⋙ g₀ ≅ s₀} {γ₁ : P₁ ⋙ G₁ ≅ S₁} {γ₁' : p₁ ⋙ g₁ ≅ s₁}
    {δ : R ⋙ S₁ ≅ S₀ ⋙ RC} {δ' : r ⋙ s₁ ≅ s₀ ⋙ rc}
    (hα : DerivedRepresents (pR.comp pP₁) (pP₀.comp pRB) α.hom α'.hom)
    (hβ : DerivedRepresents (pRB.comp pG₁) (pG₀.comp pRC) β.hom β'.hom)
    (hγ₀ : DerivedRepresents (pP₀.comp pG₀) pS₀ γ₀.hom γ₀'.hom)
    (hγ₁ : DerivedRepresents (pP₁.comp pG₁) pS₁ γ₁.hom γ₁'.hom)
    (hδ : DerivedRepresents (pR.comp pS₁) (pS₀.comp pRC) δ.hom δ'.hom)
    (e : ∀ X : A₀, g₁.map (α'.hom.app X) ≫ β'.hom.app (p₀.obj X) ≫
      rc.map (γ₀'.hom.app X) = γ₁'.hom.app (r.obj X) ≫ δ'.hom.app X)
    (X : DerivedCategory A₀) :
    G₁.map (α.hom.app X) ≫ β.hom.app (P₀.obj X) ≫ RC.map (γ₀.hom.app X) =
      γ₁.hom.app (R.obj X) ≫ δ.hom.app X := by
  have hL := (((((derivedRepresents_associator_inv pR pP₁ pG₁).comp
    (hα.whiskerRight pG₁)).comp (derivedRepresents_associator pP₀ pRB pG₁)).comp
    (hβ.whiskerLeft pP₀)).comp (derivedRepresents_associator_inv pP₀ pG₀ pRC)).comp
    (hγ₀.whiskerRight pRC)
  have hR := (hγ₁.whiskerLeft pR).comp hδ
  have h := hL.eq_of_eq hR (by
    ext Y
    simpa using e Y)
  simpa using congrArg (fun τ ↦ τ.app X) h

end Paste

section Lift

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- The derived isomorphism represented by an ordinary isomorphism of presented functors. -/
def DerivedPresentation.liftIso {Φ Ψ : DerivedCategory C ⥤ DerivedCategory D} {F G : C ⥤ D}
    [F.Additive] [G.Additive] (p : DerivedPresentation Φ F) (q : DerivedPresentation Ψ G)
    (e : F ≅ G) : Φ ≅ Ψ :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ Φ) (DerivedCategory.Q ⋙ Ψ) Φ Ψ
    (p ≪≫ isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ q.symm)

/-- `DerivedPresentation.liftIso` represents its ordinary isomorphism. -/
lemma derivedRepresents_liftIso {Φ Ψ : DerivedCategory C ⥤ DerivedCategory D} {F G : C ⥤ D}
    [F.Additive] [G.Additive] (p : DerivedPresentation Φ F) (q : DerivedPresentation Ψ G)
    (e : F ≅ G) : DerivedRepresents p q (p.liftIso q e).hom e.hom := by
  intro K
  simp [DerivedPresentation.liftIso, Localization.liftNatTrans_app]
  rfl

end Lift

end CategoryTheory.Functor
