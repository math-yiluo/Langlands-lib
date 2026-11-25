/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonFormula
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Pasting of normalized derived reduction comparisons

Source: Stacks Project, Tags 06YY and 0D6D
(blueprint: lem-weil-pbc-completed-reduction-pullback-square).

Reduction comparisons normalized on good representatives paste along squares of exact
functors whenever the underlying ordinary comparisons paste.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section Square

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F₁ : A ⥤ B) (F₂ : B ⥤ D) (F₃ : A ⥤ C) (F₄ : C ⥤ D)
  [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]

/-- The derived square of exact functors on the image of a complex is the localization of
the ordinary square, up to the factorization isomorphisms.
Source: Stacks Tag 05S7 (blueprint: lem-weil-pbc-completed-reduction-pullback-square). -/
theorem mapDerivedCategorySquareIso_hom_app_factors (σ : F₁ ⋙ F₂ ≅ F₃ ⋙ F₄)
    (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso σ).hom.app (DerivedCategory.Q.obj P) ≫
        F₄.mapDerivedCategory.map (F₃.mapDerivedCategoryFactors.hom.app P) ≫
        F₄.mapDerivedCategoryFactors.hom.app ((F₃.mapHomologicalComplex (.up ℤ)).obj P) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ P]
  simp

end Square

private theorem natTrans_ext_of_good
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    (good : C → Prop)
    (res : ∀ X, ∃ (P : C) (p : P ⟶ X), good P ∧ IsIso (F.map p))
    (α β : F ⟶ G) (h : ∀ P, good P → α.app P = β.app P) : α = β := by
  ext X
  obtain ⟨P, p, hP, hp⟩ := res X
  apply (cancel_epi (F.map p)).1
  rw [α.naturality, β.naturality, h P hP]
section Pasting

variable {BY BY' BX BX' DY DY' DX DX' : Type*}
  [Category BY] [Category BY'] [Category BX] [Category BX']
  [Category DY] [Category DY'] [Category DX] [Category DX']
  [Abelian BY] [Abelian BY'] [Abelian BX] [Abelian BX']
  [Abelian DY] [Abelian DY'] [Abelian DX] [Abelian DX']
  [HasDerivedCategory BY] [HasDerivedCategory BY'] [HasDerivedCategory BX]
  [HasDerivedCategory BX'] [HasDerivedCategory DY] [HasDerivedCategory DY']
  [HasDerivedCategory DX] [HasDerivedCategory DX']
  (Fg : BY ⥤ BY') (Ff' : BY' ⥤ BX') (Ff : BY ⥤ BX) (Fg' : BX ⥤ BX')
  (Gg : DY ⥤ DY') (Gf' : DY' ⥤ DX') (Gf : DY ⥤ DX) (Gg' : DX ⥤ DX')
  [Fg.Additive] [Ff'.Additive] [Ff.Additive] [Fg'.Additive]
  [Gg.Additive] [Gf'.Additive] [Gf.Additive] [Gg'.Additive]
  [PreservesFiniteLimits Fg] [PreservesFiniteColimits Fg]
  [PreservesFiniteLimits Ff'] [PreservesFiniteColimits Ff']
  [PreservesFiniteLimits Ff] [PreservesFiniteColimits Ff]
  [PreservesFiniteLimits Fg'] [PreservesFiniteColimits Fg']
  [PreservesFiniteLimits Gg] [PreservesFiniteColimits Gg]
  [PreservesFiniteLimits Gf'] [PreservesFiniteColimits Gf']
  [PreservesFiniteLimits Gf] [PreservesFiniteColimits Gf]
  [PreservesFiniteLimits Gg'] [PreservesFiniteColimits Gg']
  (RY : BY ⥤ DY) (RY' : BY' ⥤ DY') (RX : BX ⥤ DX) (RX' : BX' ⥤ DX')
  [RY.Additive] [RY'.Additive] [RX.Additive] [RX'.Additive]
  (MY : DerivedCategory BY ⥤ DerivedCategory DY)
  (MY' : DerivedCategory BY' ⥤ DerivedCategory DY')
  (MX : DerivedCategory BX ⥤ DerivedCategory DX)
  (MX' : DerivedCategory BX' ⥤ DerivedCategory DX')
  (εY : DerivedCategory.Q ⋙ MY ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εY' : DerivedCategory.Q ⋙ MY' ⟶ RY'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX : DerivedCategory.Q ⋙ MX ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX' : DerivedCategory.Q ⋙ MX' ⟶ RX'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

-- The pasting computation unfolds four reduction squares and two exact squares.
/-- Reduction comparisons normalized on good complexes paste along squares of exact
functors, provided the underlying ordinary comparisons paste. -/
theorem derivedReductionSquare_paste
    (eg : RY ⋙ Gg ≅ Fg ⋙ RY') (ef' : RY' ⋙ Gf' ≅ Ff' ⋙ RX')
    (ef : RY ⋙ Gf ≅ Ff ⋙ RX) (eg' : RX ⋙ Gg' ≅ Fg' ⋙ RX')
    (ρg : MY ⋙ Gg.mapDerivedCategory ≅ Fg.mapDerivedCategory ⋙ MY')
    (ρf' : MY' ⋙ Gf'.mapDerivedCategory ≅ Ff'.mapDerivedCategory ⋙ MX')
    (ρf : MY ⋙ Gf.mapDerivedCategory ≅ Ff.mapDerivedCategory ⋙ MX)
    (ρg' : MX ⋙ Gg'.mapDerivedCategory ≅ Fg'.mapDerivedCategory ⋙ MX')
    (σ : Fg ⋙ Ff' ≅ Ff ⋙ Fg') (τ : Gg ⋙ Gf' ≅ Gf ⋙ Gg')
    (good : ObjectProperty (CochainComplex BY ℤ))
    (res : ∀ K, ∃ (P : CochainComplex BY ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hg : ∀ P, good P → DerivedReductionComparisonFormula Fg Gg RY RY' MY MY'
      (fun P ↦ εY.app P) (fun P ↦ εY'.app P) eg ρg P)
    (hf' : ∀ P, good P → DerivedReductionComparisonFormula Ff' Gf' RY' RX' MY' MX'
      (fun P ↦ εY'.app P) (fun P ↦ εX'.app P) ef' ρf' ((Fg.mapHomologicalComplex (.up ℤ)).obj P))
    (hf : ∀ P, good P → DerivedReductionComparisonFormula Ff Gf RY RX MY MX
      (fun P ↦ εY.app P) (fun P ↦ εX.app P) ef ρf P)
    (hg' : ∀ P, good P → DerivedReductionComparisonFormula Fg' Gg' RX RX' MX MX'
      (fun P ↦ εX.app P) (fun P ↦ εX'.app P) eg' ρg' ((Ff.mapHomologicalComplex (.up ℤ)).obj P))
    (hiso : ∀ P, good P → IsIso (εX'.app ((Fg'.mapHomologicalComplex (.up ℤ)).obj
      ((Ff.mapHomologicalComplex (.up ℤ)).obj P))))
    (hab : ∀ M : BY, Gf'.map (eg.hom.app M) ≫ ef'.hom.app (Fg.obj M) ≫ RX'.map (σ.hom.app M) =
      τ.hom.app (RY.obj M) ≫ Gg'.map (ef.hom.app M) ≫ eg'.hom.app (Ff.obj M)) :
    Functor.whiskerRight ρg.hom Gf'.mapDerivedCategory ≫
        Functor.whiskerLeft Fg.mapDerivedCategory ρf'.hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso σ).hom MX' =
      Functor.whiskerLeft MY (Functor.mapDerivedCategorySquareIso τ).hom ≫
        Functor.whiskerRight ρf.hom Gg'.mapDerivedCategory ≫
        Functor.whiskerLeft Ff.mapDerivedCategory ρg'.hom := by
  have key : ∀ P, good P →
      Gf'.mapDerivedCategory.map (ρg.hom.app (DerivedCategory.Q.obj P)) ≫
        ρf'.hom.app (Fg.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        MX'.map ((Functor.mapDerivedCategorySquareIso σ).hom.app (DerivedCategory.Q.obj P)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app (MY.obj (DerivedCategory.Q.obj P)) ≫
        Gg'.mapDerivedCategory.map (ρf.hom.app (DerivedCategory.Q.obj P)) ≫
        ρg'.hom.app (Ff.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
    intro P hP
    have := hiso P hP
    apply (cancel_mono (MX'.map (Fg'.mapDerivedCategory.map
        (Ff.mapDerivedCategoryFactors.hom.app P) ≫
          Fg'.mapDerivedCategoryFactors.hom.app ((Ff.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        εX'.app ((Fg'.mapHomologicalComplex (.up ℤ)).obj
          ((Ff.mapHomologicalComplex (.up ℤ)).obj P)))).1
    simp only [Category.assoc]
    -- right-hand side
    have r1 : Gg'.mapDerivedCategory.map (MX.map (Ff.mapDerivedCategoryFactors.hom.app P)) ≫
        ρg'.hom.app (DerivedCategory.Q.obj ((Ff.mapHomologicalComplex (.up ℤ)).obj P)) =
      ρg'.hom.app (Ff.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        MX'.map (Fg'.mapDerivedCategory.map (Ff.mapDerivedCategoryFactors.hom.app P)) :=
      ρg'.hom.naturality _
    have r2 := hg' P hP
    unfold DerivedReductionComparisonFormula at r2
    have r3 := hf P hP
    unfold DerivedReductionComparisonFormula at r3
    have r4 : Gg'.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ef.hom (.up ℤ)).app P)) ≫
        Gg'.mapDerivedCategoryFactors.hom.app ((RX.mapHomologicalComplex (.up ℤ)).obj
          ((Ff.mapHomologicalComplex (.up ℤ)).obj P)) =
      Gg'.mapDerivedCategoryFactors.hom.app ((Gf.mapHomologicalComplex (.up ℤ)).obj
          ((RY.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Gg'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex ef.hom (.up ℤ)).app P)) :=
      Gg'.mapDerivedCategoryFactors.hom.naturality _
    have r5 : Gf'.mapDerivedCategory.map (Gg.mapDerivedCategory.map (εY.app P)) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app
          (DerivedCategory.Q.obj ((RY.mapHomologicalComplex (.up ℤ)).obj P)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app (MY.obj (DerivedCategory.Q.obj P)) ≫
        Gg'.mapDerivedCategory.map (Gf.mapDerivedCategory.map (εY.app P)) :=
      (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
    have r6 := mapDerivedCategorySquareIso_hom_app_factors Gg Gf' Gf Gg' τ
      ((RY.mapHomologicalComplex (.up ℤ)).obj P)
    -- left-hand side
    have l1 := mapDerivedCategorySquareIso_hom_app_factors Fg Ff' Ff Fg' σ P
    have l2 : MX'.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P)) ≫
        εX'.app ((Fg'.mapHomologicalComplex (.up ℤ)).obj
          ((Ff.mapHomologicalComplex (.up ℤ)).obj P)) =
      εX'.app ((Ff'.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((RX'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P)) :=
      εX'.naturality _
    have l3 : Gf'.mapDerivedCategory.map (MY'.map (Fg.mapDerivedCategoryFactors.hom.app P)) ≫
        ρf'.hom.app (DerivedCategory.Q.obj ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      ρf'.hom.app (Fg.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        MX'.map (Ff'.mapDerivedCategory.map (Fg.mapDerivedCategoryFactors.hom.app P)) :=
      ρf'.hom.naturality _
    have l4 := hf' P hP
    unfold DerivedReductionComparisonFormula at l4
    have l5 := hg P hP
    unfold DerivedReductionComparisonFormula at l5
    have l6 : Gf'.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P)) ≫
        Gf'.mapDerivedCategoryFactors.hom.app ((RY'.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      Gf'.mapDerivedCategoryFactors.hom.app ((Gg.mapHomologicalComplex (.up ℤ)).obj
          ((RY.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Gf'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P)) :=
      Gf'.mapDerivedCategoryFactors.hom.naturality _
    have hx : (Gf'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex ef'.hom (.up ℤ)).app
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (RX'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P) =
      (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app
          ((RY.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Gg'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex ef.hom (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex eg'.hom (.up ℤ)).app
          ((Ff.mapHomologicalComplex (.up ℤ)).obj P) := by
      ext n
      exact hab (P.X n)
    have l5m := congrArg (Gf'.mapDerivedCategory.map) l5
    simp only [Functor.map_comp] at l5m
    have r3m := congrArg (Gg'.mapDerivedCategory.map) r3
    simp only [Functor.map_comp] at r3m
    conv_lhs => rw [← MX'.map_comp_assoc, l1, MX'.map_comp, MX'.map_comp, Category.assoc,
      Category.assoc]
    conv_lhs => rw [l2]
    conv_lhs => rw [← reassoc_of% l3]
    conv_lhs => rw [reassoc_of% l4]
    conv_lhs => rw [reassoc_of% l5m]
    conv_lhs => rw [reassoc_of% l6]
    conv_rhs => rw [MX'.map_comp, Category.assoc]
    conv_rhs => rw [← reassoc_of% r1]
    conv_rhs => rw [r2]
    conv_rhs => rw [reassoc_of% r3m]
    conv_rhs => rw [reassoc_of% r4]
    conv_rhs => rw [← reassoc_of% r5]
    conv_rhs => rw [reassoc_of% r6]
    have hx' := congrArg DerivedCategory.Q.map hx
    simp only [Functor.map_comp] at hx'
    rw [hx']
  apply natTrans_ext_of_good _ _ (fun X ↦ ∃ P, good P ∧ X = DerivedCategory.Q.obj P)
  · intro X
    obtain ⟨P, p, hP, hp⟩ := res (DerivedCategory.Q.objPreimage X)
    have : IsIso (DerivedCategory.Q.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
    exact ⟨DerivedCategory.Q.obj P,
      (asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X).hom,
      ⟨P, hP, rfl⟩, inferInstance⟩
  · rintro _ ⟨P, hP, rfl⟩
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
      key P hP

end Pasting

section TowerPasting

variable {BY BY' BX BX' : Type*}
  [Category BY] [Category BY'] [Category BX] [Category BX']
  [Abelian BY] [Abelian BY'] [Abelian BX] [Abelian BX']
  [HasDerivedCategory BY] [HasDerivedCategory BY'] [HasDerivedCategory BX]
  [HasDerivedCategory BX'] [HasDerivedCategory (ℕᵒᵖ ⥤ BY)] [HasDerivedCategory (ℕᵒᵖ ⥤ BY')]
  [HasDerivedCategory (ℕᵒᵖ ⥤ BX)] [HasDerivedCategory (ℕᵒᵖ ⥤ BX')]
  (Fg : BY ⥤ BY') (Ff' : BY' ⥤ BX') (Ff : BY ⥤ BX) (Fg' : BX ⥤ BX')
  [Fg.Additive] [Ff'.Additive] [Ff.Additive] [Fg'.Additive]
  [PreservesFiniteLimits Fg] [PreservesFiniteColimits Fg]
  [PreservesFiniteLimits Ff'] [PreservesFiniteColimits Ff']
  [PreservesFiniteLimits Ff] [PreservesFiniteColimits Ff]
  [PreservesFiniteLimits Fg'] [PreservesFiniteColimits Fg']
  [((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg).Additive]
  [((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff').Additive]
  [((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff).Additive]
  [((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg').Additive]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg)]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff')]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff')]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff)]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg')]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg')]
  (RY : BY ⥤ ℕᵒᵖ ⥤ BY) (RY' : BY' ⥤ ℕᵒᵖ ⥤ BY') (RX : BX ⥤ ℕᵒᵖ ⥤ BX)
  (RX' : BX' ⥤ ℕᵒᵖ ⥤ BX')
  [RY.Additive] [RY'.Additive] [RX.Additive] [RX'.Additive]
  (MY : DerivedCategory BY ⥤ DerivedCategory (ℕᵒᵖ ⥤ BY))
  (MY' : DerivedCategory BY' ⥤ DerivedCategory (ℕᵒᵖ ⥤ BY'))
  (MX : DerivedCategory BX ⥤ DerivedCategory (ℕᵒᵖ ⥤ BX))
  (MX' : DerivedCategory BX' ⥤ DerivedCategory (ℕᵒᵖ ⥤ BX'))
  (εY : DerivedCategory.Q ⋙ MY ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εY' : DerivedCategory.Q ⋙ MY' ⟶ RY'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX : DerivedCategory.Q ⋙ MX ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX' : DerivedCategory.Q ⋙ MX' ⟶ RX'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

/-- The tower case of `derivedReductionSquare_paste`: the exact functors on towers act
levelwise, so the ordinary pasting condition may be checked at each level.
Source: Stacks Tags 06YY, 0D6D
(blueprint: lem-weil-pbc-completed-reduction-pullback-square). -/
theorem derivedReductionTowerSquare_paste
    (eg : RY ⋙ (Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg ≅ Fg ⋙ RY')
    (ef' : RY' ⋙ (Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff' ≅ Ff' ⋙ RX')
    (ef : RY ⋙ (Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff ≅ Ff ⋙ RX)
    (eg' : RX ⋙ (Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg' ≅ Fg' ⋙ RX')
    (ρg : MY ⋙ ((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg).mapDerivedCategory ≅
      Fg.mapDerivedCategory ⋙ MY')
    (ρf' : MY' ⋙ ((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff').mapDerivedCategory ≅
      Ff'.mapDerivedCategory ⋙ MX')
    (ρf : MY ⋙ ((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff).mapDerivedCategory ≅
      Ff.mapDerivedCategory ⋙ MX)
    (ρg' : MX ⋙ ((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg').mapDerivedCategory ≅
      Fg'.mapDerivedCategory ⋙ MX')
    (σ : Fg ⋙ Ff' ≅ Ff ⋙ Fg')
    (good : ObjectProperty (CochainComplex BY ℤ))
    (res : ∀ K, ∃ (P : CochainComplex BY ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hg : ∀ P, good P → DerivedReductionComparisonFormula Fg
      ((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg) RY RY' MY MY'
      (fun P ↦ εY.app P) (fun P ↦ εY'.app P) eg ρg P)
    (hf' : ∀ P, good P → DerivedReductionComparisonFormula Ff'
      ((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff') RY' RX' MY' MX'
      (fun P ↦ εY'.app P) (fun P ↦ εX'.app P) ef' ρf' ((Fg.mapHomologicalComplex (.up ℤ)).obj P))
    (hf : ∀ P, good P → DerivedReductionComparisonFormula Ff
      ((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff) RY RX MY MX
      (fun P ↦ εY.app P) (fun P ↦ εX.app P) ef ρf P)
    (hg' : ∀ P, good P → DerivedReductionComparisonFormula Fg'
      ((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg') RX RX' MX MX'
      (fun P ↦ εX.app P) (fun P ↦ εX'.app P) eg' ρg' ((Ff.mapHomologicalComplex (.up ℤ)).obj P))
    (hiso : ∀ P, good P → IsIso (εX'.app ((Fg'.mapHomologicalComplex (.up ℤ)).obj
      ((Ff.mapHomologicalComplex (.up ℤ)).obj P))))
    (uY : Functor.const ℕᵒᵖ ⟶ RY) (uY' : Functor.const ℕᵒᵖ ⟶ RY')
    (uX : Functor.const ℕᵒᵖ ⟶ RX) (uX' : Functor.const ℕᵒᵖ ⟶ RX')
    (hepi : ∀ (M : BY) (n : ℕᵒᵖ), Epi ((uY.app M).app n))
    (ng : ∀ (M : BY) (n : ℕᵒᵖ),
      Fg.map ((uY.app M).app n) ≫ (eg.hom.app M).app n = (uY'.app (Fg.obj M)).app n)
    (nf' : ∀ (M : BY') (n : ℕᵒᵖ),
      Ff'.map ((uY'.app M).app n) ≫ (ef'.hom.app M).app n = (uX'.app (Ff'.obj M)).app n)
    (nf : ∀ (M : BY) (n : ℕᵒᵖ),
      Ff.map ((uY.app M).app n) ≫ (ef.hom.app M).app n = (uX.app (Ff.obj M)).app n)
    (ng' : ∀ (M : BX) (n : ℕᵒᵖ),
      Fg'.map ((uX.app M).app n) ≫ (eg'.hom.app M).app n = (uX'.app (Fg'.obj M)).app n) :
    Functor.whiskerRight ρg.hom
        ((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff').mapDerivedCategory ≫
        Functor.whiskerLeft Fg.mapDerivedCategory ρf'.hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso σ).hom MX' =
      Functor.whiskerLeft MY (Functor.mapDerivedCategorySquareIso
          (show (Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg ⋙
              (Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff' ≅
            (Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff ⋙
              (Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg' from
            (Functor.whiskeringRight ℕᵒᵖ BY BX').mapIso σ)).hom ≫
        Functor.whiskerRight ρf.hom
          ((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg').mapDerivedCategory ≫
        Functor.whiskerLeft Ff.mapDerivedCategory ρg'.hom :=
  derivedReductionSquare_paste Fg Ff' Ff Fg' _ _ _ _ RY RY' RX RX' MY MY' MX MX' εY εY' εX εX'
    eg ef' ef eg' ρg ρf' ρf ρg' σ ((Functor.whiskeringRight ℕᵒᵖ BY BX').mapIso σ) good res
    hg hf' hf hg' hiso (fun M ↦ NatTrans.ext (funext fun n ↦ by
      have := hepi M n
      apply (cancel_epi (Ff'.map (Fg.map ((uY.app M).app n)))).1
      have hu := NatTrans.congr_app (uX'.naturality (σ.hom.app M)) n
      simp only [NatTrans.comp_app, Functor.const_map_app] at hu
      have hσ := σ.hom.naturality ((uY.app M).app n)
      simp only [Functor.comp_map] at hσ
      simp only [NatTrans.comp_app, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
        Functor.mapIso_hom]
      rw [← Functor.map_comp_assoc, ng, reassoc_of% (nf' (Fg.obj M) n)]
      erw [← hu, reassoc_of% hσ]
      rw [← Functor.map_comp_assoc, nf, ng']
      rfl))

end TowerPasting

end AlgebraicGeometry.Scheme
