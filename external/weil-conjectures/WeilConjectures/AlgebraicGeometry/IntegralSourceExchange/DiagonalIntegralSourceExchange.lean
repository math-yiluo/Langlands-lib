/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalIntegralBoundaryPullback
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence

/-! # The ordinary integral supported-source exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
namespace IntegralSourceExchange

/-- The integral constant sheaf used in the ordinary exchange. -/
abbrev integralConstant (X : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private def integralConstantComparison (X : Scheme.{u}) :=
  ((((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
    (Scheme.Etale.isTerminalMkId X)).comp (comparisonAdjunction Ab.{u + 1} X)).ofNatIsoRight
      ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
        Ab.{u + 1} X.smallEtaleTopology (Scheme.ProEt.topology X)
        (op (Scheme.Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (Scheme.ProEt.isTerminalMkId X)))

/-- The canonical inverse-image comparison of a commutative scheme square. -/
def integralSquare {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (w : D' ⟶ D)
    (sq : CommSq w i' i g) :
    upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} i' ≅
      upperStar Ab.{u + 1} i ⋙ upperStar Ab.{u + 1} w :=
  (upperStarComp Ab.{u + 1} i' g).symm ≪≫
    eqToIso (congrArg (upperStar Ab.{u + 1}) sq.w.symm) ≪≫
    upperStarComp Ab.{u + 1} w i

/-- The abelian closed exchange on integral constants, using the canonical inverse-image square. -/
def integralExchange {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (w : D' ⟶ D)
    (sq : CommSq w i' i g) :=
  (upperStarLowerStarAdjunction Ab.{u + 1} i').homEquiv _ _
    ((integralSquare i i' g w sq).hom.app
        ((lowerStar Ab.{u + 1} i).obj (integralConstant D)) ≫
      (upperStar Ab.{u + 1} w).map
        ((upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app (integralConstant D)) ≫
      Scheme.proEtaleConstantInverseImageMap w Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

namespace ConstantProof
universe u₁ u₂ u₃ v₁ v₂ v₃ w
variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {D : Type w} [Category D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃)
  [HasWeakSheafify J₁ D] [HasWeakSheafify J₂ D] [HasWeakSheafify J₃ D]

private def constantDirect (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂] (N : D) :
    (constantSheaf J₁ D).obj N ⟶
      (F.sheafPushforwardContinuous D J₁ J₂).obj ((constantSheaf J₂ D).obj N) :=
  ((sheafificationAdjunction J₁ D).homEquiv _ _).symm
    (Functor.whiskerLeft F.op (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)))

private theorem constantDirect_unit (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂]
    (N : D) (W : C₁ᵒᵖ) :
    (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₂ F N).hom.app W =
        (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)).app (F.op.obj W) := by
  have h := ((sheafificationAdjunction J₁ D).homEquiv
    ((Functor.const C₁ᵒᵖ).obj N)
    ((F.sheafPushforwardContinuous D J₁ J₂).obj ((constantSheaf J₂ D).obj N))).apply_symm_apply
    (Functor.whiskerLeft F.op (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app W) h

private def constantInverse (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂]
    {L : Sheaf J₁ D ⥤ Sheaf J₂ D}
    (a : L ⊣ F.sheafPushforwardContinuous D J₁ J₂) (N : D) :
    L.obj ((constantSheaf J₁ D).obj N) ⟶ (constantSheaf J₂ D).obj N :=
  (a.homEquiv _ _).symm (constantDirect J₁ J₂ F N)

private theorem homEquiv_mate
    {E E' : Type*} [Category E] [Category E']
    {L L' : E ⥤ E'} {R R' : E' ⥤ E} (a : L ⊣ R) (b : L' ⊣ R')
    (d : R' ≅ R) {X : E} {Y : E'} (t : L'.obj X ⟶ Y) :
    a.homEquiv X Y
        (((conjugateIsoEquiv a b).symm d.symm).inv.app X ≫ t) =
      b.homEquiv X Y t ≫ d.hom.app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc]
  change (a.unit.app X ≫
      R.map (((conjugateEquiv b a).symm d.hom).app X)) ≫ R.map t = _
  rw [← unit_conjugateEquiv_symm b a d.hom X, Category.assoc, ← d.hom.naturality]
  simp only [Category.assoc]

private theorem constantInverse_composite_adjunct
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.IsContinuous J₁ J₂] [G.IsContinuous J₂ J₃]
    {L₁ : Sheaf J₁ D ⥤ Sheaf J₂ D} {L₂ : Sheaf J₂ D ⥤ Sheaf J₃ D}
    (a₁ : L₁ ⊣ F.sheafPushforwardContinuous D J₁ J₂)
    (a₂ : L₂ ⊣ G.sheafPushforwardContinuous D J₂ J₃) (N : D) :
    (a₁.comp a₂).homEquiv _ _
        (L₂.map (constantInverse J₁ J₂ F a₁ N) ≫ constantInverse J₂ J₃ G a₂ N) =
      constantDirect J₁ J₂ F N ≫
        (F.sheafPushforwardContinuous D J₁ J₂).map (constantDirect J₂ J₃ G N) := by
  rw [Adjunction.comp_homEquiv]
  change a₁.homEquiv _ _ (a₂.homEquiv _ _ _) = _
  rw [Adjunction.homEquiv_naturality_left]
  unfold constantInverse
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]


end ConstantProof


private theorem comparison_counit {D Z : Scheme.{u}} (i : D ⟶ Z)
    (F : Sheaf D.smallEtaleTopology Ab.{u + 1}) :
    (upperStar Ab.{u + 1} i).map
        ((lowerStarComparisonUpperStarBaseChange i Ab.{u + 1}).app F) ≫
      (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
        ((comparisonUpperStar Ab.{u + 1} D).obj F) =
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} i).hom.app _ ≫
      (comparisonUpperStar Ab.{u + 1} D).map
        ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app F) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i)
    (upperStarLowerStarAdjunction Ab.{u + 1} i)
    (lowerStarComparisonUpperStarBaseChange i Ab.{u + 1}) F
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i)
    (upperStarLowerStarAdjunction Ab.{u + 1} i)
    (comparisonAdjunction Ab.{u + 1} Z)
    (comparisonAdjunction Ab.{u + 1} D)
    (lowerStarCompComparisonLowerStarIso i Ab.{u + 1}).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  exact h

private theorem comparison_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology Ab.{u + 1}) :
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).hom.app F ≫
        (comparisonUpperStar Ab.{u + 1} X).map
          ((Etale.upperStarComp Ab.{u + 1} f g).hom.app F) =
      (upperStarComp Ab.{u + 1} f g).hom.app _ ≫
        (upperStar Ab.{u + 1} f).map
          ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app F) ≫
        (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app
          ((Etale.upperStar Ab.{u + 1} g).obj F) := by
  have h := (comparison_pullback_coherent.2.1).2.1 X Y Z f g F
  change (comparisonUpperStar Ab.{u + 1} X).map
      ((Etale.upperStarComp Ab.{u + 1} f g).hom.app F) ≫
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).inv.app
      ((Etale.upperStar Ab.{u + 1} g).obj F) ≫
    (upperStar Ab.{u + 1} f).map
      ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).inv.app F) =
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).inv.app F ≫
      (upperStarComp Ab.{u + 1} f g).hom.app _ at h
  apply (cancel_epi
    ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).inv.app F)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

section SquareProof
attribute [local irreducible] upperStar Etale.upperStar comparisonUpperStar
  upperStarComp Etale.upperStarComp comparisonUpperStarCompUpperStarIso

private theorem comp_transport {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : h = f ≫ g) :
    Etale.upperStarComp Ab.{u + 1} f g h w =
      eqToIso (congrArg (Etale.upperStar Ab.{u + 1}) w) ≪≫
        Etale.upperStarComp Ab.{u + 1} f g := by
  subst h
  simp

private theorem map_id_transport
    {B C : Type*} [Category B] [Category C] (ν : B ⥤ C)
    {X : B} {Y : C} (t : Y ⟶ ν.obj X) :
    t ≫ ν.map (𝟙 X) = 𝟙 Y ≫ t := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

private theorem comparison_transport_nat
    {I B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
    (L : I → B ⥤ C) (P : I → D ⥤ E) (ν : B ⥤ D) (μ : C ⥤ E)
    (c : ∀ t, ν ⋙ P t ≅ L t ⋙ μ) {f g : I} (h : g = f) :
    (c f).hom ≫ Functor.whiskerRight (eqToIso (congrArg L h)).symm.hom μ =
      Functor.whiskerLeft ν (eqToIso (congrArg P h.symm)).hom ≫ (c g).hom := by
  subst g
  ext X
  change (c f).hom.app X ≫ μ.map (𝟙 _) = 𝟙 _ ≫ (c f).hom.app X
  exact map_id_transport μ ((c f).hom.app X)

private theorem pro_square_iso {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    integralSquare i i' g gD sq =
      (upperStarComp Ab.{u + 1} i' g).symm ≪≫
        eqToIso (congrArg (upperStar Ab.{u + 1}) sq.w.symm) ≪≫
        upperStarComp Ab.{u + 1} gD i := by
  unfold integralSquare
  rfl

private theorem paste_components
    {B C : Type*} [Category B] [Category C] (ν : B ⥤ C)
    {A₁ A₂ B₁ B₂ : B} {P Q R S : C}
    (a : A₁ ⟶ A₂) (ai : A₂ ⟶ A₁) (b : B₁ ⟶ B₂) (t : A₁ ⟶ B₁)
    (pi : Q ⟶ P) (q : R ⟶ S) (z : P ⟶ R)
    (c : P ⟶ ν.obj A₁) (d : R ⟶ ν.obj B₁)
    (u : Q ⟶ ν.obj A₂) (v : S ⟶ ν.obj B₂) (e : A₂ ⟶ B₂) (s : Q ⟶ S)
    (hai : a ≫ ai = 𝟙 _) (ha : u = pi ≫ c ≫ ν.map a)
    (hb : d ≫ ν.map b = q ≫ v) (ht : c ≫ ν.map t = z ≫ d)
    (he : e = ai ≫ t ≫ b) (hs : s = pi ≫ z ≫ q) :
    u ≫ ν.map e = s ≫ v := by
  have hac : ν.map a ≫ ν.map ai = 𝟙 _ := by
    rw [← Functor.map_comp, hai, CategoryTheory.Functor.map_id]
  rw [ha, he, hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hac]
  rw [reassoc_of% ht, hb]

private theorem paste_components_assoc
    {B C : Type*} [Category B] [Category C] (ν : B ⥤ C)
    {A₁ A₂ B₁ B₂ : B} {P Q R S U V : C}
    (a : A₁ ⟶ A₂) (ai : A₂ ⟶ A₁) (b : B₁ ⟶ B₂) (t : A₁ ⟶ B₁)
    (pi : Q ⟶ P) (q : R ⟶ S) (z : P ⟶ R)
    (c : P ⟶ ν.obj A₁) (d : R ⟶ ν.obj B₁)
    (u₀ : Q ⟶ U) (u₁ : U ⟶ ν.obj A₂) (v₀ : S ⟶ V) (v₁ : V ⟶ ν.obj B₂)
    (e : A₂ ⟶ B₂) (s : Q ⟶ S)
    (hai : a ≫ ai = 𝟙 _) (ha : u₀ ≫ u₁ = pi ≫ c ≫ ν.map a)
    (hb : d ≫ ν.map b = q ≫ v₀ ≫ v₁) (ht : c ≫ ν.map t = z ≫ d)
    (he : e = ai ≫ t ≫ b) (hs : s = pi ≫ z ≫ q) :
    u₀ ≫ u₁ ≫ ν.map e = s ≫ v₀ ≫ v₁ := by
  simpa only [Category.assoc] using
    paste_components ν a ai b t pi q z c d (u₀ ≫ u₁) (v₀ ≫ v₁) e s
      hai ha hb ht he hs

private theorem iso_factor
    {C : Type*} [Category C] {P Q R S : C} (p : P ⟶ Q) (pi : Q ⟶ P)
    (hpi : pi ≫ p = 𝟙 _) (c : P ⟶ R) (m : R ⟶ S) (u : Q ⟶ S)
    (h : c ≫ m = p ≫ u) : u = pi ≫ c ≫ m := by
  have hh := congrArg (fun t ↦ pi ≫ t) h
  simpa only [Category.assoc, reassoc_of% hpi] using hh.symm

private theorem comparison_comp_forward {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology Ab.{u + 1}) :
    (upperStar Ab.{u + 1} f).map
        ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app F) ≫
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app
        ((Etale.upperStar Ab.{u + 1} g).obj F) =
    (upperStarComp Ab.{u + 1} f g).inv.app
        ((comparisonUpperStar Ab.{u + 1} Z).obj F) ≫
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).hom.app F ≫
      (comparisonUpperStar Ab.{u + 1} X).map
        ((Etale.upperStarComp Ab.{u + 1} f g).hom.app F) := by
  let C := Ab.{u + 1}
  exact iso_factor ((upperStarComp C f g).hom.app ((comparisonUpperStar C Z).obj F))
    ((upperStarComp C f g).inv.app ((comparisonUpperStar C Z).obj F))
    (Iso.inv_hom_id_app (upperStarComp C f g) ((comparisonUpperStar C Z).obj F))
    ((comparisonUpperStarCompUpperStarIso C (f ≫ g)).hom.app F)
    ((comparisonUpperStar C X).map ((Etale.upperStarComp C f g).hom.app F))
    ((upperStar C f).map ((comparisonUpperStarCompUpperStarIso C g).hom.app F) ≫
      (comparisonUpperStarCompUpperStarIso C f).hom.app ((Etale.upperStar C g).obj F))
    (comparison_comp f g F)


-- Keep the diagram calculation abstract: reducing components of the concrete
-- sheaf-pullback functors during equality transport unfolds large Kan extensions.
-- L₁, L₂ are the etale path g then i'; L₁', L₂' are i then gD.
-- R denotes the corresponding pro-etale paths, and K the site comparisons.
private structure ClosedSquareData
    (A₀ B B' C P Q Q' R : Type*) [Category A₀] [Category B] [Category B']
    [Category C] [Category P] [Category Q] [Category Q'] [Category R] where
  L₁ : A₀ ⥤ B
  L₂ : B ⥤ C
  L₁' : A₀ ⥤ B'
  L₂' : B' ⥤ C
  K₀ : A₀ ⥤ P
  K₁ : B ⥤ Q
  K₁' : B' ⥤ Q'
  K₂ : C ⥤ R
  R₁ : P ⥤ Q
  R₂ : Q ⥤ R
  R₁' : P ⥤ Q'
  R₂' : Q' ⥤ R
  c₁ : K₀ ⋙ R₁ ≅ L₁ ⋙ K₁
  c₂ : K₁ ⋙ R₂ ≅ L₂ ⋙ K₂
  c₁' : K₀ ⋙ R₁' ≅ L₁' ⋙ K₁'
  c₂' : K₁' ⋙ R₂' ≅ L₂' ⋙ K₂
  L : A₀ ⥤ C
  L' : A₀ ⥤ C
  T : P ⥤ R
  T' : P ⥤ R
  c : K₀ ⋙ T ≅ L ⋙ K₂
  c' : K₀ ⋙ T' ≅ L' ⋙ K₂
  a : L ≅ L₁ ⋙ L₂
  a' : L' ≅ L₁' ⋙ L₂'
  p : T ≅ R₁ ⋙ R₂
  p' : T' ≅ R₁' ⋙ R₂'
  e : L ≅ L'
  d : T ≅ T'
  se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂'
  sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂'

private structure ClosedSquareLaws
    {A₀ B B' C P Q Q' R : Type*} [Category A₀] [Category B] [Category B']
    [Category C] [Category P] [Category Q] [Category Q'] [Category R]
    (s : ClosedSquareData A₀ B B' C P Q Q' R) : Prop where
  ha : ∀ F, s.R₂.map (s.c₁.hom.app F) ≫ s.c₂.hom.app (s.L₁.obj F) =
    s.p.inv.app (s.K₀.obj F) ≫ s.c.hom.app F ≫ s.K₂.map (s.a.hom.app F)
  hb : ∀ F, s.c'.hom.app F ≫ s.K₂.map (s.a'.hom.app F) =
    s.p'.hom.app (s.K₀.obj F) ≫ s.R₂'.map (s.c₁'.hom.app F) ≫ s.c₂'.hom.app (s.L₁'.obj F)
  ht : s.c.hom ≫ Functor.whiskerRight s.e.hom s.K₂ =
    Functor.whiskerLeft s.K₀ s.d.hom ≫ s.c'.hom
  he : s.se = s.a.symm ≪≫ s.e ≪≫ s.a'
  hp : s.sp = s.p.symm ≪≫ s.d ≪≫ s.p'

private theorem closedSquare_component
    {A₀ B B' C P Q Q' R : Type*} [Category A₀] [Category B] [Category B']
    [Category C] [Category P] [Category Q] [Category Q'] [Category R]
    (s : ClosedSquareData A₀ B B' C P Q Q' R) (h : ClosedSquareLaws s) (F : A₀) :
    s.R₂.map (s.c₁.hom.app F) ≫ s.c₂.hom.app (s.L₁.obj F) ≫
        s.K₂.map (s.se.hom.app F) =
      s.sp.hom.app (s.K₀.obj F) ≫ s.R₂'.map (s.c₁'.hom.app F) ≫
        s.c₂'.hom.app (s.L₁'.obj F) := by
  have he : s.se.hom.app F = s.a.inv.app F ≫ s.e.hom.app F ≫ s.a'.hom.app F := by
    rw [h.he]
    rfl
  have hp : s.sp.hom.app (s.K₀.obj F) =
      s.p.inv.app (s.K₀.obj F) ≫ s.d.hom.app (s.K₀.obj F) ≫
        s.p'.hom.app (s.K₀.obj F) := by
    rw [h.hp]
    rfl
  have ht := congrArg (fun t ↦ t.app F) h.ht
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ht
  exact paste_components_assoc s.K₂ (s.a.hom.app F) (s.a.inv.app F)
    (s.a'.hom.app F) (s.e.hom.app F) (s.p.inv.app (s.K₀.obj F))
    (s.p'.hom.app (s.K₀.obj F)) (s.d.hom.app (s.K₀.obj F))
    (s.c.hom.app F) (s.c'.hom.app F) (s.R₂.map (s.c₁.hom.app F))
    (s.c₂.hom.app (s.L₁.obj F)) (s.R₂'.map (s.c₁'.hom.app F))
    (s.c₂'.hom.app (s.L₁'.obj F)) (s.se.hom.app F) (s.sp.hom.app (s.K₀.obj F))
    (Iso.hom_inv_id_app s.a F) (h.ha F) (h.hb F) ht he hp

private theorem etale_square_iso {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    Etale.squareUpperStarIso Ab.{u + 1} sq =
      (Etale.upperStarComp Ab.{u + 1} i' g).symm ≪≫
        (eqToIso (congrArg (Etale.upperStar Ab.{u + 1}) sq.w)).symm ≪≫
        Etale.upperStarComp Ab.{u + 1} gD i := by
  rw [Etale.squareUpperStarIso, comp_transport i' g (gD ≫ i) sq.w]
  simp only [Iso.trans_symm, Iso.trans_assoc]

private abbrev cartierSquareData {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    ClosedSquareData
      (Sheaf Z.smallEtaleTopology Ab.{u + 1})
      (Sheaf Z'.smallEtaleTopology Ab.{u + 1})
      (Sheaf D.smallEtaleTopology Ab.{u + 1})
      (Sheaf D'.smallEtaleTopology Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology D') Ab.{u + 1}) where
  L₁ := Etale.upperStar Ab.{u + 1} g
  L₂ := Etale.upperStar Ab.{u + 1} i'
  L₁' := Etale.upperStar Ab.{u + 1} i
  L₂' := Etale.upperStar Ab.{u + 1} gD
  K₀ := comparisonUpperStar Ab.{u + 1} Z
  K₁ := comparisonUpperStar Ab.{u + 1} Z'
  K₁' := comparisonUpperStar Ab.{u + 1} D
  K₂ := comparisonUpperStar Ab.{u + 1} D'
  R₁ := upperStar Ab.{u + 1} g
  R₂ := upperStar Ab.{u + 1} i'
  R₁' := upperStar Ab.{u + 1} i
  R₂' := upperStar Ab.{u + 1} gD
  c₁ := comparisonUpperStarCompUpperStarIso Ab.{u + 1} g
  c₂ := comparisonUpperStarCompUpperStarIso Ab.{u + 1} i'
  c₁' := comparisonUpperStarCompUpperStarIso Ab.{u + 1} i
  c₂' := comparisonUpperStarCompUpperStarIso Ab.{u + 1} gD
  L := Etale.upperStar Ab.{u + 1} (i' ≫ g)
  L' := Etale.upperStar Ab.{u + 1} (gD ≫ i)
  T := upperStar Ab.{u + 1} (i' ≫ g)
  T' := upperStar Ab.{u + 1} (gD ≫ i)
  c := comparisonUpperStarCompUpperStarIso Ab.{u + 1} (i' ≫ g)
  c' := comparisonUpperStarCompUpperStarIso Ab.{u + 1} (gD ≫ i)
  a := Etale.upperStarComp Ab.{u + 1} i' g
  a' := Etale.upperStarComp Ab.{u + 1} gD i
  p := upperStarComp Ab.{u + 1} i' g
  p' := upperStarComp Ab.{u + 1} gD i
  e := (eqToIso (congrArg (Etale.upperStar Ab.{u + 1}) sq.w)).symm
  d := eqToIso (congrArg (upperStar Ab.{u + 1}) sq.w.symm)
  se := Etale.squareUpperStarIso Ab.{u + 1} sq
  sp := integralSquare i i' g gD sq


private theorem cartier_law_ha {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    ∀ F, s.R₂.map (s.c₁.hom.app F) ≫ s.c₂.hom.app (s.L₁.obj F) =
    s.p.inv.app (s.K₀.obj F) ≫ s.c.hom.app F ≫ s.K₂.map (s.a.hom.app F) := by
  exact comparison_comp_forward i' g

private theorem cartier_law_hb {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    ∀ F, s.c'.hom.app F ≫ s.K₂.map (s.a'.hom.app F) =
    s.p'.hom.app (s.K₀.obj F) ≫ s.R₂'.map (s.c₁'.hom.app F) ≫ s.c₂'.hom.app (s.L₁'.obj F) := by
  exact comparison_comp gD i

private theorem cartier_law_ht {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    s.c.hom ≫ Functor.whiskerRight s.e.hom s.K₂ =
      Functor.whiskerLeft s.K₀ s.d.hom ≫ s.c'.hom := by
  exact comparison_transport_nat
    (Etale.upperStar Ab.{u + 1}) (upperStar Ab.{u + 1})
    (comparisonUpperStar Ab.{u + 1} Z)
    (comparisonUpperStar Ab.{u + 1} D')
    (fun t ↦ comparisonUpperStarCompUpperStarIso Ab.{u + 1} t) sq.w

private theorem cartier_law_he {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    s.se = s.a.symm ≪≫ s.e ≪≫ s.a' := by
  exact etale_square_iso i i' g gD sq

private theorem cartier_law_hp {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    s.sp = s.p.symm ≪≫ s.d ≪≫ s.p' := by
  exact pro_square_iso i i' g gD sq

private theorem cartierSquareLaws {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) : ClosedSquareLaws (cartierSquareData i i' g gD sq) where
  ha := cartier_law_ha i i' g gD sq
  hb := cartier_law_hb i i' g gD sq
  ht := cartier_law_ht i i' g gD sq
  he := cartier_law_he i i' g gD sq
  hp := cartier_law_hp i i' g gD sq


end SquareProof

private lemma transportedHom
    {B C D : Type*} [Category B] [Category C] [Category D]
    {L : B ⥤ C} {R : C ⥤ B} {P : C ⥤ D} {Q : D ⥤ C} {S : D ⥤ B}
    (a : L ⊣ R) (p : P ⊣ Q) (d : Q ⋙ R ≅ S)
    (M : B) (N : D) (t : L.obj M ⟶ Q.obj N) :
    ((a.comp p).ofNatIsoRight d).homEquiv M N ((p.homEquiv _ _).symm t) =
      a.homEquiv _ _ t ≫ d.hom.app N := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (p.homEquiv _ _ ((p.homEquiv _ _).symm t)) ≫ d.hom.app N = _
  rw [Equiv.apply_symm_apply]


private lemma comparison_constant_inverse
    (T : Scheme.{u}) (M : Ab.{u + 1}) :
  let D := Ab.{u + 1};
    (integralConstantComparison T).hom.app M =
      ConstantProof.constantInverse T.smallEtaleTopology (Scheme.ProEt.topology T)
        (Scheme.toProEt T)
        (comparisonAdjunction D T) M := by
  let D := Ab.{u + 1}
  let ae := constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)
  let ap := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let p := comparisonAdjunction D T
  let e := (Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso D
    T.smallEtaleTopology (Scheme.ProEt.topology T) (op (Scheme.Etale.mk (𝟙 T)))
  let ac := (ae.comp p).ofNatIsoRight e
  apply (ac.homEquiv _ _).injective
  have hc := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ap M
  change ac.homEquiv _ _ ((integralConstantComparison T).hom.app M) =
    ap.unit.app M at hc
  rw [hc]
  unfold ConstantProof.constantInverse
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change _ = ae.homEquiv _ _ (p.homEquiv _ _ ((p.homEquiv _ _).symm _)) ≫ _
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_apply, ae, ap, constantSheafAdj,
    Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    sheafificationAdjunction_unit_app, Category.id_comp]
  change (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const (Scheme.ProEt T)ᵒᵖ).obj M)).app
        (op ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj M)).app
      (op (Scheme.Etale.mk (𝟙 T))) ≫
        (ConstantProof.constantDirect T.smallEtaleTopology (Scheme.ProEt.topology T)
          (Scheme.toProEt T) M).hom.app (op (Scheme.Etale.mk (𝟙 T)))
  exact (ConstantProof.constantDirect_unit T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) M (op (Scheme.Etale.mk (𝟙 T)))).symm

private lemma etale_constant_inverse
    {X Y : Scheme.{u}} (h : X ⟶ Y) (M : Ab.{u + 1}) :
  let D := Ab.{u + 1};
    (Scheme.upperStarConstantSheafIso D h).hom.app M =
      ConstantProof.constantInverse Y.smallEtaleTopology X.smallEtaleTopology
        h.Etale (Etale.upperStarLowerStarAdjunction D h) M := by
  let D := Ab.{u + 1}
  let ay := constantSheafAdj Y.smallEtaleTopology D terminalIsTerminal
  let ax := constantSheafAdj X.smallEtaleTopology D terminalIsTerminal
  let p := Etale.upperStarLowerStarAdjunction D h
  let d := Etale.lowerStarCompSheafSectionsTerminalIso D h
  let ac := (ay.comp p).ofNatIsoRight d
  apply (ac.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ax M
  change ac.homEquiv _ _ ((Scheme.upperStarConstantSheafIso D h).hom.app M) =
    ax.unit.app M at hn
  rw [hn]
  unfold ConstantProof.constantInverse
  conv_rhs => erw [transportedHom ay p d]
  simp only [Adjunction.homEquiv_apply, ax, ay, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app,
    Category.id_comp, Category.assoc]
  change (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
      (op (⊤_ X.Etale)) =
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
      (op (⊤_ Y.Etale)) ≫
      (ConstantProof.constantDirect Y.smallEtaleTopology X.smallEtaleTopology h.Etale M).hom.app
        (op (⊤_ Y.Etale)) ≫
      ((constantSheaf X.smallEtaleTopology D).obj M).obj.map
        (PreservesTerminal.iso h.Etale).inv.op
  rw [← Category.assoc, ConstantProof.constantDirect_unit]
  have hn := (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj M)).naturality (PreservesTerminal.iso h.Etale).inv.op
  simpa only [constantSheaf, Functor.comp_obj, Functor.const_obj_map,
    Functor.const_obj_obj, Functor.op_obj, Category.id_comp] using hn

private theorem comparison_constants_general
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Ab.{u + 1}) :
  let D := Ab.{u + 1};
    (ProEtale.upperStar D f).map ((integralConstantComparison Y).hom.app M) ≫
        Scheme.proEtaleConstantInverseImageMap f D M =
      (comparisonUpperStarCompUpperStarIso D f).hom.app
          ((constantSheaf Y.smallEtaleTopology D).obj M) ≫
        (ProEtale.comparisonUpperStar D X).map
          ((Scheme.upperStarConstantSheafIso D f).hom.app
            M) ≫ (integralConstantComparison X).hom.app M := by
  let D := Ab.{u + 1}
  let ap := (ProEtale.comparisonAdjunction D Y).comp
    (Scheme.proEtaleSheafAdjunction f D)
  let ae := (Etale.upperStarLowerStarAdjunction D f).comp
    (ProEtale.comparisonAdjunction D X)
  let d := lowerStarCompComparisonLowerStarIso f D
  have hd (S : Sheaf (Scheme.ProEt.topology X) D) (W : Y.Etaleᵒᵖ) :
      ((d.inv.app S).hom.app W) = 𝟙 _ := by
    dsimp only [d, lowerStarCompComparisonLowerStarIso]
    change ((𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact S.obj.map_id _
  simp only [comparison_constant_inverse, etale_constant_inverse]
  change (ProEtale.upperStar D f).map _ ≫
      ConstantProof.constantInverse (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (Scheme.proEtaleBaseChange f) (upperStarLowerStarAdjunction D f) M = _
  apply (ap.homEquiv _ _).injective
  change _ = ap.homEquiv _ _
    (((conjugateIsoEquiv ap ae).symm d).inv.app _ ≫ _)
  have hm := ConstantProof.homEquiv_mate ap ae d.symm
    ((ProEtale.comparisonUpperStar D X).map
      (ConstantProof.constantInverse Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (Etale.upperStarLowerStarAdjunction D f) M) ≫
      ConstantProof.constantInverse X.smallEtaleTopology (Scheme.ProEt.topology X)
        (Scheme.toProEt X)
        (ProEtale.comparisonAdjunction D X) M)
  simp only [Iso.symm_symm_eq] at hm
  erw [hm]
  have hp := ConstantProof.constantInverse_composite_adjunct Y.smallEtaleTopology
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (Scheme.toProEt Y)
    (Scheme.proEtaleBaseChange f)
    (ProEtale.comparisonAdjunction D Y) (Scheme.proEtaleSheafAdjunction f D)
    M
  have he := ConstantProof.constantInverse_composite_adjunct Y.smallEtaleTopology
    X.smallEtaleTopology (Scheme.ProEt.topology X) f.Etale (Scheme.toProEt X)
    (Etale.upperStarLowerStarAdjunction D f)
    (ProEtale.comparisonAdjunction D X) M
  erw [hp, he]
  apply ((sheafificationAdjunction Y.smallEtaleTopology D).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  simp only [sheafificationAdjunction_unit_app, NatTrans.comp_app, Category.assoc]
  change (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (ConstantProof.constantDirect Y.smallEtaleTopology (Scheme.ProEt.topology Y)
        (Scheme.toProEt Y)
        M).hom.app W ≫
      (ConstantProof.constantDirect (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (Scheme.proEtaleBaseChange f)
        M).hom.app ((Scheme.toProEt Y).op.obj W) =
    (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (ConstantProof.constantDirect Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        M).hom.app W ≫
      (ConstantProof.constantDirect X.smallEtaleTopology (Scheme.ProEt.topology X)
        (Scheme.toProEt X)
        M).hom.app (f.Etale.op.obj W) ≫
      ((d.inv.app ((constantSheaf (Scheme.ProEt.topology X) D).obj
        M)).hom.app W)
  rw [hd]
  rw [← Category.assoc, ConstantProof.constantDirect_unit, ConstantProof.constantDirect_unit,
    ← Category.assoc, ← Category.assoc, ConstantProof.constantDirect_unit,
    ConstantProof.constantDirect_unit]
  erw [Category.comp_id]
  rfl


private theorem comparison_constants {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Ab.{u + 1} f).map
        (((integralConstantComparison Y).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) ≫
      Scheme.proEtaleConstantInverseImageMap f Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app
        (Etale.supportedIntegralConstant Y) ≫
      (comparisonUpperStar Ab.{u + 1} X).map
        (((Scheme.upperStarConstantSheafIso Ab.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) ≫
      (((integralConstantComparison X).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) := by
  exact comparison_constants_general f (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private theorem integralConstantComparison_app (X : Scheme.{u}) :
    (integralConstantComparison X).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      cartierIntegralConstantComparisonIso X := by
  rfl

private theorem integralSourceIso_hom {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] :
    (cartierIntegralSourceIso i).hom = cartierIntegralSourceComparison i := by
  rfl

private theorem integralSource_cancel {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] :
    (cartierIntegralSourceIso i).inv ≫ cartierIntegralSourceComparison i = 𝟙 _ := by
  exact (cartierIntegralSourceIso i).inv_hom_id

attribute [local irreducible] lowerStar Etale.upperStar Etale.lowerStar
  comparisonUpperStar integralConstantComparison cartierIntegralConstantComparisonIso
  cartierIntegralSourceComparison cartierIntegralSourceIso
  upperStarLowerStarAdjunction Etale.upperStarLowerStarAdjunction
  Functor.sheafPullbackConstruction.sheafPullback


private theorem source_counit {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (upperStar Ab.{u + 1} i).map (cartierIntegralSourceComparison i) ≫
        (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
          (integralConstant D) =
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} i).hom.app
          ((Etale.lowerStar Ab.{u + 1} i).obj
            (Etale.supportedIntegralConstant D)) ≫
        (comparisonUpperStar Ab.{u + 1} D).map
          ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
            (Etale.supportedIntegralConstant D)) ≫
        ((integralConstantComparison D).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom := by
  unfold cartierIntegralSourceComparison integralConstant
  rw [← integralConstantComparison_app, Functor.map_comp, Category.assoc]
  have hn := (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.naturality
    (((integralConstantComparison D).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, ← Category.assoc]
  simp only [Etale.supportedIntegralConstant, Functor.comp_obj]
  rw [comparison_counit, Category.assoc]


private theorem etale_exchange_counit {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    (Etale.upperStar Ab.{u + 1} i').map
        (Etale.relativeExtensionExchange i i' g gD sq) ≫
      (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i').counit.app
        (Etale.supportedIntegralConstant D') =
    (Etale.squareUpperStarIso Ab.{u + 1} sq).hom.app _ ≫
      (Etale.upperStar Ab.{u + 1} gD).map
        ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
          (Etale.supportedIntegralConstant D)) ≫
      ((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom := by
  unfold Etale.relativeExtensionExchange
  rw [Functor.map_comp, Category.assoc]
  have hn := (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i').counit.naturality
    (((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have hb := Etale.upperStar_map_baseChangeMap_app_counit Ab.{u + 1} sq
    (Etale.supportedIntegralConstant D)
  simpa only [Category.assoc, Functor.comp_obj, Functor.id_obj,
    Etale.supportedIntegralConstant] using congrArg (fun t ↦ t ≫
    ((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) hb


-- The mate argument uses only square coherence, the two source-counit equations,
-- and compatibility of the constant maps. Work in abstract categories so that
-- associativity and naturality never unfold a concrete sheaf construction.
private theorem closedExchange_mates
    {A₀ B B' C P Q Q' R : Type*} [Category A₀] [Category B] [Category B']
    [Category C] [Category P] [Category Q] [Category Q'] [Category R]
    (s : ClosedSquareData A₀ B B' C P Q Q' R)
    (r : B' ⥤ A₀) (r' : C ⥤ B) (rp : Q' ⥤ P) (rp' : R ⥤ Q)
    (a : s.R₂ ⊣ rp') (F : B') (F' : C) (G : Q') (G' : R)
    (eps : s.L₁'.obj (r.obj F) ⟶ F) (eps' : s.L₂.obj (r'.obj F') ⟶ F')
    (ep : s.R₁'.obj (rp.obj G) ⟶ G)
    (cc : s.K₁'.obj F ⟶ G) (cc' : s.K₂.obj F' ⟶ G')
    (cm : s.L₂'.obj F ⟶ F') (cp : s.R₂'.obj G ⟶ G')
    (t : s.K₀.obj (r.obj F) ⟶ rp.obj G)
    (t' : s.K₁.obj (r'.obj F') ⟶ rp'.obj G')
    (ex : s.L₁.obj (r.obj F) ⟶ r'.obj F')
    (h : ClosedSquareLaws s)
    (ht : s.R₁'.map t ≫ ep = s.c₁'.hom.app (r.obj F) ≫ s.K₁'.map eps ≫ cc)
    (ht' : s.R₂.map t' ≫ a.counit.app G' =
      s.c₂.hom.app (r'.obj F') ≫ s.K₂.map eps' ≫ cc')
    (hc : s.R₂'.map cc ≫ cp = s.c₂'.hom.app F ≫ s.K₂.map cm ≫ cc')
    (he : s.L₂.map ex ≫ eps' = s.se.hom.app (r.obj F) ≫ s.L₂'.map eps ≫ cm) :
    s.R₁.map t ≫ (a.homEquiv _ _)
        (s.sp.hom.app (rp.obj G) ≫ s.R₂'.map ep ≫ cp) =
      s.c₁.hom.app (r.obj F) ≫ s.K₁.map ex ≫ t' := by
  apply (a.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := s.sp.hom.naturality t
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← s.R₂'.map_comp_assoc, ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc]
  have hn' := s.c₂'.hom.naturality eps
  simp only [Functor.comp_map] at hn'
  rw [reassoc_of% hn', ← reassoc_of% closedSquare_component s h (r.obj F), ht']
  have hn'' := s.c₂.hom.naturality ex
  simp only [Functor.comp_map] at hn''
  rw [reassoc_of% hn'']
  simp only [← Functor.map_comp_assoc]
  rw [he]

/-- Site comparison intertwines the two closed exchanges on constant modules.
-/
private theorem sourceComparison_closed_exchange
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar Ab.{u + 1} g).map (cartierIntegralSourceComparison i) ≫
        integralExchange i i' g gD sq =
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app
          ((Etale.lowerStar Ab.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ≫
        (comparisonUpperStar Ab.{u + 1} Z').map
          (Etale.relativeExtensionExchange i i' g gD sq) ≫
        cartierIntegralSourceComparison i' := by
  unfold integralExchange
  exact closedExchange_mates (cartierSquareData i i' g gD sq)
    (Etale.lowerStar Ab.{u + 1} i)
    (Etale.lowerStar Ab.{u + 1} i')
    (lowerStar Ab.{u + 1} i)
    (lowerStar Ab.{u + 1} i')
    (upperStarLowerStarAdjunction Ab.{u + 1} i')
    (Etale.supportedIntegralConstant D) (Etale.supportedIntegralConstant D')
    (integralConstant D) (integralConstant D')
    ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app _)
    ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i').counit.app _)
    ((upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app _)
    (((integralConstantComparison D).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
    (((integralConstantComparison D').app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
    (((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
    (Scheme.proEtaleConstantInverseImageMap gD Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (cartierIntegralSourceComparison i) (cartierIntegralSourceComparison i')
    (Etale.relativeExtensionExchange i i' g gD sq)
    (cartierSquareLaws i i' g gD sq)
    (source_counit i) (source_counit i')
    (comparison_constants gD) (etale_exchange_counit i i' g gD sq)


section InverseExchange
attribute [local irreducible] upperStar

private theorem sourceComparison_inverse_exchange
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar Ab.{u + 1} g).map (cartierIntegralSourceIso i).inv ≫
        (comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app
          ((Etale.lowerStar Ab.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ≫
        (comparisonUpperStar Ab.{u + 1} Z').map
          (Etale.relativeExtensionExchange i i' g gD sq) ≫
        (cartierIntegralSourceIso i').hom = integralExchange i i' g gD sq := by
  rw [integralSourceIso_hom, ← sourceComparison_closed_exchange i i' g gD sq,
    ← Functor.map_comp_assoc, integralSource_cancel,
    CategoryTheory.Functor.map_id, Category.id_comp]

end InverseExchange

/-- The transported integral boundary source is the canonical ordinary closed exchange. -/
theorem diagonalBoundarySource_exchange {Y Y' : Scheme.{u}}
    (v : diagonalSurface Y' ⟶ diagonalSurface Y)
    (w : ProjectiveLine Y' ⟶ ProjectiveLine Y)
    (sq : CommSq w (diagonalImmersion Y') (diagonalImmersion Y) v) :
    DiagonalCoefficients.diagonalBoundarySource v w sq =
      integralExchange (diagonalImmersion Y) (diagonalImmersion Y') v w sq := by
  exact sourceComparison_inverse_exchange
    (diagonalImmersion Y) (diagonalImmersion Y') v w sq

end IntegralSourceExchange
end AlgebraicGeometry.ProEtale
