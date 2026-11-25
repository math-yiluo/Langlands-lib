/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemAcyclicResolution
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemOrdinaryCokernel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Invertibility of the integral reduction mate

Source: blueprint classes proof (2), integral quotient reduction.
(blueprint: lem-sp-tower-reduction-mate-invertible).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

attribute [local implicit_reducible]
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  CategoryTheory.PowerTransition.functor CategoryTheory.PowerTransition.obj
  AlgebraicGeometry.ProEtale.spCoefficientCommRings
  AlgebraicGeometry.ProEtale.SpTowerClasses.abPull

set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem cokernel_comparison_isIso
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B Q Q' : C} {f f' : A ⟶ B} {p : B ⟶ Q} {p' : B ⟶ Q'}
    {hp : f ≫ p = 0} {hp' : f' ≫ p' = 0}
    (h : IsColimit (CokernelCofork.ofπ p hp))
    (h' : IsColimit (CokernelCofork.ofπ p' hp')) (hff : f = f')
    (u : Q ⟶ Q') (hu : p ≫ u = p') : IsIso u := by
  subst f'
  let e := h.coconePointUniqueUpToIso h'
  have he : p ≫ e.hom = p' :=
    h.comp_coconePointUniqueUpToIso_hom h' WalkingParallelPair.one
  have : Epi p := Cofork.IsColimit.epi h
  have : u = e.hom := (cancel_epi p).1 (hu.trans he.symm)
  rw [this]
  infer_instance

private def ordinaryMate {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    abPull f ⋙ cX.reduction.ordinary ⟶ cY.reduction.ordinary ⋙ d.pull :=
  ((mateEquiv cY.reduction.model.adjunction cX.reduction.model.adjunction).symm
    (TwoSquare.mk _ _ _ _ d.forgetIso.hom))

private theorem ordinaryMate_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    IsIso (ordinaryMate l E d) := by
  let rY := cY.reduction
  let rX := cX.reduction
  let := forget_faithful l X rX.forget
  have h (M : Ab Y) : IsIso ((ordinaryMate l E d).app M) := by
    let u := rX.forget.F.map ((ordinaryMate l E d).app M) ≫
      d.forgetIso.inv.app (rY.ordinary.obj M)
    have hu : rX.model.adjunction.unit.app ((abPull f).obj M) ≫ u =
        (abPull f).map (rY.model.adjunction.unit.app M) := by
      have h := unit_mateEquiv_symm rY.model.adjunction rX.model.adjunction
        (TwoSquare.mk _ _ _ _ d.forgetIso.hom) M
      change (abPull f).map (rY.model.adjunction.unit.app M) ≫
          d.forgetIso.hom.app (rY.ordinary.obj M) =
        rX.model.adjunction.unit.app ((abPull f).obj M) ≫
          rX.forget.F.map ((ordinaryMate l E d).app M) at h
      dsimp only [u]
      rw [← Category.assoc, ← h]
      simp only [Category.assoc, Iso.hom_inv_id_app]
      erw [Category.comp_id]
    have huIso : IsIso u := by
      have h (n : ℕᵒᵖ) : IsIso (u.app n) := by
        obtain ⟨hy, ⟨hY⟩⟩ := powerSystem_ordinary_cokernel l Y rY M
        obtain ⟨hx, ⟨hX⟩⟩ :=
          powerSystem_ordinary_cokernel l X rX ((abPull f).obj M)
        let ev := (evaluation ℕᵒᵖ (DiagonalAb X)).obj n
        have hX' := isColimitCoforkMapOfIsColimit' ev hx hX
        have hY' := isColimitCoforkMapOfIsColimit' (abPull f ⋙ ev) hy hY
        have hm : (abPull f ⋙ ev).map ((PowerTransition.multiplication l).app M) =
            ev.map ((PowerTransition.multiplication l).app ((abPull f).obj M)) := by
          change (upperStar AddCommGrpCat.{u + 1} f).map
            (l ^ (n.unop + 1) • 𝟙 (M.obj n)) =
              l ^ (n.unop + 1) • 𝟙 ((upperStar AddCommGrpCat.{u + 1} f).obj (M.obj n))
          rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
        exact cokernel_comparison_isIso hX' hY' hm.symm (u.app n)
          (congrArg (fun z ↦ z.app n) hu)
      have := h
      exact NatIso.isIso_of_isIso_app _
    have : IsIso (rX.forget.F.map ((ordinaryMate l E d).app M)) :=
      IsIso.of_isIso_comp_right _ (d.forgetIso.inv.app (rY.ordinary.obj M))
    exact isIso_of_reflects_iso _ rX.forget.F
  have := h
  exact NatIso.isIso_of_isIso_app _

section Comparison
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {EY : A ⥤ B} {UY : B ⥤ A} {EX : C ⥤ D} {UX : D ⥤ C}
  [EY.Additive] [UY.Additive] [EX.Additive] [UX.Additive]
  [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]
  [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
  (rY : DerivedExtension EY UY) (rX : DerivedExtension EX UX)
  (F : A ⥤ C) (P : B ⥤ D)
  [F.Additive] [P.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

private theorem reduction_unit_transpose (K : CochainComplex A ℤ) :
    rY.derivedAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
        UY.mapDerivedCategory.map (rY.epsilon.app K) ≫
        UY.mapDerivedCategoryFactors.hom.app ((EY.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((rY.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have h := rY.transpose K ((EY.mapHomologicalComplex (.up ℤ)).obj K) (𝟙 _)
  simp only [Adjunction.homEquiv_unit] at h
  erw [DerivedCategory.Q.map_id, Category.comp_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at h
  simpa only [Category.assoc] using h

private theorem exact_square_factors (e : UY ⋙ F ≅ P ⋙ UX)
    (K : CochainComplex B ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        UX.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
        UX.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj K) =
      F.mapDerivedCategory.map (UY.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((UY.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors UY F K]
  erw [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact Category.assoc _ _ _

private theorem mate_representative (e : UY ⋙ F ≅ P ⋙ UX)
    (a : F ⋙ EX ≅ EY ⋙ P)
    (ha : ∀ M, rX.adjunction.unit.app (F.obj M) ≫ UX.map (a.hom.app M) =
      F.map (rY.adjunction.unit.app M) ≫ e.hom.app (EY.obj M))
    (K : CochainComplex A ℤ) :
    let m := ((mateEquiv rY.derivedAdjunction rX.derivedAdjunction).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).hom))
    let ac := Functor.mapHomologicalComplexCompIso a (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (EY ⋙ P)) (.up ℤ)).symm
    m.app (DerivedCategory.Q.obj K) ≫
        P.mapDerivedCategory.map (rY.epsilon.app K) ≫
        P.mapDerivedCategoryFactors.hom.app ((EY.mapHomologicalComplex (.up ℤ)).obj K) =
      rX.derived.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        rX.epsilon.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (ac.hom.app K) := by
  dsimp only
  let m := ((mateEquiv rY.derivedAdjunction rX.derivedAdjunction).symm
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).hom))
  let ac := Functor.mapHomologicalComplexCompIso a (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (EY ⋙ P)) (.up ℤ)).symm
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Ec := EY.mapHomologicalComplex (.up ℤ)
  let Pc := P.mapHomologicalComplex (.up ℤ)
  let Uc := UX.mapHomologicalComplex (.up ℤ)
  have hc : (rX.adjunction.mapHomologicalComplex (.up ℤ)).unit.app (Fc.obj K) ≫
      Uc.map (ac.hom.app K) =
      Fc.map ((rY.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app (Ec.obj K) := by
    apply HomologicalComplex.Hom.ext
    funext i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Adjunction.mapHomologicalComplex_unit_app_f, ac, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
      NatTrans.id_app,
      NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
      Fc, Ec, Uc]
    erw [Category.comp_id]
    exact ha (K.X i)
  apply (rX.derivedAdjunction.homEquiv _ _).injective
  apply (cancel_mono (UX.mapDerivedCategoryFactors.hom.app (Pc.obj (Ec.obj K)))).1
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hm := unit_mateEquiv_symm rY.derivedAdjunction rX.derivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).hom)
    (DerivedCategory.Q.obj K)
  change F.mapDerivedCategory.map (rY.derivedAdjunction.unit.app _) ≫
      (Functor.mapDerivedCategorySquareIso e).hom.app _ =
    rX.derivedAdjunction.unit.app _ ≫ UX.mapDerivedCategory.map (m.app _) at hm
  rw [← reassoc_of% hm]
  have hn := (Functor.mapDerivedCategorySquareIso e).hom.naturality (rY.epsilon.app K)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  rw [exact_square_factors F P e (Ec.obj K)]
  rw [← F.mapDerivedCategory.map_comp_assoc, ← F.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  rw [reduction_unit_transpose rY K]
  have hF := F.mapDerivedCategoryFactors.hom.naturality
    ((rY.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj] at hF
  rw [reassoc_of% hF]
  have hunit := rX.derivedAdjunction.unit.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map,
    CategoryTheory.Functor.comp_obj] at hunit
  rw [← reassoc_of% hunit]
  have ht := rX.transpose (Fc.obj K) (Pc.obj (Ec.obj K)) (ac.hom.app K)
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at ht
  rw [ht]
  simp only [← Functor.map_comp]
  exact congrArg (fun z ↦ F.mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map z) hc.symm
end Comparison

private theorem regular_reduction_computes (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (K : CochainComplex (Ab T) ℤ)
    (hK : ∀ (i : ℤ) (n : ℕ), Mono (l ^ (n + 1) • 𝟙 ((K.X i).obj (op n)))) :
    IsIso (r.model.epsilon.app K) := by
  apply counit_computes_of_resolving r.model
    (fun P ↦ ∀ (i : ℤ) (n : ℕ), Mono (l ^ (n + 1) • 𝟙 ((P.X i).obj (op n))))
      ?_ ?_ K hK
  · intro L
    obtain ⟨P, q, hq, hP, _⟩ := powerSystem_acyclic_resolution l T r L
    exact ⟨P, q, hP, hq⟩
  · intro P Q q hP hQ hq
    exact reduction_preserves_regular_quasiIso l T r q hP hQ hq

/-- The canonical mate of the derived forgetful square. Its construction uses only
adjunction units and counits, with no choices of normalized endpoints.
Source: classes (2), reduction/pullback comparison
(blueprint: lem-sp-tower-reduction-mate-invertible). -/
def reductionPullbackMate {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    (abPull f).mapDerivedCategory ⋙ cX.reduction.derived ⟶
      cY.reduction.derived ⋙ d.pull.mapDerivedCategory :=
  ((mateEquiv cY.reduction.derivedAdjunction cX.reduction.derivedAdjunction).symm
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d.forgetIso).hom))

/-- Exact geometric inverse image commutes with integral quotient reduction, before
specifying either the integer or Kummer normalization.

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
classes proof (2); reduction-pullback proof steps 1--2
(blueprint: lem-sp-tower-reduction-mate-invertible).

Proof: the ordinary adjunction units are cokernels of the variable-power maps
on entire towers. Evaluate at each level. Exact abelian inverse image preserves
these cokernels and integer multiplication, so the ordinary mate identifies two
cokernels of the same map and is invertible. The faithful exact forgetful functor
reflects this invertibility back to quotient-module systems.

Every complex has a quasi-isomorphic resolution whose levelwise prime-power
multiplications are monic. The resolving-class computation of ordinary reduction
makes its specified universal-derived counit invertible on every such complex.
Exact inverse image preserves this regularity, so both derived counits compute
on the same resolution. Transpose through the target derived adjunction and use
the recorded representative transpose equations. Naturality of the localized
forgetful square identifies the specified derived mate, followed by the source
counit and exact-pullback factor, with the target counit followed by the localized
ordinary mate. All these comparison factors are invertible on the resolution.
Thus the specified mate is invertible there, and naturality transports this to
every derived object. No endpoint normalization or Kummer boundary is used. -/
theorem tower_reductionMate_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    IsIso (reductionPullbackMate l E d) := by
  have := ordinaryMate_isIso l E d
  let a := asIso (ordinaryMate l E d)
  have ha (M : Ab Y) :
      cX.reduction.model.adjunction.unit.app ((abPull f).obj M) ≫
        cX.reduction.forget.F.map (a.hom.app M) =
      (abPull f).map (cY.reduction.model.adjunction.unit.app M) ≫
        d.forgetIso.hom.app (cY.reduction.ordinary.obj M) :=
    (unit_mateEquiv_symm cY.reduction.model.adjunction cX.reduction.model.adjunction
      (TwoSquare.mk _ _ _ _ d.forgetIso.hom) M).symm
  have h (M : DerivedCategory (Ab Y)) :
      IsIso ((reductionPullbackMate l E d).app M) := by
    let K := DerivedCategory.Q.objPreimage M
    obtain ⟨P, q, hq, hP, hY⟩ :=
      powerSystem_acyclic_resolution l Y cY.reduction K
    let FP := ((abPull f).mapHomologicalComplex (.up ℤ)).obj P
    have hpull : ∀ (i : ℤ) (n : ℕ),
        Mono (l ^ (n + 1) • 𝟙 ((FP.X i).obj (op n))) := by
      intro i n
      have := hP i n
      have hm := (upperStar AddCommGrpCat.{u + 1} f).map_mono
        (l ^ (n + 1) • 𝟙 ((P.X i).obj (op n)))
      rw [Functor.map_nsmul] at hm
      erw [CategoryTheory.Functor.map_id] at hm
      exact hm
    have := hY
    have := regular_reduction_computes l X cX.reduction _ hpull
    have hrep := mate_representative cY.reduction.model cX.reduction.model
      (abPull f) d.pull d.forgetIso a ha P
    have hPiso : IsIso ((reductionPullbackMate l E d).app
        (DerivedCategory.Q.obj P)) := by
      apply IsIso.of_isIso_fac_right hrep
    have : QuasiIso q := hq
    have : IsIso (DerivedCategory.Q.map q) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
    let e := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso M
    have hh := (reductionPullbackMate l E d).naturality e.hom
    have : IsIso (((abPull f).mapDerivedCategory ⋙ cX.reduction.derived).map e.hom ≫
        (reductionPullbackMate l E d).app M) := by
      rw [hh]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (((abPull f).mapDerivedCategory ⋙ cX.reduction.derived).map e.hom)
      ((reductionPullbackMate l E d).app M)
  have := h
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale.SpTowerClasses
