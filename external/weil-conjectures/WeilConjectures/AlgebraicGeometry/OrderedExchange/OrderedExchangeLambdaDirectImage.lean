/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeRhoLambda
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Restriction commutes with the direct-image/derived-limit comparisons

All five comparisons in `lambda_directImageRlimIso_aux` are adjunction mates of exact descents of
ordinary identity-component squares. Transposing along the constant-diagram and tower-pullback
adjunctions reduces the equation to a cube of such squares, which is checked on complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

section SquareIsoQ

variable {𝒜 ℬ ℬ' ℰ : Type*} [Category 𝒜] [Category ℬ] [Category ℬ'] [Category ℰ]
  [Abelian 𝒜] [Abelian ℬ] [Abelian ℬ'] [Abelian ℰ] [HasDerivedCategory 𝒜]
  [HasDerivedCategory ℬ] [HasDerivedCategory ℬ'] [HasDerivedCategory ℰ]
  {F₁ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ ℰ} {G₁ : 𝒜 ⥤ ℬ'} {G₂ : ℬ' ⥤ ℰ}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- The levelwise square of complexes, with source and target in iterated form. -/
@[simps f]
def squareChainMap (e : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) (K : CochainComplex 𝒜 ℤ) :
    (F₂.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (G₂.mapHomologicalComplex (.up ℤ)).obj ((G₁.mapHomologicalComplex (.up ℤ)).obj K) where
  f i := e.app (K.X i)
  comm' i j _ := by simpa using (e.naturality (K.d i j)).symm

/-- On a complex, the exact descent of a square is the levelwise square, after the
factorization isomorphisms. -/
@[reassoc]
theorem mapDerivedCategorySquareIso_hom_app_Q (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (K : CochainComplex 𝒜 ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (squareChainMap e.hom K) := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    ← mapDerivedCategoryCompIso_hom_app_factors_assoc F₁ F₂ K, Iso.hom_inv_id_app_assoc]
  rfl

/-- The inverse form of `mapDerivedCategorySquareIso_hom_app_Q`. -/
@[reassoc]
theorem mapDerivedCategorySquareIso_inv_app_Q (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (K : CochainComplex 𝒜 ℤ) :
    (mapDerivedCategorySquareIso e).inv.app (DerivedCategory.Q.obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) =
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (squareChainMap e.inv K) := by
  have h := mapDerivedCategorySquareIso_hom_app_Q e K
  have hid : squareChainMap e.hom K ≫ squareChainMap e.inv K = 𝟙 _ := by
    ext i
    simp
  rw [← cancel_epi ((mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K)),
    Iso.hom_inv_id_app_assoc, reassoc_of% h, ← DerivedCategory.Q.map_comp, hid,
    DerivedCategory.Q.map_id, Category.comp_id]

end SquareIsoQ

section Cube

variable {C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Category C₃] [Category C₄] [Category C₅] [Category C₆] [Category C₇]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄] [Abelian C₅] [Abelian C₆]
  [Abelian C₇] [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄] [HasDerivedCategory C₅]
  [HasDerivedCategory C₆] [HasDerivedCategory C₇]
  {rV : C₀ ⥤ C₁} {δV : C₁ ⥤ C₂} {πc : C₂ ⥤ C₃} {κV : C₀ ⥤ C₄} {ρV : C₄ ⥤ C₂}
  {πt : C₄ ⥤ C₅} {ρU : C₅ ⥤ C₃} {pd : C₀ ⥤ C₆} {κU : C₆ ⥤ C₅} {pc : C₁ ⥤ C₇}
  {δU : C₇ ⥤ C₃} {rU : C₆ ⥤ C₇}
  [rV.Additive] [PreservesFiniteLimits rV] [PreservesFiniteColimits rV]
  [δV.Additive] [PreservesFiniteLimits δV] [PreservesFiniteColimits δV]
  [πc.Additive] [PreservesFiniteLimits πc] [PreservesFiniteColimits πc]
  [κV.Additive] [PreservesFiniteLimits κV] [PreservesFiniteColimits κV]
  [ρV.Additive] [PreservesFiniteLimits ρV] [PreservesFiniteColimits ρV]
  [πt.Additive] [PreservesFiniteLimits πt] [PreservesFiniteColimits πt]
  [ρU.Additive] [PreservesFiniteLimits ρU] [PreservesFiniteColimits ρU]
  [pd.Additive] [PreservesFiniteLimits pd] [PreservesFiniteColimits pd]
  [κU.Additive] [PreservesFiniteLimits κU] [PreservesFiniteColimits κU]
  [pc.Additive] [PreservesFiniteLimits pc] [PreservesFiniteColimits pc]
  [δU.Additive] [PreservesFiniteLimits δU] [PreservesFiniteColimits δU]
  [rU.Additive] [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]

/-- A cube of exact functors whose ordinary faces commute has commuting derived faces. -/
theorem mapDerivedCategory_cube (aV : rV ⋙ δV ≅ κV ⋙ ρV) (b : ρV ⋙ πc ≅ πt ⋙ ρU)
    (c : κV ⋙ πt ≅ pd ⋙ κU) (e : δV ⋙ πc ≅ pc ⋙ δU) (f : pd ⋙ rU ≅ rV ⋙ pc)
    (aU : rU ⋙ δU ≅ κU ⋙ ρU)
    (h : ∀ M : C₀, πc.map (aV.hom.app M) ≫ b.hom.app (κV.obj M) ≫ ρU.map (c.hom.app M) =
      e.hom.app (rV.obj M) ≫ δU.map (f.inv.app M) ≫ aU.hom.app (pd.obj M))
    (P : DerivedCategory C₀) :
    πc.mapDerivedCategory.map ((mapDerivedCategorySquareIso aV).hom.app P) ≫
        (mapDerivedCategorySquareIso b).hom.app (κV.mapDerivedCategory.obj P) ≫
        ρU.mapDerivedCategory.map ((mapDerivedCategorySquareIso c).hom.app P) =
      (mapDerivedCategorySquareIso e).hom.app (rV.mapDerivedCategory.obj P) ≫
        δU.mapDerivedCategory.map ((mapDerivedCategorySquareIso f).inv.app P) ≫
        (mapDerivedCategorySquareIso aU).hom.app (pd.mapDerivedCategory.obj P) := by
  have key : ∀ K : CochainComplex C₀ ℤ,
      πc.mapDerivedCategory.map ((mapDerivedCategorySquareIso aV).hom.app
          (DerivedCategory.Q.obj K)) ≫
        (mapDerivedCategorySquareIso b).hom.app (κV.mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) ≫
        ρU.mapDerivedCategory.map ((mapDerivedCategorySquareIso c).hom.app
          (DerivedCategory.Q.obj K)) =
      (mapDerivedCategorySquareIso e).hom.app (rV.mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) ≫
        δU.mapDerivedCategory.map ((mapDerivedCategorySquareIso f).inv.app
          (DerivedCategory.Q.obj K)) ≫
        (mapDerivedCategorySquareIso aU).hom.app (pd.mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) := by
    intro K
    let Φ := ρU.mapDerivedCategory.mapIso (κU.mapDerivedCategory.mapIso
        (pd.mapDerivedCategoryFactors.app K)) ≪≫
      ρU.mapDerivedCategory.mapIso (κU.mapDerivedCategoryFactors.app
        ((pd.mapHomologicalComplex (.up ℤ)).obj K)) ≪≫
      ρU.mapDerivedCategoryFactors.app ((κU.mapHomologicalComplex (.up ℤ)).obj
        ((pd.mapHomologicalComplex (.up ℤ)).obj K))
    rw [← cancel_mono Φ.hom]
    have hΦ : Φ.hom = ρU.mapDerivedCategory.map (κU.mapDerivedCategory.map
        (pd.mapDerivedCategoryFactors.hom.app K)) ≫
      ρU.mapDerivedCategory.map (κU.mapDerivedCategoryFactors.hom.app
        ((pd.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      ρU.mapDerivedCategoryFactors.hom.app ((κU.mapHomologicalComplex (.up ℤ)).obj
        ((pd.mapHomologicalComplex (.up ℤ)).obj K)) := rfl
    rw [hΦ]
    simp only [Category.assoc]
    -- left side
    have hD := congrArg ρU.mapDerivedCategory.map (mapDerivedCategorySquareIso_hom_app_Q c K)
    simp only [Functor.map_comp] at hD
    rw [reassoc_of% hD, mapDerivedCategoryFactors_hom_naturality]
    have nB := (mapDerivedCategorySquareIso b).hom.naturality
      (κV.mapDerivedCategoryFactors.hom.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at nB
    rw [← reassoc_of% nB, mapDerivedCategorySquareIso_hom_app_Q_assoc]
    have hA := congrArg πc.mapDerivedCategory.map (mapDerivedCategorySquareIso_hom_app_Q aV K)
    simp only [Functor.map_comp] at hA
    rw [reassoc_of% hA, mapDerivedCategoryFactors_hom_naturality_assoc]
    -- right side
    have nU := (mapDerivedCategorySquareIso aU).hom.naturality
      (pd.mapDerivedCategoryFactors.hom.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at nU
    rw [← reassoc_of% nU]
    rw [mapDerivedCategorySquareIso_hom_app_Q aU ((pd.mapHomologicalComplex (.up ℤ)).obj K)]
    have hI := congrArg δU.mapDerivedCategory.map (mapDerivedCategorySquareIso_inv_app_Q f K)
    simp only [Functor.map_comp] at hI
    rw [reassoc_of% hI, mapDerivedCategoryFactors_hom_naturality_assoc]
    have nP := (mapDerivedCategorySquareIso e).hom.naturality
      (rV.mapDerivedCategoryFactors.hom.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at nP
    rw [← reassoc_of% nP, mapDerivedCategorySquareIso_hom_app_Q_assoc]
    simp only [← DerivedCategory.Q.map_comp]
    congr 4
    ext i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, squareChainMap_f]
    exact h (K.X i)
  have hLR : (Functor.whiskerRight (mapDerivedCategorySquareIso aV).hom πc.mapDerivedCategory ≫
      Functor.whiskerLeft κV.mapDerivedCategory (mapDerivedCategorySquareIso b).hom ≫
      Functor.whiskerRight (mapDerivedCategorySquareIso c).hom ρU.mapDerivedCategory :
        (rV.mapDerivedCategory ⋙ δV.mapDerivedCategory) ⋙ πc.mapDerivedCategory ⟶
          (pd.mapDerivedCategory ⋙ κU.mapDerivedCategory) ⋙ ρU.mapDerivedCategory) =
      Functor.whiskerLeft rV.mapDerivedCategory (mapDerivedCategorySquareIso e).hom ≫
        Functor.whiskerRight (mapDerivedCategorySquareIso f).inv δU.mapDerivedCategory ≫
        Functor.whiskerLeft pd.mapDerivedCategory (mapDerivedCategorySquareIso aU).hom :=
    Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C₀ (.up ℤ))
      (fun K ↦ key K)
  exact congr_app hLR P

end Cube

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (u : U ⟶ V)

/-- `lambda` is the mate of the derived identity scalar/diagonal square: its counit form. -/
theorem lambda_counit (T : Scheme.{t}) (W : DerivedCategory (d.towers T)) :
    (diagonal (A := A) T).map ((lambda d T).hom.app W) ≫
        (diagonalAdjunction (A := A) T).counit.app ((exchangeTowerRes d T).obj W) =
      (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d T).symm).hom.app
          ((completedRlim T (d.completedRing T)).obj W) ≫
        (exchangeTowerRes d T).map ((d.constantRlimAdjunction T).counit.app W) := by
  rw [← lambda_mate]
  exact mateEquiv_counit _ _ _ W

/-- `exchangeResPush` is the mate of the derived restriction/pullback square: its counit form. -/
theorem exchangeResPush_counit (Z : DerivedCategory (d.towers U)) :
    (exchangeConstantPull (A := A) u).map ((exchangeResPush d u).hom.app Z) ≫
        (exchangeTowerAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso u A)).counit.app ((exchangeTowerRes d U).obj Z) =
      (Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d u).symm).hom.app
          ((d.towerPush u).obj Z) ≫
        (exchangeTowerRes d U).map ((d.towerAdjunction u).counit.app Z) := by
  have : (exchangeTowerModuleRes d U).PreservesKInjectiveComplexes :=
    exchangeTowerModuleRes_kinjective d U
  have h := exactDerivedMate_eq
    (G := exchangeTowerModuleRes d V) (H := exchangeTowerModuleRes d U)
    (d.towerModuleAdjunction u)
    (exchangeTowerModuleAdjunction u (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso u A))
    (exchangeModuleResPull d u).symm (exchangeModuleResPush d u)
    (exchangeModuleResPull_mate d u) (exchangeResPush d u)
    (exchangeResPush_existsUnique d u).choose_spec.1
  rw [h]
  unfold exactDerivedMate
  exact mateEquiv_counit _ _ _ Z

/-- `directImageRlimIso` is a conjugate: its counit form. -/
theorem directImageRlimIso_counit (Z : DerivedCategory (d.towers U)) :
    (d.towerPull u).map ((d.derivedConstantTower V).map ((d.directImageRlimIso u).hom.app Z)) ≫
        (d.towerPull u).map ((d.constantRlimAdjunction V).counit.app ((d.towerPush u).obj Z)) ≫
        (d.towerAdjunction u).counit.app Z =
      (d.derivedConstantPullbackIso u).hom.app
          ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z)) ≫
        (d.derivedConstantTower U).map
          ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
            (d.integralRingIso u)).counit.app ((completedRlim U (d.completedRing U)).obj Z)) ≫
        (d.constantRlimAdjunction U).counit.app Z := by
  have h := conjugateEquiv_counit
    ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
      (d.integralRingIso u)).comp (d.constantRlimAdjunction U))
    ((d.constantRlimAdjunction V).comp (d.towerAdjunction u))
    (d.derivedConstantPullbackIso u).hom Z
  simp only [Adjunction.comp_counit_app, Functor.comp_map] at h
  unfold AdicCoefficientDatum.directImageRlimIso
  exact h

/-- `directLimitIso` is a conjugate: its counit form. -/
theorem directLimitIso_counit (W : DerivedCategory (exchangeTowers U (exchangeConstantRing U A))) :
    (exchangeConstantPull (A := A) u).map ((diagonal (A := A) V).map
        ((directLimitIso (A := A) u).hom.app W)) ≫
        (exchangeConstantPull (A := A) u).map ((diagonalAdjunction (A := A) V).counit.app
          ((exchangeConstantPush (A := A) u).obj W)) ≫
        (exchangeTowerAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso u A)).counit.app W =
      (diagonalPullIso (A := A) u).hom.app
          ((push (A := A) u).obj ((rlim (A := A) U).obj W)) ≫
        (diagonal (A := A) U).map
          ((proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
            (exchangeConstantIso u A)).counit.app ((rlim (A := A) U).obj W)) ≫
        (diagonalAdjunction (A := A) U).counit.app W := by
  have h := conjugateEquiv_counit
    ((proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso u A)).comp (diagonalAdjunction (A := A) U))
    ((diagonalAdjunction (A := A) V).comp
      (exchangeTowerAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)))
    (diagonalPullIso (A := A) u).hom W
  simp only [Adjunction.comp_counit_app, Functor.comp_map] at h
  unfold directLimitIso
  exact h

/-- `chi` is the mate of the inverse of `alpha`: its counit form. -/
theorem chi_counit (X : d.derived U) :
    (pull (A := A) u).map ((chi d u).hom.app X) ≫
        (proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso u A)).counit.app ((res d U).obj X) =
      (alpha d u).inv.app ((d.push u).obj X) ≫
        (res d U).map ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
          (d.integralRingIso u)).counit.app X) := by
  have h := (proEtaleRingSheafChangeAdjunction u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)).2.2 ((d.push u).obj X) X
    ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
      (d.integralRingIso u)).counit.app X)
  rw [Adjunction.homEquiv_unit (proEtaleRingDerivedAdjunction u (d.completedRing V)
    (d.completedRing U) (d.integralRingIso u)), Adjunction.right_triangle_components,
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h2 := congrArg ((proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)).homEquiv _ _).symm h
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h2
  exact h2.symm

set_option quotPrecheck false
local notation "aD" => proEtaleRingDerivedAdjunction u (AdicCoefficientDatum.completedRing d V)
  (AdicCoefficientDatum.completedRing d U) (AdicCoefficientDatum.integralRingIso d u)
local notation "aC" => proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
  (exchangeConstantRing U A) (exchangeConstantIso u A)
local notation "tC" => exchangeTowerAdjunction u (exchangeConstantRing V A)
  (exchangeConstantRing U A) (exchangeConstantIso u A)
local notation "αV" => (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d V).symm).hom
local notation "αU" => (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d U).symm).hom
local notation "βR" => (Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d u).symm).hom

set_option linter.flexible false in
/-- The cube of exact-descent squares underlying `lambda_directImageRlimIso_aux`. -/
theorem restriction_cube (P : d.derived V) :
    (exchangeConstantPull (A := A) u).map ((αV).app P) ≫
        (βR).app ((d.derivedConstantTower V).obj P) ≫
        (exchangeTowerRes d U).map ((d.derivedConstantPullbackIso u).hom.app P) =
      (diagonalPullIso (A := A) u).hom.app ((res d V).obj P) ≫
        (diagonal (A := A) U).map ((alpha d u).inv.app P) ≫
        (αU).app ((d.pull u).obj P) := by
  refine Functor.mapDerivedCategory_cube (ordinaryScalarDiagonal d V).symm
    (exchangeModuleResPull d u).symm (d.constantPullbackIso u)
    (ordinaryDiagonalPullIso (A := A) u) (exchangeOrdinaryResPull d u)
    (ordinaryScalarDiagonal d U).symm (fun M ↦ ?_) P
  ext n
  simp [ordinaryScalarDiagonal, exchangeModuleResPull, AdicCoefficientDatum.constantPullbackIso,
    ordinaryDiagonalPullIso]
  erw [CategoryTheory.Functor.map_id]
  rfl

theorem lambda_directImageRlimIso_aux (Z : DerivedCategory (d.towers U)) :
    (res d V).map ((d.directImageRlimIso u).hom.app Z) ≫
        (lambda d V).hom.app ((d.towerPush u).obj Z) ≫
        (rlim (A := A) V).map ((exchangeResPush d u).hom.app Z) =
      (chi d u).hom.app ((completedRlim U (d.completedRing U)).obj Z) ≫
        (push (A := A) u).map ((lambda d U).hom.app Z) ≫
        (directLimitIso (A := A) u).hom.app ((exchangeTowerRes d U).obj Z) := by
  apply ((diagonalAdjunction (A := A) V).homEquiv _ _).symm.injective
  apply ((tC).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  -- the left side
  have e1 : (diagonal (A := A) V).map ((res d V).map ((d.directImageRlimIso u).hom.app Z) ≫
        (lambda d V).hom.app ((d.towerPush u).obj Z) ≫
        (rlim (A := A) V).map ((exchangeResPush d u).hom.app Z)) ≫
        (diagonalAdjunction (A := A) V).counit.app
          ((exchangeConstantPush (A := A) u).obj ((exchangeTowerRes d U).obj Z)) =
      (αV).app ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z)) ≫
        (exchangeTowerRes d V).map ((d.derivedConstantTower V).map
          ((d.directImageRlimIso u).hom.app Z) ≫
          (d.constantRlimAdjunction V).counit.app ((d.towerPush u).obj Z)) ≫
        (exchangeResPush d u).hom.app Z := by
    have n1 := (αV).naturality ((d.directImageRlimIso u).hom.app Z)
    simp only [Functor.comp_map] at n1
    simp only [Functor.map_comp, Category.assoc]
    erw [Adjunction.counit_naturality]
    rw [reassoc_of% (lambda_counit d V ((d.towerPush u).obj Z)), reassoc_of% n1]
  have e2 : (exchangeConstantPull (A := A) u).map
        ((diagonal (A := A) V).map ((res d V).map ((d.directImageRlimIso u).hom.app Z) ≫
          (lambda d V).hom.app ((d.towerPush u).obj Z) ≫
          (rlim (A := A) V).map ((exchangeResPush d u).hom.app Z)) ≫
        (diagonalAdjunction (A := A) V).counit.app
          ((exchangeConstantPush (A := A) u).obj ((exchangeTowerRes d U).obj Z))) ≫
        (tC).counit.app ((exchangeTowerRes d U).obj Z) =
      (exchangeConstantPull (A := A) u).map
          ((αV).app ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (βR).app ((d.derivedConstantTower V).obj
          ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (exchangeTowerRes d U).map ((d.derivedConstantPullbackIso u).hom.app
          ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z)) ≫
          (d.derivedConstantTower U).map ((aD).counit.app
            ((completedRlim U (d.completedRing U)).obj Z)) ≫
          (d.constantRlimAdjunction U).counit.app Z) := by
    rw [e1]
    have n2 := (βR).naturality ((d.derivedConstantTower V).map
          ((d.directImageRlimIso u).hom.app Z) ≫
          (d.constantRlimAdjunction V).counit.app ((d.towerPush u).obj Z))
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at n2
    simp only [Functor.map_comp, Category.assoc]
    rw [exchangeResPush_counit, reassoc_of% n2]
    have h3 := congrArg (exchangeTowerRes d U).map (directImageRlimIso_counit d u Z)
    simp only [Functor.map_comp] at h3
    rw [h3]
  -- the right side
  have e3 : (exchangeConstantPull (A := A) u).map
        ((diagonal (A := A) V).map
          ((chi d u).hom.app ((completedRlim U (d.completedRing U)).obj Z) ≫
          (push (A := A) u).map ((lambda d U).hom.app Z) ≫
          (directLimitIso (A := A) u).hom.app ((exchangeTowerRes d U).obj Z)) ≫
        (diagonalAdjunction (A := A) V).counit.app
          ((exchangeConstantPush (A := A) u).obj ((exchangeTowerRes d U).obj Z))) ≫
        (tC).counit.app ((exchangeTowerRes d U).obj Z) =
      (diagonalPullIso (A := A) u).hom.app
          ((res d V).obj ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (diagonal (A := A) U).map ((alpha d u).inv.app
          ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (αU).app ((d.pull u).obj ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (exchangeTowerRes d U).map ((d.derivedConstantTower U).map ((aD).counit.app
            ((completedRlim U (d.completedRing U)).obj Z)) ≫
          (d.constantRlimAdjunction U).counit.app Z) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [directLimitIso_counit]
    have n4 := (diagonalPullIso (A := A) u).hom.naturality
      ((chi d u).hom.app ((completedRlim U (d.completedRing U)).obj Z))
    have n5 := (diagonalPullIso (A := A) u).hom.naturality
      ((push (A := A) u).map ((lambda d U).hom.app Z))
    simp only [Functor.comp_map] at n4 n5
    rw [reassoc_of% n5, reassoc_of% n4]
    have n6 : (diagonal (A := A) U).map ((pull (A := A) u).map ((push (A := A) u).map
          ((lambda d U).hom.app Z))) ≫
        (diagonal (A := A) U).map ((aC).counit.app ((rlim (A := A) U).obj
          ((exchangeTowerRes d U).obj Z))) =
        (diagonal (A := A) U).map ((aC).counit.app
          ((res d U).obj ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (diagonal (A := A) U).map ((lambda d U).hom.app Z) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      erw [Adjunction.counit_naturality]
      rfl
    have n7 : (diagonal (A := A) U).map ((pull (A := A) u).map
          ((chi d u).hom.app ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (diagonal (A := A) U).map ((aC).counit.app
          ((res d U).obj ((completedRlim U (d.completedRing U)).obj Z))) =
        (diagonal (A := A) U).map ((alpha d u).inv.app
          ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z))) ≫
        (diagonal (A := A) U).map ((res d U).map
          ((aD).counit.app ((completedRlim U (d.completedRing U)).obj Z))) := by
      rw [← Functor.map_comp, ← Functor.map_comp, chi_counit]
    have n8 := lambda_counit d U Z
    have n9 := (αU).naturality ((aD).counit.app ((completedRlim U (d.completedRing U)).obj Z))
    simp only [Functor.comp_map] at n9
    rw [reassoc_of% n6, reassoc_of% n7, n8, reassoc_of% n9]
  refine Eq.trans e2 (Eq.trans ?_ e3.symm)
  simp only [Functor.map_comp]
  rw [reassoc_of% (restriction_cube d u
    ((d.push u).obj ((completedRlim U (d.completedRing U)).obj Z)))]


end AlgebraicGeometry.Scheme.OrderedExchange
