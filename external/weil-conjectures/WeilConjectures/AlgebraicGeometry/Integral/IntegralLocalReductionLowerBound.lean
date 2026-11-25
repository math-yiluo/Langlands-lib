/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionCohomologySequence
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
import all WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleClosedProjection.ProEtaleClosedUnderivedProjection
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalRestriction.ProEtaleLocalDerivedRestrictionComparisonsSupplement

/-! # Lower cohomological bound for a restricted completed DVR quotient

The coefficient ring is the actual inverse image of the completed ring.

## References

* Stacks Project, Tag 093M
* Tag 06YU
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem completed_principal_resolution
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsDomain A]
    (d : AdicCoefficientDatum A) (π : A) (hI : d.ideal = Ideal.span {π})
    (hπ : π ≠ 0) (n : ℕ) :
    let c := CompletedConstantReduction.base T d.ideal ≫
      CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
    let F := adicLisseConstantModules T A ⋙
      completedAdicChange T c
    let e := CompletedConstantReduction.constantChange_unit T c
    let f := e.inv ≫ F.map (ModuleCat.ofHom
      (LinearMap.mulLeft A (π ^ (n + 1)))) ≫ e.hom
    ∃ p : SheafOfModules.unit ((adicLisseForget T).obj (pbcAdicCompletion T d)) ⟶
        (pbcRestrict (pbcAdicProjection T d n)).obj
          (SheafOfModules.unit ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))),
      ∃ h : f ≫ p = 0, (ShortComplex.mk f p h).ShortExact ∧
        ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : (pbcAdicCompletion T d).obj.obj U) =
          (1 : ((pbcAdicRings T d).obj (op n)).obj.obj U) := by
  let c := CompletedConstantReduction.base T d.ideal ≫
      CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  let F := adicLisseConstantModules T A ⋙ completedAdicChange T c
  let e := CompletedConstantReduction.constantChange_unit T c
  let : IsNoetherianRing A := d.noetherian
  have hfin := CompletedConstantReduction.finite_coefficient_identification
    T d.ideal d.quotientFinite
  have hc : IsIso (CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite) :=
    hfin.2.1
  have hh := completed_constant_algebra_flat_quotients T d.ideal _
    (asIso (CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite)) c
    (fun n ↦ by
      dsimp only [c]
      simp only [asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
      exact (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 n)
  let := (exactFunctor_iff (completedAdicChange T c)).1 hh.2.1 |>.1
  let := (exactFunctor_iff (completedAdicChange T c)).1 hh.2.1 |>.2
  let := (CompletedConstantReduction.constant_exact T A).1
  let := (CompletedConstantReduction.constant_exact T A).2
  let := CompletedConstantReduction.constant_additive T A
  let a := π ^ (n + 1)
  have hspan : Ideal.span {a} = d.ideal ^ (n + 1) := by
    rw [hI]
    exact (Ideal.span_singleton_pow _ _).symm
  let μ := ModuleCat.ofHom (LinearMap.mulLeft A a)
  let p₀ := ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (d.ideal ^ (n + 1))).toLinearMap)
  obtain ⟨hw, hs⟩ : ∃ h : μ ≫ p₀ = 0, (ShortComplex.mk μ p₀ h).ShortExact := by
    dsimp only [μ, p₀]
    rw [← hspan]
    exact principal_scalar_sequence a (pow_ne_zero _ hπ)
  let r := CompletedConstantReduction.finiteReduction T d.ideal d.quotientFinite n
  have hr : IsIso r := hfin.2.2.1 n
  let eR := asIso r
  let p := e.inv ≫ F.map p₀ ≫ eR.hom
  have hp : (e.inv ≫ F.map μ ≫ e.hom) ≫ p = 0 := by
    simp only [p, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, hw,
      Functor.map_zero, zero_comp, comp_zero]
  refine ⟨p, hp, ?_, ?_⟩
  · let i : ((ShortComplex.mk μ p₀ hw).map F) ≅
        ShortComplex.mk (e.inv ≫ F.map μ ≫ e.hom) p hp :=
      ShortComplex.isoMk e e eR (by simp) (by simp [p])
    exact ShortComplex.shortExact_of_iso i (hs.map_of_exact F)
  · intro U
    change r.val.app U
      (((completedAdicChange T c).map ((adicLisseConstantModules T A).map p₀)).val.app U
        ((CompletedConstantReduction.constantChange_unit T c).inv.val.app U
          (1 : (pbcAdicCompletion T d).obj.obj U))) =
        (1 : ((pbcAdicRings T d).obj (op n)).obj.obj U)
    rw [constant_unit_inv_one, completed_map_tensor_one, constantGenerator_naturality]
    change r.val.app U (completedAdicChangeTensor T c _ U 1
      (constantGenerator T (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) U 1)) =
        (1 : ((pbcAdicRings T d).obj (op n)).obj.obj U)
    have hraw : constantGenerator T (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) U 1 =
        (toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))))).app U
              (1 : A ⧸ d.ideal ^ (n + 1)) := rfl
    rw [hraw]
    exact ((CompletedConstantReduction.finiteReduction_exists T d.ideal
      d.quotientFinite n).choose_spec.1 U 1 1).trans (by
        simp only [id_eq, map_one, one_mul])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def coefficientUnitMap
    (X : Scheme.{u}) {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) :
    SheafOfModules.unit ((adicLisseForget X).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget X).obj S)) where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map
      ((forget₂ CommRingCat RingCat).map (φ.hom.app U))) (fun r ↦ by
      ext m
      exact ((φ.hom.app U).hom.map_mul r m).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_pullback_sequence
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (f : SheafOfModules.unit ((adicLisseForget X).obj R) ⟶
      SheafOfModules.unit ((adicLisseForget X).obj R))
    (p : SheafOfModules.unit ((adicLisseForget X).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget X).obj S)))
    (hp : ∀ V : X.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (hz : f ≫ p = 0) (hs : (ShortComplex.mk f p hz).ShortExact) :
    ∃ f' : SheafOfModules.unit
        ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj R)) ⟶
      SheafOfModules.unit ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj R)),
      ∃ hz' : f' ≫ coefficientUnitMap Y ((adicTowerInverseImage g).map φ) = 0,
        (ShortComplex.mk f' (coefficientUnitMap Y ((adicTowerInverseImage g).map φ))
          hz').ShortExact := by
  let G := proEtaleModuleInverseImage g R
  let eR := ProEtaleClosedProjection.regularInverseIso g R
  let eS := ProEtaleClosedProjection.coefficientInverseIso g φ
  let q := coefficientUnitMap Y ((adicTowerInverseImage g).map φ)
  have hpall (V : X.ProEtᵒᵖ) (r : R.obj.obj V) :
      p.val.app V r = φ.hom.app V r := by
    have h := (p.val.app V).hom.map_smul r (1 : R.obj.obj V)
    change (p.val.app V (r * (1 : R.obj.obj V)) : S.obj.obj V) =
      φ.hom.app V r * (@id (S.obj.obj V) (p.val.app V (1 : R.obj.obj V))) at h
    simpa only [mul_one, hp V, id_eq] using h
  have hcomm : G.map p ≫ eS.hom = eR.hom ≫ q := by
    apply ProEtaleTensorComparison.inverseModule_hom_ext g
    intro V r
    change eS.hom.val.app _ ((G.map p).val.app _
      (ProEtaleTensorComparison.inverseSection g _ V r)) =
        q.val.app _ (eR.hom.val.app _
          (ProEtaleTensorComparison.inverseSection g _ V r))
    rw [ProEtaleTensorComparison.inverseSection_map,
      ProEtaleClosedProjection.coefficientInverseIso_sections,
      ProEtaleClosedProjection.regularInverseIso_sections, hpall]
    have h := congrArg
      (fun k ↦ k.hom.app (op V) (show R.obj.obj (op V) from r))
      ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality φ)
    exact h
  let f' := eR.inv ≫ G.map f ≫ eR.hom
  have hq : q = eR.inv ≫ G.map p ≫ eS.hom := by
    rw [hcomm]
    simp
  have hz' : f' ≫ q = 0 := by
    rw [hq]
    simp only [f', Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp_assoc, hz, Functor.map_zero, zero_comp, comp_zero]
  refine ⟨f', hz', ?_⟩
  let e : (ShortComplex.mk f p hz).map G ≅ ShortComplex.mk f' q hz' :=
    ShortComplex.isoMk eR eR eS (by simp [f']) hcomm.symm
  exact ShortComplex.shortExact_of_iso e (hs.map_of_exact G)

set_option backward.isDefEq.respectTransparency false in
private theorem lower_bound_of_coefficient_sequence
    (Y : Scheme.{u}) {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S)
    (f : SheafOfModules.unit ((adicLisseForget Y).obj R) ⟶
      SheafOfModules.unit ((adicLisseForget Y).obj R))
    (p : SheafOfModules.unit ((adicLisseForget Y).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget Y).obj S)))
    (hp : ∀ V : Y.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (hz : f ≫ p = 0) (hs : (ShortComplex.mk f p hz).ShortExact)
    (K : DerivedCategory (pbcModules Y R)) (a : ℤ) [K.IsGE a] :
    ((pbcDerivedExtend φ).obj K).IsGE (a - 1) := by
  obtain ⟨v, w, ht, _⟩ := pbc_adic_reduction_triangle Y φ f p hp hz hs K
  rw [DerivedCategory.isGE_iff]
  intro q hq
  have hzero := (DerivedCategory.HomologySequence.exact₃
    (Pretriangulated.Triangle.mk v ((pbcDerivedScalarAdjunction φ).unit.app K) w)
    ht q (q + 1) rfl).isZero_of_both_isZero
      (DerivedCategory.isZero_of_isGE K a q (by omega))
      (DerivedCategory.isZero_of_isGE K a (q + 1) (by omega))
  let H := (DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj K)
  have hU : IsZero ((pbcRestrict φ).obj H) :=
    hzero.of_iso (((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).app
      ((pbcDerivedExtend φ).obj K))
  have hH : IsZero ((SheafOfModules.toSheaf _).obj H) :=
    (SheafOfModules.toSheaf ((adicLisseForget Y).obj R)).map_isZero hU
  apply (IsZero.iff_id_eq_zero H).2
  apply (SheafOfModules.toSheaf _).map_injective
  simpa using hH.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 H))
    ((SheafOfModules.toSheaf _).map (0 : H ⟶ H))

/-- Reducing a lower-bounded complex by a completed quotient for a principal ideal generated
by a nonzero element of a domain loses at most one degree. -/
theorem integralLocalReduction_isGE_of_principal
    {A : Type (u + 1)} [CommRing A] [IsDomain A] (d : AdicCoefficientDatum A)
    (π : A) (hI : d.ideal = Ideal.span {π}) (hπ : π ≠ 0)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] (n : ℕ) :
    (adicTowerLocalReduction d g L n).IsGE (a - 1) := by
  obtain ⟨p, hz, hs, hp⟩ := completed_principal_resolution X d π hI hπ n
  obtain ⟨f', hz', hs'⟩ := normalized_pullback_sequence g
    (pbcAdicProjection X d n) _ p hp hz hs
  exact lower_bound_of_coefficient_sequence Y _ f' _
    (fun V ↦ by
      change (((adicTowerInverseImage g).map
        (pbcAdicProjection X d n)).hom.app V)
          (1 : ((adicTowerInverseImage g).obj
            (pbcAdicCompletion X d)).obj.obj V) = 1
      exact map_one _) hz' hs' (DerivedCategory.Q.obj L) a

/-- Reducing a lower-bounded complex by a completed DVR quotient loses at most one degree. -/
theorem integralLocalReduction_isGE
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X (pbcIntegralDatum l E)))) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] (n : ℕ) :
    (adicTowerLocalReduction (pbcIntegralDatum l E) g L n).IsGE (a - 1) := by
  let A := PbcIntegralRing l E
  let e : A ≃+* Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  let : IsDomain A := e.toMulEquiv.isDomain _
  have hπ : pbcUniformizer l E ≠ 0 := by
    intro h
    exact AlgebraicGeometry.uniformizer_ne_zero l E (congrArg ULift.down h)
  obtain ⟨p, hz, hs, hp⟩ := completed_principal_resolution X
    (pbcIntegralDatum l E) (pbcUniformizer l E) rfl hπ n
  obtain ⟨f', hz', hs'⟩ := normalized_pullback_sequence g
    (pbcAdicProjection X (pbcIntegralDatum l E) n) _ p hp hz hs
  exact lower_bound_of_coefficient_sequence Y _ f' _
    (fun V ↦ by
      change (((adicTowerInverseImage g).map
        (pbcAdicProjection X (pbcIntegralDatum l E) n)).hom.app V)
          (1 : ((adicTowerInverseImage g).obj
            (pbcAdicCompletion X (pbcIntegralDatum l E))).obj.obj V) = 1
      exact map_one _) hz' hs' (DerivedCategory.Q.obj L) a

end AlgebraicGeometry.Scheme
