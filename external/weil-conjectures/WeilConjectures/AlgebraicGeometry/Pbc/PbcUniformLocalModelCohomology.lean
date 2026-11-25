/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionAlgEquiv
/-! # Common cohomological bounds from integral local models

The lower bound is reused from the
levelwise truncation theorem, applied at the common upper bound. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale
private theorem cover_of_sieve (X : Scheme.{u})
    (V : Sieve (⊤_ X.ProEt)) (hV : V ∈ ProEt.topology X (⊤_ X.ProEt)) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt) (f : ∀ i, U i ⟶ ⊤_ X.ProEt),
      Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        proetalePrecoverage X ∧ ∀ i, V (f i) := by
  let e : ProEt.mk (𝟙 X) ≅ ⊤_ X.ProEt :=
    (ProEt.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
  have h := (ProEt.topology X).pullback_stable e.hom hV
  obtain ⟨P, hP, hPV⟩ := ProEt.mem_topology_iff.mp h
  obtain ⟨I, U, f, rfl⟩ := P.exists_eq_ofArrows
  refine ⟨I, U, fun i ↦ f i ≫ e.hom, ?_, fun i ↦ hPV _ _ ⟨i⟩⟩
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
  change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
    proetalePrecoverage X at hP
  have hw (i : I) : (f i).left = (U i).hom := by
    have hw := MorphismProperty.Over.w (f i)
    change (f i).left ≫ 𝟙 X = (U i).hom at hw
    exact (Category.comp_id _).symm.trans hw
  simpa only [hw] using hP

private theorem pullback_homology_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (K : DerivedCategory (pbcModules Y R)) (q : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((adicTowerPullback g R).obj K))) :
    IsZero ((proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      ((SheafOfModules.toSheaf _).obj ((DerivedCategory.homologyFunctor _ q).obj K))) := by
  let R' := (adicTowerInverseImage g).obj R
  let F := proEtaleRingModulePullback g R R' (Iso.refl _)
  let adj := proEtaleRingModuleAdjunction g R R' (Iso.refl _)
  let H := (DerivedCategory.homologyFunctor _ q).obj K
  have hz : IsZero (F.obj H) :=
    h.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
  let a := ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).homEquiv
    ((SheafOfModules.toSheaf _).obj H)
    ((SheafOfModules.toSheaf _).obj (F.obj H))).symm
      ((SheafOfModules.toSheaf _).map (adj.unit.app H))
  have : IsIso a := ringUnitComparison g R R' (Iso.refl _) adj H
  exact ((SheafOfModules.toSheaf _).map_isZero hz).of_iso (asIso a)

private theorem uniform_upper (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (a b : ℤ) (_hab : a ≤ b)
    (S : Stratification T)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :
    ∀ n, (M.level n).IsLE b := by
  intro n
  apply (DerivedCategory.isLE_iff _ b).2
  intro q hq
  let H := (DerivedCategory.homologyFunctor _ q).obj (M.level n)
  have hz : IsZero ((SheafOfModules.toSheaf _).obj H) := by
    apply proEtale_isZero_of_stratum_cover T S V
    intro i j
    let g := (V i).f j ≫ S.immersion i
    let P := (L i j).complex
    have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
      (fun q hq ↦ (L i j).bounded q (Or.inr hq))
    have hb : (adicTowerLocalReduction d g P n).IsLE b := by
      exact (SheafOfModules.ringedTensorCohomologicalBounds
        ((adicTowerInverseImage g).map (pbcAdicProjection T d n)) b).1
          (DerivedCategory.Q.obj P) inferInstance
    apply pullback_homology_zero g _ (M.level n) q
    exact (DerivedCategory.isZero_of_isLE (adicTowerLocalReduction d g P n) b q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso ((L i j).identification n))
  apply (IsZero.iff_id_eq_zero H).2
  apply (SheafOfModules.toSheaf _).map_injective
  simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 H))
    ((SheafOfModules.toSheaf _).map (0 : H ⟶ H))

private theorem finite_lisse_descent {X : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (V : Cover.{u + 1} proetalePrecoverage X)
    (h : ∀ i, IsFiniteLocallyConstant A
      ((upperStar (ModuleCat.{u + 1} A) (V.f i)).obj F)) :
    IsFiniteLocallyConstant A F := by
  choose I W g hg he using h
  refine ⟨(Σ i, I i), (fun p ↦ W p.1 p.2),
    (fun p ↦ g p.1 p.2 ≫ V.f p.1),
    Precoverage.comp_mem_coverings V.f V.mem₀ g hg, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := he i j
  exact ⟨M, hM, ⟨(upperStarComp (ModuleCat.{u + 1} A) (g i j) (V.f i)).app F ≪≫ e⟩⟩

private theorem local_finite {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : adicLisseConstantRing Y A ⟶ R)
    (K : DerivedCategory (pbcModules Y R)) (q : ℤ)
    (h : IsRelativelyFiniteLisseModule g A
      ((pbcRestrict ((adicTowerInverseImage g).map c)).obj
        ((DerivedCategory.homologyFunctor _ q).obj ((adicTowerPullback g R).obj K)))) :
    IsFiniteLocallyConstant A
      ((upperStar (ModuleCat.{u + 1} A) g).obj
        ((CoefficientSerre.proEtaleModuleRestriction Y A).obj
          ((pbcRestrict c).obj ((DerivedCategory.homologyFunctor _ q).obj K)))) := by
  let C := adicLisseConstantRing Y A
  let R' := (adicTowerInverseImage g).obj R
  let C' := (adicTowerInverseImage g).obj C
  let FR := proEtaleRingModulePullback g R R' (Iso.refl _)
  let FC := proEtaleRingModulePullback g C C' (Iso.refl _)
  let H := (DerivedCategory.homologyFunctor _ q).obj K
  let U := pbcRestrict ((adicTowerInverseImage g).map c)
  let U₀ := pbcRestrict c
  let e₁ : U.obj ((DerivedCategory.homologyFunctor _ q).obj
      ((adicTowerPullback g R).obj K)) ≅ U.obj (FR.obj H) :=
    U.mapIso ((FR.mapDerivedCategoryHomologyFunctorIso q).app K).symm
  let e₂ : FC.obj (U₀.obj H) ≅ U.obj (FR.obj H) :=
    by
    let t := proEtaleRingRestrictionPullbackInv g C R C' R' c
      ((adicTowerInverseImage g).map c) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso g C R C' R' c
      ((adicTowerInverseImage g).map c) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    exact asIso (t.app H)
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl C')).choose
  let e₃ : FC.obj (U₀.obj H) ≅
      (proEtaleModuleInverseImage g C).obj (U₀.obj H) := by
    exact θ _
  have hf := (CoefficientSerre.relative_finite_iff g A _).mp h
  exact isFiniteLocallyConstant_of_iso
    ((CoefficientSerre.relativeRestriction g A).mapIso (e₁ ≪≫ e₂.symm ≪≫ e₃) ≪≫
      CoefficientSerre.relativePullbackComparison g A (U₀.obj H)) hf

private theorem restricted_transition_transport {T X : Scheme.{u}} (g : X ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M N : AdicTower T d) (e : ∀ n, M.level n ≅ N.level n)
    (he : ∀ b a hab,
      adicTowerSemilinearTransition T d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map (e a).hom =
        (e b).hom ≫ adicTowerSemilinearTransition T d N.level N.normalization b a hab)
    (b a : ℕ) (hab : a ≤ b) :
    (adicTowerPullback g ((pbcAdicRings T d).obj (op b))).map (e b).hom ≫
        adicTowerRestrictedTransition d g N b a hab =
      adicTowerRestrictedTransition d g M b a hab ≫
        (pbcDerivedRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient T d b a hab))).map
          ((adicTowerPullback g ((pbcAdicRings T d).obj (op a))).map (e a).hom) := by
  let F := adicTowerPullback g ((pbcAdicRings T d).obj (op b))
  let c := proEtaleRingRestrictionDerivedPullback g
    ((pbcAdicRings T d).obj (op b)) ((pbcAdicRings T d).obj (op a))
    ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op b)))
    ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op a)))
    (pbcAdicQuotient T d b a hab)
    ((adicTowerInverseImage g).map (pbcAdicQuotient T d b a hab))
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)
  change F.map (e b).hom ≫ F.map _ ≫ c.inv.app _ =
    (F.map _ ≫ c.inv.app _) ≫ _
  simp only [Category.assoc]
  rw [← Category.assoc, ← F.map_comp, ← he b a hab, F.map_comp, Category.assoc]
  exact congrArg (fun t ↦ F.map
    (adicTowerSemilinearTransition T d M.level M.normalization b a hab) ≫ t)
      (c.inv.naturality (e a).hom)

private theorem local_model_transport {T X : Scheme.{u}} (g : X ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M N : AdicTower T d) (e : ∀ n, M.level n ≅ N.level n)
    (he : ∀ b a hab,
      adicTowerSemilinearTransition T d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map (e a).hom =
        (e b).hom ≫ adicTowerSemilinearTransition T d N.level N.normalization b a hab)
    (a b : ℤ) (L : AdicTowerLocalModel d g M a b) :
    Nonempty (AdicTowerLocalModel d g N a b) := by
  let E (n : ℕ) :=
    (adicTowerPullback g ((pbcAdicRings T d).obj (op n))).mapIso (e n)
  refine ⟨{
    complex := L.complex
    bounded := L.bounded
    adicLisse := L.adicLisse
    finiteLisse := L.finiteLisse
    identification := fun n ↦ (E n).symm ≪≫ L.identification n
    compatible := ?_ }⟩
  intro j i hij
  apply (cancel_epi (E j).hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have ht := restricted_transition_transport g d M N e he j i hij
  change (E j).hom ≫ adicTowerRestrictedTransition d g N j i hij =
    adicTowerRestrictedTransition d g M j i hij ≫
      (pbcDerivedRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient T d j i hij))).map (E i).hom at ht
  rw [← Category.assoc (E j).hom, ht]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  let U := pbcDerivedRestrict ((adicTowerInverseImage g).map
    (pbcAdicQuotient T d j i hij))
  have hi := (U.mapIso (E i)).hom_inv_id_assoc (U.map (L.identification i).hom)
  change U.map (E i).hom ≫ U.map (E i).inv ≫ U.map (L.identification i).hom =
    U.map (L.identification i).hom at hi
  rw [hi]
  exact L.compatible j i hij

private theorem uniform_constructible (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (a b : ℤ)
    (S : Stratification T)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :
    ∀ n q, IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient d n)
      ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
        ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) := by
  intro n q
  let A' := PbcQuotient d n
  let H := (DerivedCategory.homologyFunctor _ q).obj (M.level n)
  let c := (pbcLevelConstantComparison T d n).hom
  let F := (CoefficientSerre.proEtaleModuleRestriction T A').obj ((pbcRestrict c).obj H)
  apply (CoefficientSerre.coefficient_constructible_iff T A' _).mpr
  refine ⟨S, fun i ↦ finite_lisse_descent A' _ (V i) (fun j ↦ ?_)⟩
  let g := (V i).f j ≫ S.immersion i
  have hlocal : IsFiniteLocallyConstant A'
      ((upperStar (ModuleCat.{u + 1} A') g).obj F) := by
    apply local_finite g A' _ c (M.level n) q
    apply (CoefficientSerre.relative_finite_iff g A' _).mpr
    let U := pbcRestrict ((adicTowerInverseImage g).map c)
    let e := U.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((L i j).identification n))
    exact isFiniteLocallyConstant_of_iso
      ((CoefficientSerre.relativeRestriction g A').mapIso e).symm
      ((CoefficientSerre.relative_finite_iff g A' _).mp ((L i j).finiteLisse n q))
  exact isFiniteLocallyConstant_of_iso
    ((upperStarComp (ModuleCat.{u + 1} A') ((V i).f j) (S.immersion i)).app F) hlocal

/-- Common local term windows give a uniform reduction profile, for any coefficient datum
whose ideal is generated by a nonzero element of a domain. -/
theorem pbcUniformLocalModelCohomology_of_principal
    {A : Type (u + 1)} [CommRing A] [IsDomain A] (d : AdicCoefficientDatum A)
    (π : A) (hI : d.ideal = Ideal.span {π}) (hπ : π ≠ 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (K : PbcCompletedDerived T d) :
    (PbcHasUniformConstructibleReductions T d K ∧
      PbcHasCompatibleEtaleOrigins T d K) →
      PbcUniformReductionProfile T d K := by
  rintro ⟨⟨M, e, ⟨a, b, hab, S, hS⟩, he⟩, _⟩
  choose W hW hL using hS
  have hcov := fun i ↦ cover_of_sieve (S.domain i) (W i) (hW i)
  choose I U f hU hf using hcov
  let V (i : Fin S.n) : Cover.{u + 1} proetalePrecoverage (S.domain i) :=
    { I₀ := I i, X := fun j ↦ (U i j).left, f := fun j ↦ (U i j).hom, mem₀ := hU i }
  have hmodels (i : Fin S.n) (j : (V i).I₀) :
      Nonempty (AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :=
    hL i (U i j) (f i j) (hf i j)
  let L (i : Fin S.n) (j : (V i).I₀) := Classical.choice (hmodels i j)
  have hb := uniform_upper T d M a b hab S V L
  let C := pbcReductionAdicTower T d K
  have he' : ∀ j i hij,
      adicTowerSemilinearTransition T d M.level M.normalization j i hij ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d j i hij)).map (e i).hom =
        (e j).hom ≫ adicTowerSemilinearTransition T d C.level C.normalization j i hij := by
    intro j i hij
    rw [he j i hij]
    congr 1
    dsimp only [C, pbcReductionAdicTower, adicTowerSemilinearTransition,
      pbcReductionNormalization, pbcReductionNormalizationHom]
    exact ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d j i hij)).homEquiv _ _
      |>.apply_symm_apply _).symm
  have hbC (n : ℕ) : (C.level n).IsLE b :=
    DerivedCategory.TStructure.t.isLE_of_iso (e n) b
  have hTor : PbcLevelwiseTorVanishing T d C b := by
    intro n q hq p hp
    have : (pbcDerivedRestrict
        (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).Additive :=
      inferInstanceAs ((pbcRestrict _).mapDerivedCategory.Additive)
    have : (pbcDerivedExtend
        (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).Additive :=
      (pbcDerivedScalarAdjunction _).left_adjoint_additive
    have hz := DerivedCategory.isZero_of_isLE (C.level (n + 1)) b q (by omega)
    exact (DerivedCategory.homologyFunctor _ (-(p : ℤ))).map_isZero
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).map_isZero
        ((DerivedCategory.singleFunctor _ 0).map_isZero hz))
  have hcanonical : a ≤ b ∧ ∃ S : Stratification T,
      ∀ i : Fin S.n, ∃ V : Sieve (⊤_ (S.domain i).ProEt),
        V ∈ ProEt.topology (S.domain i) (⊤_ (S.domain i).ProEt) ∧
        ∀ (U : (S.domain i).ProEt) (f : U ⟶ ⊤_ (S.domain i).ProEt),
          V f → Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion i) C a b) := by
    refine ⟨hab, S, fun i ↦ ⟨W i, hW i, fun U f hf ↦ ?_⟩⟩
    obtain ⟨L⟩ := hL i U f hf
    exact local_model_transport _ d M C e he' a b L
  obtain ⟨N, hN⟩ := pbc_adic_levelwise_truncations T d C b hTor
  have hzero := (pbc_levelwise_truncations_constructible_of_principal T d π hI hπ K b a b N hN hTor
    hcanonical).2.2.1
  have haC (n : ℕ) : (C.level n).IsGE (a - 1) := by
    apply (DerivedCategory.isGE_iff _ _).2
    intro q hq
    have hz := hzero n q (Or.inl hq)
    rw [N.lowerLevel n] at hz
    let t := (DerivedCategory.TStructure.t.truncLEι b).app (C.level n)
    have : IsIso ((DerivedCategory.homologyFunctor _ q).map t) :=
      DerivedCategory.isIso_homologyFunctor_map_truncLTι_app (C.level n) (b + 1) q
        (by omega)
    exact hz.of_iso (asIso ((DerivedCategory.homologyFunctor _ q).map t)).symm
  have hc := uniform_constructible T d M a b S V L
  refine ⟨a - 1, b, fun n ↦ ?_⟩
  let R := pbcRestrict (pbcLevelConstantComparison T d n).hom
  have eH (q : ℤ) := R.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso (e n)) ≪≫
    (R.mapDerivedCategoryHomologyFunctorIso q).app (C.level n)
  refine ⟨R.isGE_mapDerivedCategory_obj (C.level n) (a - 1),
    R.isLE_mapDerivedCategory_obj (C.level n) b, fun q ↦ ?_⟩
  apply (CoefficientSerre.coefficient_constructible_iff T (PbcQuotient d n) _).mpr
  exact isConstructible_of_iso
    ((CoefficientSerre.proEtaleModuleRestriction T (PbcQuotient d n)).mapIso (eH q))
    ((CoefficientSerre.coefficient_constructible_iff T (PbcQuotient d n) _).mp (hc n q))

/-- The local-model and origin hypotheses imply a common intrinsic cohomological
interval for all reductions. This is the forward half of the uniform criterion. -/
theorem pbcUniformLocalModelCohomology (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (PbcHasUniformConstructibleReductions T (pbcIntegralDatum l E) K ∧
      PbcHasCompatibleEtaleOrigins T (pbcIntegralDatum l E) K) →
      PbcUniformReductionProfile T (pbcIntegralDatum l E) K := by
  let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  let : IsDomain (PbcIntegralRing l E) := e.toMulEquiv.isDomain _
  have hπ : pbcUniformizer l E ≠ 0 := by
    intro h
    exact Padic.coefficientExtensionUniformizer_ne_zero l E (congrArg ULift.down h)
  exact pbcUniformLocalModelCohomology_of_principal (pbcIntegralDatum l E)
    (pbcUniformizer l E) rfl hπ T K
end AlgebraicGeometry.Scheme
