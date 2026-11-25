/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerScalarConeComparison
import WeilConjectures.CategoryTheory.Normalized.NormalizedStrictLimitBase
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarConeExactProducts
import WeilConjectures.CategoryTheory.RegularScalarQuotient.RegularScalarQuotientTower

/-! # Scalar cones of strict ordinary quotient limits

Source: Stacks 099M and 0941; diagonal tower limit proof paragraph (3).
(blueprint: lem-sfb-diagonal-tower-scalar-cone-is-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale

private theorem rlimCone
    {A : Type*} [Category A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasCountableProducts (DerivedCategory A)]
    (L : DiagonalRlim A) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ p : (Functor.const ℕᵒᵖ).obj (L.R.obj (DerivedCategory.Q.obj X)) ⟶
        X.asFunctor ⋙ DerivedCategory.Q,
      CategoryTheory.Pretriangulated.IsHomotopyLimit (Cone.mk _ p) ∧
      ∀ n : ℕ, p.app (op n) =
        (L.projection n).app (DerivedCategory.Q.obj X) ≫
          ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X := by
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck A
  let I := (CochainComplex.kInjectiveResolutionFunctor (ℕᵒᵖ ⥤ A)).obj X
  let j : X ⟶ I := (CochainComplex.toKInjectiveResolution (ℕᵒᵖ ⥤ A)).app X
  have : QuasiIso j := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app (ℕᵒᵖ ⥤ A) X).2
  have : IsIso (L.η.app I) := L.computation I inferInstance
  let t := Functor.whiskerRight
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j) DerivedCategory.Q
  have : ∀ n, IsIso (t.app n) := by
    intro n
    change IsIso (DerivedCategory.Q.map
      ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map j))
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app _
  let e := asIso t
  let d := asIso (L.R.map (DerivedCategory.Q.map j))
  obtain ⟨q, hq, hη⟩ := normalizedStrictLimitBase L.R L.η L.universal I
  have hleg (n : ℕ) : q.app (op n) =
      (L.projection n).app (DerivedCategory.Q.obj I) ≫
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I := by
    apply (cancel_epi (L.η.app I)).1
    rw [hη]
    exact (L.normalization I n).symm
  let c := ((Cone.postcompose e.inv).obj (Cone.mk _ q)).extend d.hom
  have hc : CategoryTheory.Pretriangulated.IsHomotopyLimit c :=
    hq.of_iso e.symm c d.symm (by intro n; simp [c])
  refine ⟨c.π, hc, ?_⟩
  intro n
  change L.R.map (DerivedCategory.Q.map j) ≫
    (q.app (op n) ≫ e.inv.app (op n)) = _
  rw [hleg]
  simp only [← Category.assoc]
  rw [(L.projection n).naturality]
  simp only [Category.assoc]
  have hn := ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.naturality j
  change ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map
      (DerivedCategory.Q.map j) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I =
    ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X ≫ t.app (op n) at hn
  rw [← Category.assoc _ _ (e.inv.app _), hn]
  have ht : t = e.hom := rfl
  rw [ht]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact congrArg ((L.projection n).app (DerivedCategory.Q.obj X) ≫ ·)
    (Category.comp_id
      (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X))

private theorem scalarConeAugmentation_isIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [HasCountableProducts (DerivedCategory A)]
    (s : ℤ) (U : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hU : CochainComplex.IsNormalizedAdicTower s U) (k : ℕ)
    (c : Cone ((addOpFunctor k ⋙ U) ⋙ DerivedCategory.Q))
    (hc : IsHomotopyLimit c) :
    IsIso ((CochainComplex.LinearScalarCone.derived (s ^ k)).map (c.π.app (op 0)) ≫
      (CochainComplex.LinearScalarCone.comparison (s ^ k)).hom.app
        (U.obj ((addOpFunctor k).obj (op 0))) ≫
      DerivedCategory.Q.map (CochainComplex.LinearScalarCone.augmentation hU k (op 0))) := by
  let F := CochainComplex.LinearScalarCone.derived (A := A) (s ^ k)
  obtain ⟨hshift, htri, hprod⟩ := CochainComplex.LinearScalarCone.exact_products (A := A) (s ^ k)
  let := hshift
  let := htri
  let := hprod
  let e : ((addOpFunctor k ⋙ U) ⋙ DerivedCategory.Q) ⋙ F ≅
      CochainComplex.IsNormalizedAdicTower.arrowTower (ϖ := s) (T := U) k ⋙
        CochainComplex.ConeCoimage.cone ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (addOpFunctor k ⋙ U)
        (CochainComplex.LinearScalarCone.comparison (s ^ k)) ≪≫
      (Functor.associator _ _ _).symm
  let d := (Cone.postcompose e.hom).obj (F.mapCone c)
  have hd : IsHomotopyLimit d := (hc.map F).of_iso e d (Iso.refl _) (by
    intro n
    simp [d])
  simpa only [d, e, F, Iso.trans_hom, Iso.symm_hom,
    Cone.postcompose_obj_π, Cone.postcompose_obj_pt, Functor.mapCone_pt,
    Functor.const_obj_obj, Functor.comp_obj, Functor.mapCone_π_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, CochainComplex.LinearScalarCone.augmentation,
    Nat.zero_add, Category.assoc] using hU.isIso_π_comp k hd

private theorem zeroSandwich
    {A : Type*} [Category A] [HasZeroMorphisms A] {P K I Z W : A}
    (a : P ⟶ K) (b : K ⟶ I) (c : I ⟶ Z) (d : Z ⟶ W) (h : b ≫ c = 0) :
    a ≫ b ≫ c ≫ d = 0 := by
  rw [← Category.assoc b c d, h, zero_comp, comp_zero]

private theorem coneCokernelDesc
    {A : Type*} [Category A] [Abelian A]
    (a : Arrow (CochainComplex A ℤ)) {Z : CochainComplex A ℤ}
    (f : a.right ⟶ Z) (hf : a.hom ≫ f = 0)
    (g : CochainComplex.ConeCoimage.coker.obj a ⟶ Z)
    (hg : cokernel.π a.hom ≫ g = f) :
    CochainComplex.ConeCoimage.ρ.app a ≫ CochainComplex.ConeCoimage.desc.app a ≫ g =
      CochainComplex.mappingCone.descShortComplex (ShortComplex.mk a.hom f hf) := by
  change CochainComplex.ConeCoimage.ρ.app a ≫ CochainComplex.ConeCoimage.desc.app a ≫ g =
    CochainComplex.mappingCone.desc a.hom 0 f (by simp [hf])
  apply HomologicalComplex.hom_ext
  intro q
  apply CochainComplex.mappingCone.ext_from _ (q + 1) q rfl
  · simp only [HomologicalComplex.comp_f, ← Category.assoc]
    rw [CochainComplex.ConeCoimage.inl_v_ρ_app_f]
    simp only [Category.assoc, CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.zero_v]
    change (Abelian.coimage.π a.hom).f (q + 1) ≫
      (CochainComplex.mappingCone.inl (CochainComplex.ConeCoimage.cokerSequence a).f).v
        (q + 1) q (by omega) ≫
      (CochainComplex.mappingCone.descShortComplex
        (CochainComplex.ConeCoimage.cokerSequence a)).f q ≫ g.f q = 0
    exact zeroSandwich _ _ _ _
      (CochainComplex.mappingCone.inl_v_descShortComplex_f
        (CochainComplex.ConeCoimage.cokerSequence a) (q + 1) q (by omega))
  · have h := congrArg (· ≫ g) (CochainComplex.ConeCoimage.inr_ρ_desc a)
    simpa only [HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f] using
      congrArg (fun z ↦ z.f q) (h.trans hg)

private theorem scalarConeAugmentation_at_zero_isIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [HasCountableProducts (DerivedCategory A)]
    (s : ℤ) (U : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hU : CochainComplex.IsNormalizedAdicTower s U) (k : ℕ)
    (t : ℤ) (ht : t = s ^ k)
    (c : Cone (U ⋙ DerivedCategory.Q)) (hc : IsHomotopyLimit c) :
    IsIso ((CochainComplex.LinearScalarCone.derived (t)).map (c.π.app (op k)) ≫
      (CochainComplex.LinearScalarCone.comparison (t)).hom.app (U.obj (op k)) ≫
      DerivedCategory.Q.map
        (CochainComplex.ConeCoimage.ρ.app (Arrow.mk (t • 𝟙 (U.obj (op k)))) ≫
          CochainComplex.ConeCoimage.desc.app (Arrow.mk (t • 𝟙 (U.obj (op k)))) ≫
          cokernel.desc (t • 𝟙 (U.obj (op k))) (𝟙 _) (by
            rw [Category.comp_id, ht, hU.smul_eq_zero]))) := by
  subst t
  have h := scalarConeAugmentation_isIso s U hU k
    (c.whisker (addOpFunctor k)) (hc.whiskerAdd k)
  dsimp only [CochainComplex.LinearScalarCone.augmentation,
    CochainComplex.IsNormalizedAdicTower.cokerDesc,
    CochainComplex.IsNormalizedAdicTower.red,
    CochainComplex.IsNormalizedAdicTower.arrowTower,
    CochainComplex.smulArrow_obj, Arrow.mk_hom,
    Cone.whisker_π, Functor.whiskerLeft_app, addOpFunctor_obj,
    Functor.comp_obj] at h
  dsimp only [Cone.whisker_pt, Functor.const_obj_obj] at h ⊢
  have transport (j : ℕ) (hj : j = k) (f : op j ⟶ op k)
      (hz : (s ^ k • 𝟙 (U.obj (op j))) ≫ U.map f = 0)
      (hi : IsIso
        ((CochainComplex.LinearScalarCone.derived (s ^ k)).map (c.π.app (op j)) ≫
          (CochainComplex.LinearScalarCone.comparison (s ^ k)).hom.app (U.obj (op j)) ≫
          DerivedCategory.Q.map
            (CochainComplex.ConeCoimage.ρ.app (Arrow.mk (s ^ k • 𝟙 (U.obj (op j)))) ≫
              CochainComplex.ConeCoimage.desc.app
                (Arrow.mk (s ^ k • 𝟙 (U.obj (op j)))) ≫
              cokernel.desc (s ^ k • 𝟙 (U.obj (op j))) (U.map f) hz))) :
      IsIso ((CochainComplex.LinearScalarCone.derived (s ^ k)).map (c.π.app (op k)) ≫
        (CochainComplex.LinearScalarCone.comparison (s ^ k)).hom.app (U.obj (op k)) ≫
        DerivedCategory.Q.map
          (CochainComplex.ConeCoimage.ρ.app (Arrow.mk (s ^ k • 𝟙 (U.obj (op k)))) ≫
            CochainComplex.ConeCoimage.desc.app (Arrow.mk (s ^ k • 𝟙 (U.obj (op k)))) ≫
            cokernel.desc (s ^ k • 𝟙 (U.obj (op k))) (𝟙 _) (by
              rw [Category.comp_id, hU.smul_eq_zero]))) := by
    subst j
    have hf : f = 𝟙 (op k) := Subsingleton.elim _ _
    subst f
    have hd : cokernel.desc (s ^ k • 𝟙 (U.obj (op k))) (U.map (𝟙 (op k))) hz =
        cokernel.desc (s ^ k • 𝟙 (U.obj (op k))) (𝟙 _) (by
          rw [Category.comp_id, hU.smul_eq_zero]) := by
      apply coequalizer.hom_ext
      rw [cokernel.π_desc, cokernel.π_desc, U.map_id]
    rw [hd] at hi
    exact hi
  exact transport (0 + k) (Nat.zero_add k)
    (homOfLE (Nat.le_add_left k 0)).op _ h

/-- The explicit scalar-cone comparison for a regular strict quotient tower is invertible.

Source: Stacks 099M, the proof of naive completion; Stacks 0941; blueprint
`sk-prop-diagonal-tower-limit.proof.md`, paragraph (3).
(blueprint: lem-sfb-diagonal-tower-scalar-cone-is-iso).

Proof: exact scalar extension preserves all the monic scalar maps on P. Identify
its ordinary quotients with the scalar cokernels by the given colimit property,
compatibly with transitions by cancellation of the quotient epimorphisms. Adjoin
the zero quotient at exponent zero. The resulting tower T is normalized: the
scalar annihilation follows by cancelling the quotient projection; the quotient
of P/ell^m by ell^k is P/ell^k for k <= m; regularity identifies the kernel of
ell^b on P/ell^(a+b) with the image of ell^a. These are degreewise statements and
therefore give the three fields of IsNormalizedAdicTower for the complex tower.
Apply the normalized strict-limit theorem to a K-injective replacement I of the
strict tower complex. At I, L.eta is invertible, so cancel it in the two
normalization formulas to identify the cone legs with L.projection followed by
the exact evaluation comparison. Evaluation of the replacement is a levelwise
quasi-isomorphism. Transport this cone back along those isomorphisms and
L.R applied to the replacement, using naturality of L.projection. This gives
the required homotopy-limit cone at the original tower. Deleting
the initial zero term and restricting to any finite tail preserves this property.
Apply the existing integer-linear scalar cone, which is triangulated and preserves
countable products, to the tail starting at n+1. Its representative comparison
identifies the resulting cone with a homotopy limit of the strict multiplication
cones for ell^(n+1). The theorem IsNormalizedAdicTower.isIso_π_comp says its
augmented zeroth projection is invertible. At that zeroth level the reduction is
the identity. Its cone augmentation agrees with the projection used in
our defined map: their degree-zero inclusion composites are the identity and their
shifted inclusion components are zero. Naturality of the representative comparison
therefore identifies this invertible augmented projection with the explicitly
defined map, up to invertible evaluation factors. This proves its invertibility.
The same argument includes n=0, a zero complex and the empty scheme. -/
theorem diagonal_tower_scalar_cone_isIso (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (O : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ W))
    (L : DiagonalRlim (DiagonalMod ℓ W)) (n : ℕ)
    (P : CochainComplex (DiagonalAb W) ℤ)
    (hP : ∀ (m : ℕ) (i : ℤ), Mono (ℓ ^ (m + 1) • 𝟙 (P.X i))) :
    IsIso ((diagonalTowerScalarConeComparison O L n).app P) := by
  let S := diagonalScalarExtension ℓ W
  have : PreservesFiniteLimits S := scalarExtension_exact ℓ W
  have : S.Additive := scalarExtension_additive ℓ W
  let V := (S.mapHomologicalComplex (.up ℤ)).obj P
  let X := (O.E.mapHomologicalComplex (.up ℤ)).obj P
  have hmono (m : ℕ) (i : ℤ) : Mono (ℓ ^ (m + 1) • 𝟙 (S.obj (P.X i))) := by
    have : Mono (ℓ ^ (m + 1) • 𝟙 (P.X i)) := hP m i
    have hm : Mono (S.map (ℓ ^ (m + 1) • 𝟙 (P.X i))) := inferInstance
    simp only [Functor.map_nsmul] at hm
    rw [S.map_id] at hm
    exact hm
  have hV (m : ℕ) : Mono ((ℓ : ℤ) ^ m • 𝟙 V) := by
    cases m with
    | zero => simp only [pow_zero, one_smul]; infer_instance
    | succ m =>
      have hm : Mono (ℓ ^ (m + 1) • 𝟙 V) :=
        HomologicalComplex.mono_of_mono_f _ (hmono m)
      simpa only [← Nat.cast_pow, natCast_zsmul] using hm
  let U := CategoryTheory.RegularScalarQuotient.tower (ℓ : ℤ) V
  have hU : CochainComplex.IsNormalizedAdicTower (ℓ : ℤ) U :=
    CategoryTheory.RegularScalarQuotient.normalized (ℓ : ℤ) V hV
  let π : (Functor.const ℕᵒᵖ).obj V ⟶ X.asFunctor :=
    NatTrans.ofOpSequence
      (fun m ↦ (NatTrans.mapHomologicalComplex (O.π m) (.up ℤ)).app P)
      (by
        intro m
        apply HomologicalComplex.hom_ext
        intro i
        change (𝟙 _) ≫ (O.π m).app (P.X i) =
          (O.π (m + 1)).app (P.X i) ≫
            (O.E.obj (P.X i)).map (homOfLE m.le_succ).op
        rw [Category.id_comp]
        exact (O.transition m (P.X i)).symm)
  have hzero (m : ℕ) : ((ℓ : ℤ) ^ (m + 1) • 𝟙 V) ≫ π.app (op m) = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    change ((ℓ : ℤ) ^ (m + 1) • 𝟙 (S.obj (P.X i))) ≫ (O.π m).app (P.X i) = 0
    simpa only [← Nat.cast_pow, natCast_zsmul] using O.zero m (P.X i)
  let hcol (m : ℕ) : IsColimit (CokernelCofork.ofπ (π.app (op m)) (hzero m)) := by
    have hs := reductionComplexSequence_shortExact ℓ S O m P (hmono m)
    have := hs.epi_g
    have hf : ((ℓ : ℤ) ^ (m + 1) • 𝟙 V) = ℓ ^ (m + 1) • 𝟙 V := by
      rw [← Nat.cast_pow, natCast_zsmul]
    exact CokernelCofork.isColimitOfIsColimitOfIff' hs.exact.gIsCokernel
      ((ℓ : ℤ) ^ (m + 1) • 𝟙 V) (by
        intro Z f
        change (ℓ ^ (m + 1) • 𝟙 V) ≫ f = 0 ↔
          ((ℓ : ℤ) ^ (m + 1) • 𝟙 V) ≫ f = 0
        rw [hf])
  let e (m : ℕ) : U.obj (op (m + 1)) ≅ X.asFunctor.obj (op m) :=
    (cokernelIsCokernel ((ℓ : ℤ) ^ (m + 1) • 𝟙 V)).coconePointUniqueUpToIso (hcol m)
  have he (m : ℕ) : cokernel.π ((ℓ : ℤ) ^ (m + 1) • 𝟙 V) ≫ (e m).hom =
      π.app (op m) :=
    (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom (hcol m)
      WalkingParallelPair.one
  let α : addOpFunctor 1 ⋙ U ≅ X.asFunctor := NatIso.ofComponents
    (fun m ↦ e m.unop) (by
      intro i j f
      apply (cancel_epi (cokernel.π ((ℓ : ℤ) ^ (i.unop + 1) • 𝟙 V))).1
      change cokernel.π _ ≫
        (CategoryTheory.RegularScalarQuotient.map (ℓ : ℤ) V
          (Nat.add_le_add_right (leOfHom f.unop) 1) ≫ (e j.unop).hom) =
        cokernel.π _ ≫ ((e i.unop).hom ≫ X.asFunctor.map f)
      rw [← Category.assoc, CategoryTheory.RegularScalarQuotient.π_map,
        he, ← Category.assoc, he]
      have hn := π.naturality f
      change (𝟙 V) ≫ π.app j = π.app i ≫ X.asFunctor.map f at hn
      rw [Category.id_comp] at hn
      exact hn)
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod ℓ W) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) W
  have : HasCountableProducts (DerivedCategory (DiagonalMod ℓ W)) :=
    ⟨fun J _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ J⟩
  obtain ⟨p, hp, hleg⟩ := rlimCone L X
  let αQ := Functor.isoWhiskerRight α.symm DerivedCategory.Q
  let cp := (Cone.postcompose αQ.hom).obj (Cone.mk _ p)
  have hcp : IsHomotopyLimit cp := hp.of_iso αQ cp (Iso.refl _) (by
    intro m
    simp [cp])
  let cf := homotopyLimitCone (U ⋙ DerivedCategory.Q)
  have hcf : IsHomotopyLimit cf :=
    isHomotopyLimit_homotopyLimitCone (U ⋙ DerivedCategory.Q)
  obtain ⟨d, hd⟩ := hcp.exists_iso (hcf.whiskerAdd 1)
  let c := cf.extend d.hom
  have hc : IsHomotopyLimit c := hcf.of_iso (Iso.refl _) c d.symm (by
    intro m
    simp [c])
  have hcleg (m : ℕ) : c.π.app (op (m + 1)) =
      p.app (op m) ≫ DerivedCategory.Q.map (e m).inv := by
    simpa only [c, cp, αQ, α, Cone.extend_π, Cone.postcompose_obj_π,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, NatIso.ofComponents_inv_app,
      addOpFunctor_obj, Cone.whisker_π, Functor.const_map_app] using hd m
  have hi := scalarConeAugmentation_at_zero_isIso (ℓ : ℤ) U hU (n + 1)
    (ℓ ^ (n + 1) : ℕ) (Nat.cast_pow ℓ (n + 1)) c hc
  let B := DiagonalMod ℓ W
  let Z := (diagonalQuotientLevelComplex O n).obj P
  let M := U.obj (op (n + 1))
  let g : M ≅ Z := e n
  let r := ℓ ^ (n + 1)
  let F := diagonalScalarCone B r
  let δ := CochainComplex.LinearScalarCone.comparison (A := B) (r : ℤ)
  let qZ := (diagonalQuotientLevelConeProjection O n).app P
  let S₀ : ShortComplex (CochainComplex B ℤ) :=
    ShortComplex.mk ((r : ℤ) • 𝟙 M) (𝟙 M) (by
      simpa only [Category.comp_id, r, ← Nat.cast_pow] using hU.smul_eq_zero (n + 1))
  let a := CochainComplex.ConeCoimage.ρ.app (Arrow.mk S₀.f) ≫
    CochainComplex.ConeCoimage.desc.app (Arrow.mk S₀.f) ≫
    cokernel.desc S₀.f (𝟙 M) S₀.zero
  have ha : a = CochainComplex.mappingCone.descShortComplex S₀ :=
    coneCokernelDesc (Arrow.mk S₀.f) (𝟙 M) S₀.zero
      (cokernel.desc S₀.f (𝟙 M) S₀.zero) (cokernel.π_desc _ _ _)
  let t : S₀ ⟶ diagonalQuotientLevelSequence O n P :=
    { τ₁ := g.hom, τ₂ := g.hom, τ₃ := g.hom
      comm₁₂ := by
        simp only [S₀, r, diagonalQuotientLevelSequence, natCast_zsmul,
          Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp, Category.comp_id]
      comm₂₃ := by simp only [S₀, diagonalQuotientLevelSequence,
        Category.id_comp, Category.comp_id] }
  have hbridge : (CochainComplex.LinearScalarCone.cochain (r : ℤ)).map g.hom ≫
      (diagonalScalarConeComplexComparison B r).hom.app Z ≫ qZ = a ≫ g.hom := by
    rw [ha]
    change CochainComplex.mappingCone.map _ _ g.hom g.hom
        (by simp [S₀, Linear.smul_comp, Linear.comp_smul]) ≫
      CochainComplex.mappingCone.map _ _ (𝟙 Z) (𝟙 Z)
        (by
          change ((r : ℤ) • 𝟙 Z) ≫ 𝟙 Z = 𝟙 Z ≫ (r • 𝟙 Z)
          simp only [Category.comp_id, Category.id_comp, natCast_zsmul]) ≫
        CochainComplex.mappingCone.descShortComplex (diagonalQuotientLevelSequence O n P) =
      CochainComplex.mappingCone.descShortComplex S₀ ≫ g.hom
    rw [← Category.assoc, ← CochainComplex.mappingCone.map_comp]
    simpa only [Category.comp_id] using CochainComplex.mappingCone.map_descShortComplex
      S₀ (diagonalQuotientLevelSequence O n P) t
  have hi' : IsIso (F.map (c.π.app (op (n + 1))) ≫ δ.hom.app M ≫
      DerivedCategory.Q.map a) := by
    exact hi
  have hm : IsIso (F.map (c.π.app (op (n + 1))) ≫ δ.hom.app M ≫
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map g.hom) := by
    have := hi'
    have h : IsIso ((F.map (c.π.app (op (n + 1))) ≫ δ.hom.app M ≫
        DerivedCategory.Q.map a) ≫ DerivedCategory.Q.map g.hom) := inferInstance
    simpa only [Category.assoc] using h
  have hg : c.π.app (op (n + 1)) ≫ DerivedCategory.Q.map g.hom = p.app (op n) := by
    rw [hcleg]
    change (p.app (op n) ≫ DerivedCategory.Q.map (e n).inv) ≫
      DerivedCategory.Q.map (e n).hom = p.app (op n)
    rw [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id,
      DerivedCategory.Q.map_id]
    exact Category.comp_id (p.app (op n))
  have hcmp : F.map (c.π.app (op (n + 1))) ≫ δ.hom.app M ≫
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map g.hom =
      F.map (p.app (op n)) ≫ (diagonalScalarConeFactors B r).hom.app Z ≫
        DerivedCategory.Q.map qZ := by
    calc
      _ = F.map (c.π.app (op (n + 1))) ≫ δ.hom.app M ≫
          DerivedCategory.Q.map ((CochainComplex.LinearScalarCone.cochain (r : ℤ)).map
            g.hom) ≫ DerivedCategory.Q.map
            ((diagonalScalarConeComplexComparison B r).hom.app Z) ≫
          DerivedCategory.Q.map qZ := by
        rw [← DerivedCategory.Q.map_comp, ← hbridge]
        simp only [Functor.map_comp]; rfl
      _ = F.map (c.π.app (op (n + 1))) ≫ F.map (DerivedCategory.Q.map g.hom) ≫
          δ.hom.app Z ≫ DerivedCategory.Q.map
            ((diagonalScalarConeComplexComparison B r).hom.app Z) ≫
          DerivedCategory.Q.map qZ := by
        have hδ : F.map (DerivedCategory.Q.map g.hom) ≫ δ.hom.app Z =
            δ.hom.app M ≫ DerivedCategory.Q.map
              ((CochainComplex.LinearScalarCone.cochain (r : ℤ)).map g.hom) :=
          δ.hom.naturality g.hom
        rw [← Category.assoc (δ.hom.app M), ← hδ]
        simp only [Category.assoc]
      _ = F.map (c.π.app (op (n + 1)) ≫ DerivedCategory.Q.map g.hom) ≫
          (diagonalScalarConeFactors B r).hom.app Z ≫ DerivedCategory.Q.map qZ := by
        simp only [Functor.map_comp, diagonalScalarConeFactors, Iso.trans_hom,
          NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
          Category.assoc, δ]
      _ = _ := by rw [hg]
  rw [hcmp] at hm
  have hfinal : (diagonalTowerScalarConeComparison O L n).app P =
      (F.map (p.app (op n)) ≫ (diagonalScalarConeFactors B r).hom.app Z ≫
        DerivedCategory.Q.map qZ) ≫ (diagonalQuotientLevelFactors O n).inv.app P := by
    dsimp only [diagonalTowerScalarConeComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp]
    rw [hleg, F.map_comp]
    simp only [Category.assoc]
    rfl
  rw [hfinal]
  have := hm
  infer_instance

end AlgebraicGeometry.ProEtale
