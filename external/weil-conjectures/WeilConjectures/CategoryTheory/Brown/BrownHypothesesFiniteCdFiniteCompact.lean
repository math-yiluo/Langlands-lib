/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCoefficientIso
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

/-! # Finite-coefficient compactness from finite base cohomological dimension

This is the finite-coefficient compactness input needed by the corrected Brown theorem.
The existing finite-coefficient compactness theorem is specialized to finite or separably
closed fields; the present statement isolates its finite-cohomological-dimension extension.
(blueprint: lem-sfb-brown-finite-cd-finite-compact)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

private theorem ell_torsion_of_annihilated
    {A : Type u} [Category.{v} A] [Abelian A] [HasColimitsOfShape ℕ A]
    (l : ℕ) (hl : l.Prime) (M : A) (e : ℕ) (he : (l ^ e) • 𝟙 M = 0) :
    IsEllPowerTorsion l hl M := by
  have hi : 𝟙 M ≫ ((l ^ e) • 𝟙 M) = 0 := by simpa using he
  let D := ellPowerKernelFunctor l (F := M)
  let a := ellPowerKernelColimitMap l (F := M)
  let b : M ⟶ colimit D :=
    kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e
  have hba : b ≫ a = 𝟙 M := by
    dsimp [b, a, ellPowerKernelColimitMap]
    rw [Category.assoc, colimit.ι_desc]
    exact kernel.lift_ι _ _ _
  have hab : a ≫ b = 𝟙 (colimit D) := by
    apply colimit.hom_ext
    intro r
    let t := e + r
    have her : e ≤ t := Nat.le_add_right e r
    have hrt : r ≤ t := Nat.le_add_left r e
    have hmap : kernel.ι ((l ^ r) • 𝟙 M) ≫
        kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ D.map (homOfLE her) =
        D.map (homOfLE hrt) := by
      apply (cancel_mono (kernel.ι ((l ^ t) • 𝟙 M))).mp
      simp only [D, ellPowerKernelFunctor, ellPowerKernelMap, Category.assoc,
        kernel.lift_ι, Category.comp_id]
    calc
      colimit.ι D r ≫ a ≫ b =
          kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e := by
        dsimp [a, b, ellPowerKernelColimitMap]
        rw [← Category.assoc, colimit.ι_desc]
        rfl
      _ = kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫
              D.map (homOfLE her) ≫ colimit.ι D t := by rw [colimit.w]
      _ = D.map (homOfLE hrt) ≫ colimit.ι D t := by
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ colimit.ι D t) hmap
      _ = colimit.ι D r ≫ 𝟙 _ := by rw [colimit.w, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

private theorem module_cd_of_prime_cd
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hcd : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤)
    (A : Type (u + 1)) [CommRing A] (r : ℕ) (hr : (ℓ ^ r : A) = 0) :
    Etale.HasFiniteCohomologicalDimension A (Spec (.of k)) := by
  classical
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hcd)
  have hde : etaleCohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) = d := by
    rw [← cohomologicalDimension_eq_etaleCohomologicalDimension, ← hd]
    rfl
  refine ⟨d, fun F q hq ↦ ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
  let B := (Etale.sheafForget₂ A (Spec (.of k))).obj F
  have ht : IsEllPowerTorsion ℓ (Fact.out : ℓ.Prime) B := by
    apply ell_torsion_of_annihilated ℓ (Fact.out : ℓ.Prime) B r
    apply Sheaf.hom_ext
    ext U x
    have hzero (y : F.obj.obj U) : (ℓ ^ r) • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, hr, zero_smul]
    exact hzero x
  have hz : IsZero ((Etale.cohomology Ab.{u + 1} (Spec (.of k)) (n : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj B)) := by
    by_contra hn
    have hle : (n : WithTop ℕ) ≤
        etaleCohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) :=
      le_sSup ⟨n, rfl, B, ht, hn⟩
    rw [hde] at hle
    exact (not_le_of_gt (by omega : d < n)) (WithTop.coe_le_coe.mp hle)
  obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso (Spec (.of k)) A n
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero (hz.of_iso (e.app F)))

private theorem ordinary_constructible_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryConstructible A T M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [FiniteDiscreteOrdinary.ordinaryConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ (hC i.down).imp fun _ hP ↦
        ⟨by have := hP.1; exact Module.Finite.of_finite, hP.2⟩⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      (h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)).imp fun _ hP ↦
        ⟨by have := hP.1; exact Module.finite_of_finite (ULift.{u + 1} A), hP.2⟩⟩

private theorem ordinary_ctf_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    FiniteDiscreteOrdinary.ordinaryCtf A T K ↔
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
  have hb : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
    constructor
    · rintro ⟨hb, hc⟩
      apply DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A) hb
      intro n
      exact exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} A)
        ((ordinary_constructible_iff A T _).mp (hc n))
    · intro h
      have hi := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ h
      exact ⟨hi.1, fun n ↦ (ordinary_constructible_iff A T _).mpr (hi.2 n)⟩
  exact and_congr hb Iff.rfl

private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩

/-- For a finite discrete admissible coefficient, finite ℓ-cohomological dimension of the
base field gives the objectwise compactness clause in the Noetherian Brown criterion.

Source: blueprint `proposition-compactness-finite-coefficients` and
`sk-lem-brown-hypotheses.proof.md`, compactness paragraph. Proof: transport a bounded constructible
finite-Tor complex to the finite-coefficient étale model, apply the finite-coefficient compactness
argument using the finite torsion cohomological-dimension bound supplied by
`cohomologicalDimension_lt_top_of_finiteType`, and transport compactness back through the
finite discrete coefficient equivalence. The construction is uniform in the finite ring,
the scheme, and the object; the empty scheme and zero ring are included. -/
theorem brownHypotheses_compact_of_finite_cd_finite
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (hpl : p ≠ ℓ)
    (hcd : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) :
    ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
      letI := hSums
      ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
        (constantModelBoundedConstructible Λ X K.obj ∧
          DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K := by
  classical
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  obtain ⟨A, _, _, _, _, hA, ⟨r, hr⟩, ⟨e⟩⟩ := hΛ
  let _ := hA
  let B := ULift.{u} A
  have hpB : (ℓ ^ r : ULift.{u + 1} B) = 0 := by
    apply ULift.ext
    apply ULift.ext
    change (ℓ : A) ^ r = 0
    simpa using hr 1
  have hbase := module_cd_of_prime_cd ℓ k hcd (ULift.{u + 1} B) r hpB
  let _ : HasInvertibleExponent (ULift.{u + 1} B) (Spec (.of k)) := by
    refine ⟨ℓ ^ r, pow_pos (Fact.out : ℓ.Prime).pos _, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hpB
    · have hℓ : (ℓ : k) ≠ 0 :=
        CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hpl
      simpa using (isUnit_iff_ne_zero.mpr (pow_ne_zero r hℓ)).map
        (Scheme.ΓSpecIso (.of k)).inv.hom
  let _ : HasInvertibleExponent (ULift.{u + 1} B) X :=
    HasInvertibleExponent.of_hom aX
  obtain ⟨ea⟩ := finiteCoefficientLiftIso.{u} A
  let R := Profinite.continuousCoefficientRingObj B
  have hR : IsLocalizingAdmissibleCoefficient ℓ R := by
    exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨r, hr⟩, ⟨ea.symm⟩⟩
  have hBR : BrownHypothesesFor R X := by
    obtain ⟨E, hE, _⟩ :=
      FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence B
    obtain ⟨_, _, _, _, hctf, _, _, _, hloc⟩ := hE X
    let d := (E X).fixedDerived
    let L := localizingClosureProEtale R X
    let P := (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).localizingClosure
    have hLP : P.inverseImage d.functor = L := by
      funext K
      apply propext
      have hprop : FiniteDiscreteOrdinary.ordinaryCtf B X =
          AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} B)) X := by
        funext K
        exact propext (ordinary_ctf_iff B X K)
      have h := hloc K
      rw [hprop] at h
      have hclosure : CategoryTheory.localizingClosure
          (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} B)) X) = P := by
        let Q := AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
        funext M
        apply propext
        constructor
        · intro hm
          exact hm P ⟨inferInstance, inferInstance, fun {I} F hF hFP ↦ by
            let _ := hF
            let _ := closedUnderCoproducts_of_small P (fun _ ↦ inferInstance) I
            exact P.prop_of_isColimit (colimit.isColimit F) (fun i ↦ hFP i.as)⟩
            Q.le_localizingClosure
        · intro hm T ht hQT
          let _ := ht.1
          let _ := ht.2.1
          have hbig (I : Type (u + 2)) :
              T.IsClosedUnderColimitsOfShape (Discrete I) :=
            ht.isClosedUnderColimitsOfShape_discrete I
          have _ (I : Type (u + 1)) :
              T.IsClosedUnderColimitsOfShape (Discrete I) :=
            ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
              (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
          exact hm T hQT { isClosedUnderColimitsOfShape_discrete := fun _ ↦ inferInstance }
      rw [hclosure] at h
      exact h.symm
    let dL := d.congrFullSubcategory hLP
    have _ : dL.functor.Additive :=
      ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _
        (d.functor.map_add (f := f.hom) (g := g.hom))⟩
    have _ : dL.inverse.Additive :=
      ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _
        (d.inverse.map_add (f := f.hom) (g := g.hom))⟩
    have _ : dL.symm.functor.Additive := inferInstanceAs dL.inverse.Additive
    obtain ⟨_, _, _, _, hSums, _⟩ := brownHypotheses_structural R X
    apply (brownHypothesesFor_iff_compact_of_noetherian ℓ X R hR).mpr
    refine ⟨hSums, fun K hK ↦ ?_⟩
    have hc : BrownRepresentability.IsCompactObj (dL.functor.obj K) := by
      apply AlgebraicGeometry.ProEtale.DerivedCategory.isCompactObj_of_constructibleFiniteTor
        hbase aX
      exact (ordinary_ctf_iff B X _).mp ((hctf K.obj).mp hK)
    exact (isCompactObject_iff_isCompactObj K).mpr
      ((hc.of_adjunction dL.symm.toAdjunction).of_iso (dL.unitIso.app K))
  have hB := (brownHypothesesFor_coefficientIso_iff (e ≪≫ ea) X).mpr hBR
  exact ((brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ
    (Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨r, hr⟩, ⟨e⟩⟩)).mp hB)

end CategoryTheory
