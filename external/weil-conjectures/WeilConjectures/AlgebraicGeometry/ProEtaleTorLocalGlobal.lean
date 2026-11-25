/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel

/-!
# Local and global finite Tor dimension on a quasi-compact pro-etale site

Source: Stacks Project, Tags 08FZ and 09C2, the uniform Tor interval in the proof of
`lemma-describe-constructible-complexes`
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The recorded exact derived slice restriction at the standard localizations used by
`HasCoefficientModelTorAmplitude`. Both rings are the actual sectionwise restrictions.
Source: Stacks Tags 03DH and 08JB (auxiliary; not a blueprint node). -/
def coefficientModelSliceRestriction {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (V : C) :
    ConstantCompletion.D R ⥤ ConstantCompletion.D (R.over V) :=
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (SheafOfModules.{w} ((siteModuleRings R).over V))
  ringedDerivedRestrictionSized (siteModuleRings R) V

end CategoryTheory

section ProofHelpers
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MonoidalCategory
namespace CategoryTheory

-- Restrict a bounded flat model, using the coefficient-sized flat-model criterion.
private theorem coefficientModelTorAmplitude_restrict
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (V : C)
    (M : ConstantCompletion.D R) (a b : ℤ)
    (h : HasCoefficientModelTorAmplitude R M a b) :
    HasCoefficientModelTorAmplitude (R.over V)
      ((coefficientModelSliceRestriction R V).obj M) a b := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (R.over V))
  let A := siteModuleRings R
  let F : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod (R.over V) :=
    SheafOfModules.overFunctor.{w} A V
  have : F.Additive := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).1
  have : PreservesFiniteLimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.1
  have : PreservesFiniteColimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.2
  obtain ⟨P, hge, hle, hflat, ⟨e⟩⟩ :=
    (coefficientModelTorAmplitude_iff_flatModel R M a b h.1).mp h
  let B : ConstantCompletion.Cx (R.over V) := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hBge : B.IsStrictlyGE a := (B.isStrictlyGE_iff a).mpr (fun i hi ↦
    F.map_isZero (P.isZero_of_isStrictlyGE a i hi))
  have hBle : B.IsStrictlyLE b := (B.isStrictlyLE_iff b).mpr (fun i hi ↦
    F.map_isZero (P.isZero_of_isStrictlyLE b i hi))
  apply (coefficientModelTorAmplitude_iff_flatModel (R.over V) _ a b h.1).mpr
  refine ⟨B, hBge, hBle, fun i ↦ ?_, ?_⟩
  · exact SheafOfModules.isFlat_over (P.X i) V (hflat i)
  · exact ⟨(F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e⟩

-- Exact K-flat restriction and natural tensor restriction; Tags 0E8K, 07A4 and 08FZ.
private theorem coefficientModelTorAmplitude_restricted_test_isZero
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (V : C)
    (M : ConstantCompletion.D R) (a b : ℤ)
    (h : HasCoefficientModelTorAmplitude (R.over V)
      ((coefficientModelSliceRestriction R V).obj M) a b)
    (P : ConstantCompletion.Cx R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (e : Nonempty ((ConstantCompletion.Q R).obj P ≅ M))
    (N : ConstantCompletion.Mod R) (q : ℤ) (hq : q < a ∨ b < q) :
    IsZero ((SheafOfModules.overFunctor (siteModuleRings R) V).obj
      ((((ringedKoszulTensor R).obj P).obj
        ((HomologicalComplex.single (ConstantCompletion.Mod R)
          (ComplexShape.up ℤ) 0).obj N)).homology q)) := by
  classical
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (R.over V))
  let A := siteModuleRings R
  let F : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod (R.over V) :=
    SheafOfModules.overFunctor.{w} A V
  have : F.Additive := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).1
  have : PreservesFiniteLimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.1
  have : PreservesFiniteColimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.2
  let FC := F.mapHomologicalComplex (.up ℤ)
  have hres : CochainComplex.IsKFlatIndependentCoefficients (R := R.over V) (FC.obj P) :=
    (SheafOfModules.ringedSite_restriction_exact_kflat.{w, w, w} J R V).2.2 P hP
  obtain ⟨e⟩ := e
  have er : Nonempty ((ConstantCompletion.Q (R.over V)).obj (FC.obj P) ≅
      (coefficientModelSliceRestriction R V).obj M) :=
    ⟨(F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e⟩
  have hz := h.2 (FC.obj P) hres er (F.obj N) q hq
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (R.over V)
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed (R.over V)).1
  let d : tensorRight N ⋙ F ≅ F ⋙ tensorRight (F.obj N) :=
    NatIso.ofComponents
      (fun L ↦ SheafOfModules.sliceTensorIso (J := J.over V) (Over.forget V) R L N)
      (by
        intro L L' f
        simpa [F, SheafOfModules.sliceCommModuleRestriction,
          SheafOfModules.sliceModuleRestriction, SheafOfModules.overFunctor] using
          SheafOfModules.sliceTensorIso_natural (J := J.over V)
          (Over.forget V) R f (𝟙 N))
  let dC := ((Functor.mapHomologicalComplexCompIso (Iso.refl (tensorRight N ⋙ F))
    (.up ℤ)).app P) ≪≫ ((NatIso.mapHomologicalComplex d (.up ℤ)).app P) ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ tensorRight (F.obj N)))
        (.up ℤ)).app P).symm
  let K := CochainComplex.mapBifunctor P
    ((HomologicalComplex.single _ (.up ℤ) 0).obj N) (curriedTensor _)
  let c := FC.mapIso (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N P) ≪≫
    dC ≪≫ (CochainComplex.mapBifunctorSingle₂Iso
      (curriedTensor _) (F.obj N) (FC.obj P)).symm
  let hc := ((K.sc q).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso c
  exact hz.of_iso hc

-- Detect zero sectionwise using uniqueness for covering sieves; Stacks Tag 00VR.
private theorem isZero_of_slice_cover
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat) {I : Type*} (V : I → C) (hV : J.CoversTop V)
    (F : SheafOfModules R)
    (hF : ∀ i, IsZero ((SheafOfModules.overFunctor R (V i)).obj F)) : IsZero F := by
  apply (IsZero.iff_id_eq_zero F).2
  apply (SheafOfModules.toSheaf R).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply F.isSheaf.hom_ext (hV.cover U.unop)
  rintro ⟨W, f, ⟨i, ⟨g⟩⟩⟩
  have h := congrArg
    (fun k ↦ k.val.app (Opposite.op (Over.mk g)))
    ((hF i).eq_of_src (𝟙 _) 0)
  have hz : (𝟙 (F.val.presheaf.obj (Opposite.op W))) = 0 := by
    apply AddCommGrpCat.hom_ext
    exact congrArg (fun k ↦ k.hom.toAddMonoidHom) h
  change (𝟙 _ : F.val.presheaf.obj U ⟶ _) ≫ _ = 0 ≫ _
  simp only [Category.id_comp, zero_comp]
  rw [← Category.comp_id (F.val.presheaf.map f.op), hz, comp_zero]

end CategoryTheory
end ProofHelpers

namespace AlgebraicGeometry.Scheme.ProEt
private theorem exists_finite_refinement (T : Scheme.{u}) [CompactSpace T]
    (𝒰 : Scheme.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale) T)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    ∃ 𝒱 : Scheme.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale) T,
      Finite 𝒱.I₀ ∧ QuasiCompactCover 𝒱.toPreZeroHypercover ∧ Nonempty (𝒱 ⟶ 𝒰) := by
  classical
  let 𝒜₀ := T.affineCover.finiteSubcover
  let 𝒜 : Scheme.OpenCover.{u + 1} T := 𝒜₀.reindex (Equiv.ulift : ULift.{u + 1} 𝒜₀.I₀ ≃ 𝒜₀.I₀)
  have : Finite 𝒜.I₀ := inferInstanceAs (Finite (ULift 𝒜₀.I₀))
  have hAffine (a : 𝒜.I₀) : IsAffine (𝒜.X a) := by
    change IsAffine (𝒜₀.X a.down)
    dsimp [𝒜₀]
    infer_instance
  let (a : 𝒜.I₀) : IsAffine (𝒜.X a) := hAffine a
  have hlocal (a : 𝒜.I₀) :
      ∃ (𝒱 : Scheme.AffineCover.{u + 1} @WeaklyEtale (𝒜.X a))
        (r : 𝒱.cover ⟶ 𝒰.pullback₁ (𝒜.f a)),
        Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (r.h₀ j) := by
    let : QuasiCompactCover (𝒰.pullback₁ (𝒜.f a)).toPreZeroHypercover := by
      change QuasiCompactCover (𝒰.toPreZeroHypercover.pullback₁ (𝒜.f a))
      infer_instance
    exact QuasiCompactCover.exists_hom (𝒰.pullback₁ (𝒜.f a))
  choose 𝒱 r hfin _ using hlocal
  let (a : 𝒜.I₀) : Finite (𝒱 a).I₀ := hfin a
  let 𝒜' := 𝒜.changeProp (Q := @WeaklyEtale) (fun _ ↦ inferInstance)
  let 𝒲 := 𝒜'.bind (fun a ↦ (𝒱 a).cover)
  have hqcA : QuasiCompactCover 𝒜'.toPreZeroHypercover := by
    change QuasiCompactCover 𝒜.toPreZeroHypercover
    infer_instance
  have hqcV (a : 𝒜'.I₀) : QuasiCompactCover (𝒱 a).cover.toPreZeroHypercover := by
    infer_instance
  let := hqcA
  let (a : 𝒜'.I₀) := hqcV a
  refine ⟨𝒲, ?_, ?_, ⟨?_⟩⟩
  · change Finite (Σ a : 𝒜.I₀, (𝒱 a).I₀)
    infer_instance
  · change QuasiCompactCover (𝒜'.toPreZeroHypercover.bind
      (fun a ↦ (𝒱 a).cover.toPreZeroHypercover))
    infer_instance
  · exact
    { s₀ := fun p ↦ (r p.1).s₀ p.2
      h₀ := fun p ↦ (r p.1).h₀ p.2 ≫ 𝒰.pullbackHom (𝒜.f p.1) _
      w₀ := fun p ↦ by
        change ((r p.1).h₀ p.2 ≫ 𝒰.pullbackHom (𝒜.f p.1) _) ≫
          𝒰.f _ = (𝒱 p.1).cover.f p.2 ≫ 𝒜.f p.1
        rw [Category.assoc, Cover.pullbackHom_map, ← Category.assoc, (r p.1).w₀ p.2] }

private theorem qc_finite_cover (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] (S : Sieve W) (hS : S ∈ topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ topology X W ∧ ∀ i, S (f i) := by
  classical
  have : (precoverage X).IsStableUnderComposition := by dsimp [precoverage]; infer_instance
  have : (precoverage X).HasIsos := by dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderBaseChange := by dsimp [precoverage]; infer_instance
  obtain ⟨T, hT, hTS⟩ :=
    (precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  let E := T.preZeroHypercover
  let F := ProEt.forget X ⋙ Over.forget X
  let E' := E.map F
  have hE' : E'.presieve₀ ∈ Scheme.proetalePrecoverage W.left := by
    have he : E'.presieve₀ = Presieve.map F T := by
      dsimp only [E']
      rw [PreZeroHypercover.presieve₀_map]
      exact congrArg (Presieve.map F) T.presieve₀_preZeroHypercover
    rw [he]
    exact hT
  let U : W.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'.2⟩
  let : QuasiCompactCover U.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE'.1
  obtain ⟨A, hfin, hqc, ⟨r⟩⟩ := exists_finite_refinement W.left U
  let := hfin
  let := hqc
  have (i : A.I₀) : WeaklyEtale (A.f i) := A.map_prop i
  let V : A.I₀ → X.ProEt := fun i ↦ ProEt.mk (A.f i ≫ W.hom)
  let f : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (A.f i) (by rfl)
  refine ⟨A.I₀, hfin, V, f, ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    change Presieve.map F (Presieve.ofArrows V f) ∈ Scheme.proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    change A.presieve₀ ∈ Scheme.proetalePrecoverage W.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hqc, A.mem₀⟩
  · intro i
    let e := r.s₀ i
    let g : V i ⟶ E.X e := MorphismProperty.Over.homMk (r.h₀ i) (by
      change r.h₀ i ≫ (E.X e).hom = A.f i ≫ W.hom
      have he : r.h₀ i ≫ (E.f e).left = A.f i := r.w₀ i
      rw [← he, Category.assoc]
      congr 1
      simp)
    have hg : g ≫ E.f e = f i := by
      apply (ProEt.forget X).map_injective
      apply Over.OverMorphism.ext
      exact r.w₀ i
    rw [← hg]
    exact S.downward_closed (hTS _ _ e.2) g
end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.Scheme
private theorem model_finite_cover (X : Scheme.{u})
    (U : coefficientProEtaleSiteModel.{u, v} X) [CompactSpace (ULift.down U).left] (S : Presieve U)
    (hS : Sieve.generate S ∈ coefficientProEtaleModelTopology X U) :
    ∃ (I : Type (u + 1)) (_ : Finite I)
      (V : I → coefficientProEtaleSiteModel.{u, v} X) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ coefficientProEtaleModelTopology X U ∧ ∀ i, S (f i) := by
  classical
  let D : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  have : D.IsEquivalence :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, max v (u + 1)}
      (C := X.ProEt)).inverse.IsEquivalence)
  have hs : (Sieve.generate S).functorPushforward D ∈ ProEt.topology X (ULift.down U) :=
    (D.mem_inducedTopology_iff_of_isCoverDense _ _).mp hS
  obtain ⟨I, hi, V, f, hf, hm⟩ := ProEt.qc_finite_cover X (ULift.down U) _ hs
  let := hi
  have hfac (i : I) : ∃ (Z : coefficientProEtaleSiteModel.{u, v} X)
      (g : Z ⟶ U) (k : V i ⟶ (ULift.down Z)), S g ∧ k ≫ g.down = f i := by
    obtain ⟨Z, g, k, hg, he⟩ := hm i
    obtain ⟨T, a, b, ha, hab⟩ := hg
    refine ⟨T, b, k ≫ a.down, ha, ?_⟩
    change (k ≫ D.map a) ≫ D.map b = f i
    rw [Category.assoc, ← Functor.map_comp, hab]
    exact he.symm
  choose Z g k hg he using hfac
  refine ⟨I, hi, Z, g, ?_, hg⟩
  apply (D.mem_inducedTopology_iff_of_isCoverDense _ _).mpr
  rw [Sieve.functorPushforward_ofArrows]
  apply (ProEt.topology X).superset_covering _ hf
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  rw [← he i]
  exact (Sieve.ofArrows (fun i ↦ (ULift.down (Z i)))
    (fun i ↦ (g i).down)).downward_closed (Sieve.ofArrows_mk _ _ i) (k i)
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Global finite Tor dimension is equivalent to finite Tor dimension locally on every
object of the small pro-etale site. A covering is expressed by a presieve whose generated
sieve belongs to the topology; each of its arrows has its own ordered Tor interval.
The coefficient-sized small model retains all objects and coverings of the recorded site.
Source: Stacks Tags 08FZ and 09C2 (auxiliary; not a blueprint node).

Proof:
1. Exact module restriction (`lem-pur-site-restriction-module-adjunction-exact`) commutes
   with cohomology (`lem-weil-pbc-exact-functor-complex-cohomology`). The localization case
   of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` identifies restricted derived
   tensor with derived tensor of restrictions, for arbitrary unbounded complexes.
2. A global interval remains an interval against every slice module by
   `lem-sf-site-tor-interval-restriction`. Use the identity covering of each object.
   The two recorded restrictions both send Q(C) to Q(C|U). The tensor models agree by
   `lem-weil-pbc-site-derived-tensor-descent`, since flat-term K-flat resolutions are K-flat.
3. Conversely, quasi-compactness gives a finite affine open covering of X. Apply the local
   hypothesis to each member. The affine-target finite refinement in
   `definition-small-pro-etale-site` refines each resulting covering to a finite affine covering.
   Compose these coverings, using `def-weil-pbc-sites-and-cohomology`, to obtain a finite covering
   of X.
4. Restrict the selected intervals further along the refinement, again using
   `lem-sf-site-tor-interval-restriction`. Relocalization identifies the iterated restriction
   with restriction to the refined object (`def-pur-localized-ringed-site`). Take the minimum
   of the finitely many lower bounds and 0, and the maximum of the upper bounds and 0.
   This gives an ordered common interval and includes the empty-scheme case.
5. For every global module N and q outside this interval, step 1 identifies the restriction
   of H^q(M tensor N) with the corresponding local cohomology. Step 4 makes each zero.
6. Base change the finite cover to any test object T. Sectionwise slice restriction and
   the sheaf equalizer axiom make sections over T inject into the product of zero groups.
   Thus the global cohomology sheaf is zero. The empty cover has the same conclusion.
-/
theorem hasFiniteCoefficientProEtaleTorAmplitude_iff_locally
    (X : Scheme.{u}) [CompactSpace X]
    (A : Type (max v (u + 1))) [CommRing A]
    (M : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A)) :
    HasFiniteCoefficientProEtaleTorAmplitude X A M ↔
      ∀ U : coefficientProEtaleSiteModel.{u, v} X,
        ∃ S : Presieve U,
          Sieve.generate S ∈ coefficientProEtaleModelTopology.{u, v} X U ∧
            ∀ (V : coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f →
              ∃ a b : ℤ,
                HasCoefficientModelTorAmplitude
                  ((ConstantCompletion.constant
                    (coefficientProEtaleModelTopology.{u, v} X) A).over V)
                  ((coefficientModelSliceRestriction
                    (ConstantCompletion.constant
                      (coefficientProEtaleModelTopology.{u, v} X) A) V).obj M) a b := by
  classical
  let R := ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A
  constructor
  · rintro ⟨a, b, hM⟩ U
    refine ⟨Presieve.singleton (𝟙 U), ?_, ?_⟩
    · simp
    · intro V f hf
      cases hf
      exact ⟨a, b, coefficientModelTorAmplitude_restrict R U M a b hM⟩
  · intro h
    let U : coefficientProEtaleSiteModel.{u, v} X :=
      AsSmall.up.obj (ProEt.mk (𝟙 X))
    have hU : IsTerminal U := IsTerminal.ofUniqueHom
      (fun V ↦ AsSmall.up.map
        (MorphismProperty.Over.homMk (ULift.down V).hom (Category.comp_id _)))
      (by
        intro V f
        apply ULift.ext
        apply (ProEt.forget X).map_injective
        apply Over.OverMorphism.ext
        exact (Category.comp_id _).symm.trans (ULift.down f).hom.w)
    obtain ⟨S, hS, hs⟩ := h U
    have : CompactSpace (ULift.down U).left := inferInstanceAs (CompactSpace X)
    obtain ⟨I, hi, V, f, hV, hmem⟩ := model_finite_cover X U S hS
    let := hi
    have hc : (coefficientProEtaleModelTopology.{u, v} X).CoversTop V :=
      ((coefficientProEtaleModelTopology.{u, v} X).coversTop_iff_of_isTerminal U hU V).mpr
        ((coefficientProEtaleModelTopology.{u, v} X).superset_covering
          (Sieve.ofArrows_le_ofObjects V f) hV)
    choose a b hab using fun i ↦ hs (V i) (f i) (hmem i)
    obtain ⟨a₀, ha₀⟩ := (Set.finite_range a).bddBelow
    obtain ⟨b₀, hb₀⟩ := (Set.finite_range b).bddAbove
    refine ⟨min a₀ 0, max b₀ 0, ?_, ?_⟩
    · exact le_trans (min_le_right _ _) (le_max_right _ _)
    · intro P hP e N q hq
      apply isZero_of_slice_cover (siteModuleRings R) V hc
      intro i
      apply coefficientModelTorAmplitude_restricted_test_isZero R (V i) M
        (a i) (b i) (hab i) P hP e N q
      rcases hq with hq | hq
      · exact Or.inl (lt_of_lt_of_le hq
          (le_trans (min_le_left _ _) (ha₀ (Set.mem_range_self i))))
      · exact Or.inr (lt_of_le_of_lt
          (le_trans (hb₀ (Set.mem_range_self i)) (le_max_left _ _)) hq)

end AlgebraicGeometry.Scheme
