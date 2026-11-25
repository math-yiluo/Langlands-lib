/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionConstructibility
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.CategoryTheory.ConstantInverseImageScalarNormalization
import all WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # AdicFiniteEtaleOrigins
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

private theorem adicFiniteOrdinaryPullback_comparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Nonempty (adicFiniteOrdinaryPullback.{u, v} X A ≅
      ProEtale.constructibleComparisonPullback.{u, v} X A) := by
  let J := smallModelComparisonEtaleTopology.{u, v} X
  let K := coefficientProEtaleModelTopology.{u, v} X
  let G := smallModelComparisonInclusion.{u, v} X
  let L := smallModelComparisonPullback.{u, v} X
  let adj := smallModelProEtaleComparison.{u, v} X
  let := smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  let R := constant J A
  let S := constant K A
  let F := adicFiniteComparisonData.{u, v} X
  let φ : R ⟶ (G.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S :=
    ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
      ((Functor.const _).obj (CommRingCat.of A))
      ((G.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S)).symm
        (Functor.whiskerLeft G.op
          (toSheafify K ((Functor.const _).obj (CommRingCat.of A))))
  let p := siteContinuousRingedTopos G L adj S R φ
  let AI := F.algebra R
  let c := constantMap F A
  have hn : AI.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{max v (u + 1)})).map c = p.ringMap :=
    constantInverseImageScalarNormalization J K G L adj F A
  have hc : (sheafCompose K (CategoryTheory.forget CommRingCat.{max v (u + 1)})).map c =
      AI.ringUnderlying.inv ≫ p.ringMap := by
    rw [← hn, Iso.inv_hom_id_assoc]
  obtain ⟨am, _⟩ := supplied_module_adjunction p (F.rings.obj R) AI c hc
  have am' : adicFiniteOrdinaryPullback.{u, v} X A ⊣
      SheafOfModules.pushforward (ProEtale.constructibleComparisonRingMap X A) := am
  exact ⟨am'.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction
      (ProEtale.constructibleComparisonRingMap X A))⟩

private theorem adicFinitePullback_comparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (D : ConstantCompletion.D (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
      adicFiniteAmbient.{u, v} X A)
    (α : Q _ ⋙ D ≅ ProEtale.constructibleComparisonComplexPullback X A ⋙ Q _) :
    Nonempty (adicFinitePullback.{u, v} X A ≅ D) := by
  let R := constant (smallModelComparisonEtaleTopology.{u, v} X) A
  let S := constant (coefficientProEtaleModelTopology.{u, v} X) A
  let := HasDerivedCategory.standard (Mod R)
  let W := HomologicalComplex.quasiIso (Mod R) (.up ℤ)
  obtain ⟨e⟩ := adicFiniteOrdinaryPullback_comparison X A
  have : (ProEtale.constructibleComparisonPullback X A).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint
      (ProEtale.constructibleComparisonPullback X A)
  let ε := adicFinitePullbackComparison.{u, v} X A
  have : (adicFinitePullback.{u, v} X A).IsLeftDerivedFunctor ε W :=
    (adicFinitePullbackData.{u, v} X A).universal
  have : D.IsLeftDerivedFunctor α.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W D α
  let τ : (adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex (.up ℤ) ⋙ Q S ≅
      ProEtale.constructibleComparisonComplexPullback X A ⋙ Q S :=
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) (Q S)
  exact ⟨Functor.leftDerivedNatIso _ _ ε α.hom W τ⟩

private theorem adicFiniteTor_iso {T : Type*} [SmallCategory T]
    {t : GrothendieckTopology T} (R : Sheaf t CommRingCat)
    {K L : D R} (i : K ≅ L) (a b : ℤ)
    (h : HasCoefficientModelTorAmplitude R K a b) :
    HasCoefficientModelTorAmplitude R L a b := by
  exact ⟨h.1, fun P hP ⟨f⟩ ↦ h.2 P hP ⟨f ≪≫ i.symm⟩⟩

private theorem adicFiniteTor_cohomology_bounds {T : Type*} [SmallCategory T]
    {t : GrothendieckTopology T} (R : Sheaf t CommRingCat)
    (M : D R) (a b : ℤ) (h : HasCoefficientModelTorAmplitude R M a b) :
    ∀ q : ℤ, q < a ∨ b < q → IsZero ((coefficientModelCohomology R q).obj M) := by
  let := HasDerivedCategory.standard (Mod R)
  obtain ⟨P, hge, hle, _, ⟨i⟩⟩ :=
    (coefficientModelTorAmplitude_iff_flatModel R M a b h.1).mp h
  let := hge
  let := hle
  intro q hq
  let iH := (coefficientModelCohomology R q).mapIso i.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (Mod R) q).app P
  rcases hq with hq | hq
  · exact (P.isZero_of_isGE a q hq).of_iso iH
  · exact (P.isZero_of_isLE b q hq).of_iso iH

private theorem adicFiniteBoundedConstructible_iso (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    {K L : adicFiniteAmbient.{u, v} X A} (i : K ≅ L)
    (hK : ProEtale.coefficientBoundedConstructibleProEtale X A K) :
    ProEtale.coefficientBoundedConstructibleProEtale X A L := by
  constructor
  · intro q
    exact ProEtale.coefficientProEtale_constructible_of_iso X A
      ((coefficientModelCohomology _ q).mapIso i) (hK.1 q)
  · obtain ⟨a, b, hab, hv⟩ := hK.2
    exact ⟨a, b, hab, fun q hq ↦
      (hv q hq).of_iso ((coefficientModelCohomology _ q).mapIso i.symm)⟩

/-- Each reduction has a bounded constructible etale origin with the same Tor
interval. No compatibility or residue marking is asserted here.
Source: Stacks Project, proetale.tex, Tag 09C2 (3)-(4) and Tag 09AL.
(auxiliary; not a blueprint node).

Proof: Identify the ordinary comparison functors as left adjoints of the same
module direct image. Constant inverse-image scalar normalization supplies the
required equality of ring maps. Uniqueness of left derived functors then identifies
adicFinitePullback with the derived comparison used by constructibleComparison.
The latter's bounded constructible equivalence and the given e show that the
residue reduction is bounded constructible. Apply the coefficient-filtration
constructibility lemma (Tag 09BR) to obtain constructible cohomology at every
level. The flat-model characterization of the assumed Tor interval bounds each
reduction in [a,b]. Apply the finite-Tor comparison equivalence to this bounded
constructible finite-Tor object. Its counit gives an etale origin, and reflection
of the Tor test gives precisely [a,b]. Transport its comparison isomorphism back
along the identification with adicFinitePullback. Each level is treated separately,
so no compatibility or prescribed zero marking is introduced. -/
theorem adicFiniteEtale_origins
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    (C : adicFiniteEtale.{u, v} X J 0)
    (hC : IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J 0) C)
    (e : (adicFinitePullback.{u, v} X (adicFiniteCoeff J 0)).obj C ≅
      adicFiniteReduction.{u, v} X J N 0)
    (a b : ℤ)
    (hTor : ∀ n : ℕ, HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J n)
      (adicFiniteReduction.{u, v} X J N n) a b) :
    ∀ n : ℕ, ∃ Cn : adicFiniteEtale.{u, v} X J n,
      IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J n) Cn ∧
      HasCoefficientModelTorAmplitude
        (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J n)) Cn a b ∧
      Nonempty ((adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).obj Cn ≅
        adicFiniteReduction.{u, v} X J N n) := by
  have hres : ProEtale.coefficientBoundedConstructibleProEtale X (adicFiniteCoeff J 0)
      (adicFiniteReduction X J N 0) := by
    obtain ⟨D, ⟨α⟩, E, ⟨β⟩⟩ := (ProEtale.constructibleComparison X (adicFiniteCoeff J 0)).2.2.2
    obtain ⟨γ⟩ := adicFinitePullback_comparison X (adicFiniteCoeff J 0) D α
    let C' : CoefficientBoundedConstructibleEtaleCategory X (adicFiniteCoeff J 0) := ⟨C, hC⟩
    let i : (E.functor.obj C').obj ≅ adicFiniteReduction X J N 0 :=
      β.app C' ≪≫ (γ.app C).symm ≪≫ e
    exact adicFiniteBoundedConstructible_iso X (adicFiniteCoeff J 0) i
      (E.functor.obj C').property
  have hc := adicFiniteReduction_constructible_cohomology X A J N hres
  intro n
  let B := adicFiniteCoeff J n
  let M := adicFiniteReduction X J N n
  have hM : ProEtale.coefficientBoundedConstructibleProEtale X B M :=
    ⟨hc n, a, b, (hTor n).1, adicFiniteTor_cohomology_bounds _ M a b (hTor n)⟩
  obtain ⟨D, ⟨α⟩, ht, E, ⟨β⟩⟩ := ProEtale.finiteTorComparisonNoetherian X B
  obtain ⟨γ⟩ := adicFinitePullback_comparison X B D α
  let M' : ObjectProperty.FullSubcategory
      (fun K ↦ ProEtale.coefficientBoundedConstructibleProEtale X B K ∧
        HasFiniteCoefficientProEtaleTorAmplitude X B K) := ⟨M, hM, a, b, hTor n⟩
  let C' := E.inverse.obj M'
  let i : D.obj C'.obj ≅ M := (β.app C').symm ≪≫
    (ObjectProperty.ι _).mapIso (E.counitIso.app M')
  refine ⟨C'.obj, C'.property.1, ?_, ⟨γ.app C'.obj ≪≫ i⟩⟩
  exact (ht C'.obj C'.property.1 a b (hTor n).1).mpr
    (adicFiniteTor_iso _ i.symm a b (hTor n))

end AlgebraicGeometry.Scheme
