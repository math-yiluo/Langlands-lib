/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientFiniteModuleModels
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelTorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedFiniteTorPerfect
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Uniform perfect models of finite quotients

Source: Stacks Tags 09C2 and 094I
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).

This interface records finite-level models without asserting a completed realization.
All coefficient identifications are normalized on constant sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized comparisons preserve the actual consecutive quotient maps.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: it suffices to test on constant presheaf sections. Naturality of the two
sheafification units reduces both composites to the same constant quotient function. -/
private theorem finitePerfectModelsComparison_step (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hnorm : FinitePerfectModelsNormalized X d φ) (n : ℕ) :
    adicConstantMap X (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)) ≫
        φ n =
      φ (n + 1) ≫
        completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n) := by
  let J := ProEt.topology X
  let q := adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicFiniteCommRing X d n).property
  ext U a
  change (φ n).hom.app U
      ((adicConstantMap X q).hom.app U
        ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1 + 1))).app U a)) =
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app U
      ((φ (n + 1)).hom.app U
        ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1 + 1))).app U a))
  let qlift : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 2)) →+*
      ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) := RingHom.ulift q
  have hq := congrArg (fun k ↦ (k.app U).hom a)
    (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom qlift)))
  change (koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U
      ((RingHom.ulift q) a) =
    (adicConstantMap X q).hom.app U
      ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1 + 1))).app U a) at hq
  rw [← hq, hnorm, hnorm]
  have hs := congrArg
    (fun k ↦ (k.app U).hom ((finiteCoefficientConstants X
      (completedAdicQuotient d (n + 1))).app U a))
    (toSheafify_naturality J (completedAdicFinitePresheafStep X d n))
  have hc : (completedAdicFinitePresheafStep X d n).app U
        ((finiteCoefficientConstants X (completedAdicQuotient d (n + 1))).app U a) =
      (finiteCoefficientConstants X (completedAdicQuotient d n)).app U (qlift a) := by
    apply ContinuousMap.ext
    intro c
    rfl
  simp only [NatTrans.comp_app, RingCat.comp_apply] at hs
  rw [hc] at hs
  change (toSheafify J (finiteCoefficientPresheaf X
      (completedAdicQuotient d n))).app U
        ((finiteCoefficientConstants X (completedAdicQuotient d n)).app U (qlift a)) = _
  simpa only [completedAdicQuotientCommMap, completedAdicRingSystem,
    Functor.ofOpSequence_map_homOfLE_succ, completedAdicFiniteStep,
    finiteCoefficientScalarMap, NatTrans.comp_app, RingCat.comp_apply,
    CommRingCat.hom_ofHom, RingCat.Hom.hom, sheafifyMap, J] using! hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed scalar map is normalized by the finite quotient comparisons.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: test the equality after the constant presheaf unit. The scalar map's defining
projection equation gives the left side, and naturality of the sheafification unit
followed by normalization of the finite comparison gives the right side. -/
private theorem finitePerfectModelsScalar_projection (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hnorm : FinitePerfectModelsNormalized X d φ) (n : ℕ) :
    completedAdicScalar X d ≫ completedAdicCommProjection X d n =
      adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ≫
        φ n := by
  let J := ProEt.topology X
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicFiniteCommRing X d n).property
  ext U a
  have hs := (completedAdicScalar_exists X d).exists.choose_spec n U a
  let qlift : ULift.{t + 1} A →+* completedAdicQuotient d n :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have hq := congrArg (fun k ↦ (k.app U).hom a)
    (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom qlift)))
  change (koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U
      (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) =
    (adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
      ((koszulConstantUnit X A).app U a) at hq
  change (completedAdicProjection X d n).hom.app U
      (((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicScalar X d)).hom.app U ((koszulConstantUnit X A).app U a)) =
    (φ n).hom.app U
      ((adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
        ((koszulConstantUnit X A).app U a))
  rw [← hq, hnorm]
  exact hs

/-- Normalization on constant sections determines a compatible coefficient system.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: precompose each required square with the constant-presheaf sheafification unit.
Naturality identifies the consecutive quotient maps. The defining projection equation
for the completed scalar map identifies the scalar squares. Sheafification's universal
property reflects both equalities back to maps of sheaves. -/
theorem finitePerfectModels_normalized_compatible (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hnorm : FinitePerfectModelsNormalized X d φ) :
    FinitePerfectModelsCompatible X d φ :=
  ⟨finitePerfectModelsComparison_step X d φ hnorm,
    finitePerfectModelsScalar_projection X d φ hnorm⟩

/-- Further restriction is exact and preserves the representative-based derived
restriction isomorphisms. Source: Stacks Tag 03DJ
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: the underlying sheaf functor is pullback to the localized site. It preserves
finite limits and colimits, and the faithful exact forgetful functor reflects short
exactness. Derived composition and the representative localization factors then
identify further restriction with restriction to the smaller chart. -/
private theorem finitePerfectModelsOverMap_exact (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V) :
    (SheafOfModules.overMap.{t + 1} R f).Additive ∧
      PreservesFiniteLimits (SheafOfModules.overMap.{t + 1} R f) ∧
      PreservesFiniteColimits (SheafOfModules.overMap.{t + 1} R f) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let H := (ProEt.topology X).overMapPullback AddCommGrpCat.{t + 1} f
  have hAdd : F.Additive := ⟨fun {_ _} a b ↦ by ext V x; rfl⟩
  let e : F ⋙ SheafOfModules.toSheaf.{t + 1} (R.over U) ≅
      SheafOfModules.toSheaf.{t + 1} (R.over V) ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesColimitsOfSize.{t + 1, t + 1} H :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{t + 1}
      ((ProEt.topology X).over U) ((ProEt.topology X).over V)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits H :=
    PreservesColimitsOfSize.preservesFiniteColimits H
  have h (S : ShortComplex (SheafOfModules.{t + 1} (R.over V))) (hS : S.ShortExact) :
      (S.map F).ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.toSheaf.{t + 1} (R.over U))
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e.symm)
      ((hS.map_of_exact (SheafOfModules.toSheaf.{t + 1} (R.over V))).map_of_exact H)
  exact ⟨hAdd, (Functor.exact_tfae F).out 1 4 |>.mp h⟩

/-- The exact derived restriction agrees with the chosen representative formula.
Source: Stacks Tags 03DJ and 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private def finitePerfectModelsRestrictionComparison (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (M : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj M ≅
      ringedSiteDerivedRestrictionOfUniverses R U M := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

/-- A local isomorphism persists on every smaller chart.
Source: Stacks Tag 03DJ
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private theorem finitePerfectModelsRestrictIso_further (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V)
    (M N : DerivedCategory (SheafOfModules.{t + 1} R))
    (e : ringedSiteDerivedRestrictionOfUniverses R V M ≅
      ringedSiteDerivedRestrictionOfUniverses R V N) :
    Nonempty (ringedSiteDerivedRestrictionOfUniverses R U M ≅
      ringedSiteDerivedRestrictionOfUniverses R U N) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let FV := SheafOfModules.overFunctor.{t + 1} R V
  let FU := SheafOfModules.overFunctor.{t + 1} R U
  have := (finitePerfectModelsOverMap_exact X R f).1
  have := (finitePerfectModelsOverMap_exact X R f).2.1
  have := (finitePerfectModelsOverMap_exact X R f).2.2
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  have := (ringedOverFunctor_exactGeneral R V).1
  have := (ringedOverFunctor_exactGeneral R V).2.1
  have := (ringedOverFunctor_exactGeneral R V).2.2
  have c (K : DerivedCategory (SheafOfModules.{t + 1} R)) :
      F.mapDerivedCategory.obj (ringedSiteDerivedRestrictionOfUniverses R V K) ≅
        ringedSiteDerivedRestrictionOfUniverses R U K :=
    F.mapDerivedCategory.mapIso (finitePerfectModelsRestrictionComparison X R V K).symm ≪≫
      (Functor.mapDerivedCategoryCompIso FV F).app K ≪≫
      (Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap R f)).app K ≪≫
      finitePerfectModelsRestrictionComparison X R U K
  exact ⟨(c M).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫ c N⟩
/-- One step of the perfect-residue coefficient filtration preserves local models
and their fixed Tor interval. No completeness or simultaneous trivialization is assumed.

Source: Stacks Project, sites-cohomology.tex, Tag 094I; proetale.tex, Tag 09C2;
connected etale perfect constancy.
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).

Proof: refine the two etale covers giving the residue and previous-level models to
one cover. Tensor the constant quotient sequence with a flat K-flat representative
of M. Its kernel term is the residue model tensored with I^(n+1)/I^(n+2), by
balancing. This is a bounded constant complex with finite cohomology. The previous
model supplies the other outer term. The weak Serre theorem over the Noetherian
finite coefficient ring gives locally constant finite cohomology of the middle
term, with the same bounds. Finite-ring constructible derived origin descends it to
the etale site. Full faithfulness transports its residue marking. Nilpotent-reduction
lissity makes its etale cohomology finite locally constant. For the Tor bound, tensor
with an arbitrary module and use its finite ideal filtration: each quotient is an
A/I-module, so balancing with the residue model gives vanishing outside [a,b].
Connected etale perfect constancy now provides local perfect constant values.
Represent them by finite-projective complexes in [a,b], using this Tor bound.
The coefficient squares identify each tensor and reduction with the specified
quotient functors. Compose the local coverings. Empty charts use empty covers. -/
theorem residuePerfect_quotient_models_succ
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (_hφ : ∀ n : ℕ, IsIso (φ n)) (_hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (_hab : a ≤ b)
    (_hresidue : FinitePerfectModelsOn X d φ M 0 V a b) (n : ℕ)
    (_hprevious : FinitePerfectModelsOn X d φ M n V a b) :
    FinitePerfectModelsOn X d φ M (n + 1) V a b := by
  obtain ⟨T, hT, hlocal⟩ := finiteQuotient_finiteModule_models_succ X d φ _hφ
    _hcompat M V a b _hab _hresidue n _hprevious
  refine ⟨T, hT, ?_⟩
  intro W g hg
  obtain ⟨P, hPa, hPb, hfinite, ⟨e⟩, hchart⟩ := hlocal W g hg
  have hTor := finiteQuotient_model_torAmplitude X d φ _hφ _hcompat M V a b
    _hresidue (n + 1) W g P hchart ⟨e⟩
  let B := A ⧸ d.ideal ^ (n + 1 + 1)
  let : Finite B := d.quotientFinite (n + 1)
  obtain ⟨⟨E, hEzero, hE, ⟨eE⟩⟩, _, _⟩ :=
    DerivedCategory.exists_bounded_finite_projective_model_of_torAmplitudeIn B P
      ⟨a, b, hPa, hPb, hfinite⟩ a b _hab hTor
  refine ⟨E, (E.isStrictlyGE_iff a).2 (fun i hi ↦ hEzero i (Or.inl hi)),
    (E.isStrictlyLE_iff b).2 (fun i hi ↦ hEzero i (Or.inr hi)), hE, ?_⟩
  have hconstant : (koszulConstantFunctor X B).Additive ∧
      PreservesFiniteLimits (koszulConstantFunctor X B) ∧
      PreservesFiniteColimits (koszulConstantFunctor X B) :=
    commutativeSiteConstantModuleFunctor_exact (ProEt.topology X) (ULift.{t + 1} B)
  have := hconstant.1
  have := hconstant.2.1
  have := hconstant.2.2
  have : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  let F := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
    koszulConstantFunctor X B
  have c : DerivedCategory.Q.obj (finiteModelConstantComplex X B P) ≅
      DerivedCategory.Q.obj (finiteModelConstantComplex X B E) :=
    (F.mapDerivedCategoryFactors.app P).symm ≪≫
      F.mapDerivedCategory.mapIso eE.symm ≪≫ F.mapDerivedCategoryFactors.app E
  let R := completedAdicFiniteRing X d (n + 1)
  let U := (toProEt X).obj W
  exact ⟨e ≪≫ (finitePerfectModelsRestrictionComparison X R U _).symm ≪≫
    (ringedDerivedRestrictionGeneral R U).mapIso
      ((completedAdicDerivedChange X (φ (n + 1))).mapIso c) ≪≫
    finitePerfectModelsRestrictionComparison X R U _⟩

/-- Widening the fixed interval preserves a finite perfect local model.
Source: the interval monotonicity in the definition of `FinitePerfectModelsOn`.
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
This is proved by reusing the same covering, complexes, and restriction
isomorphisms; only the two degree bounds are weakened. -/
private theorem finitePerfectModelsOn_mono (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) (V : X.Etale)
    {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (h : FinitePerfectModelsOn X d φ M n V a b) :
    FinitePerfectModelsOn X d φ M n V a' b' := by
  obtain ⟨T, hT, hlocal⟩ := h
  refine ⟨T, hT, ?_⟩
  intro W g hg
  obtain ⟨P, hPa, hPb, hP, e⟩ := hlocal W g hg
  exact ⟨P, P.isStrictlyGE_of_ge a' a ha,
    P.isStrictlyLE_of_le b b' hb, hP, e⟩

/-- A perfect constant residue model gives uniformly bounded perfect constant models
at all finite levels, on etale refinements. Completeness of M is not assumed.

Source: Stacks Tags 094I and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: keep the given residue covering. Enlarge a possibly empty interval to
[min a b,b]. Further exact slice restriction gives the same residue model on every
smaller chart. This proves the zero-level case. Induct on the quotient level with
the one-step coefficient-filtration theorem, preserving this fixed interval. -/
theorem residuePerfect_finite_quotient_models
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hresidue : ∃ S : Sieve (⊤_ X.Etale), S ∈ X.smallEtaleTopology (⊤_ X.Etale) ∧
      ∀ (V : X.Etale) (f : V ⟶ ⊤_ X.Etale), S f →
        ∃ (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (0 + 1)) (P.X i) ∧
            Module.Finite (A ⧸ d.ideal ^ (0 + 1)) (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V) ((completedAdicQuotientReduction X d 0).obj M) ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V) ((completedAdicDerivedChange X (φ 0)).obj
                  (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    HasUniformFinitePerfectModels X d φ M := by
  obtain ⟨S, hS, hlocal⟩ := hresidue
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hlocal V f hf
  have : P.IsStrictlyGE a := ha
  have hzero' : FinitePerfectModelsOn X d φ M 0 V a b := by
    refine ⟨⊤, X.smallEtaleTopology.top_mem V, ?_⟩
    intro W g _
    refine ⟨P, ha, hb, hP, ?_⟩
    exact finitePerfectModelsRestrictIso_further X (completedAdicFiniteRing X d 0)
      ((toProEt X).map g) _ _ e
  have hzero := finitePerfectModelsOn_mono X d φ M 0 V
    (min_le_left a b) (le_refl b) hzero'
  refine ⟨min a b, b, min_le_right _ _, ?_⟩
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact residuePerfect_quotient_models_succ X d φ hφ hcompat M V
      (min a b) b (min_le_right _ _) hzero n ih

end AlgebraicGeometry.Scheme
