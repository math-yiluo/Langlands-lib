/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueComparison
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceIsoReflects
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The algebraic residue of a finite-quotient constant model

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (094I)
(blueprint: lem-weil-pbc-finite-quotient-model-residue-projective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem residueOverMap_exact (X : Scheme.{t})
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
private def residueRestrictionComparison (X : Scheme.{t})
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
private theorem residueRestrictIso_further (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V)
    (M N : DerivedCategory (SheafOfModules.{t + 1} R))
    (e : ringedSiteDerivedRestrictionOfUniverses R V M ≅
      ringedSiteDerivedRestrictionOfUniverses R V N) :
    Nonempty (ringedSiteDerivedRestrictionOfUniverses R U M ≅
      ringedSiteDerivedRestrictionOfUniverses R U N) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let FV := SheafOfModules.overFunctor.{t + 1} R V
  let FU := SheafOfModules.overFunctor.{t + 1} R U
  have := (residueOverMap_exact X R f).1
  have := (residueOverMap_exact X R f).2.1
  have := (residueOverMap_exact X R f).2.2
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  have := (ringedOverFunctor_exactGeneral R V).1
  have := (ringedOverFunctor_exactGeneral R V).2.1
  have := (ringedOverFunctor_exactGeneral R V).2.2
  have c (K : DerivedCategory (SheafOfModules.{t + 1} R)) :
      F.mapDerivedCategory.obj (ringedSiteDerivedRestrictionOfUniverses R V K) ≅
        ringedSiteDerivedRestrictionOfUniverses R U K :=
    F.mapDerivedCategory.mapIso (residueRestrictionComparison X R V K).symm ≪≫
      (Functor.mapDerivedCategoryCompIso FV F).app K ≪≫
      (Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap R f)).app K ≪≫
      residueRestrictionComparison X R U K
  exact ⟨(c M).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫ c N⟩

/-- On a nonempty chart, the algebraic derived residue of a constant quotient model
has a projective representative in the residue interval. This asserts a model only
AFTER reduction modulo the image of the coefficient ideal, not a Tor bound before reduction.

Source: Stacks Project, sites-cohomology.tex, Tags 094I (lemma-bounded, part (2))
and 094G (lemma-locally-constant); proetale.tex, Tag 09C2.
(blueprint: lem-weil-pbc-finite-quotient-model-residue-projective).

Proof: let B = A/I^(n+1), J be the image of I in B, and identify B/J with A/I.
Scalar extension along B -> B/J has a total left derived functor: take flat K-flat
resolutions and extend scalars termwise, which preserves their quasi-isomorphisms.
Choose a geometric point of the nonempty chart W. Pull the covering sieve in the
residue-model hypothesis back along W -> V and choose a member through that point.
At the chosen geometric stalk, the constant realization of P has algebraic value P,
with the stated universe lift. Exactness of stalks and derived tensor pullback identify
its derived B/J-extension with the stalk of the residue reduction of M: iterate the
quotient compatibility square and use the scalar compatibility square to identify the
coefficient actions. On the chosen covering member, the hypothesis identifies that
residue with a complex of finite projective A/I-modules in [a,b]. Taking its stalk
recovers that algebraic complex. Transport it along B/J = A/I and remove the universe
lift by the module equivalence. The resulting complex E has zero terms outside [a,b],
projective terms, and its localization is the derived residue of Q(P). No nilpotent
lifting, Tor bound for Q(P), or finiteness assumption on P is used in this step. -/
theorem finiteQuotient_model_residueProjective
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (a b : ℤ)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b)
    (n : ℕ) (W : X.Etale) (g : W ⟶ V)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ)
    (hchart : Nonempty W.left)
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    let B := A ⧸ d.ideal ^ (n + 1)
    let J := d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    ∃ (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} (B ⧸ J)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        @Functor.mapHomotopyCategory _ _ _ _ _ _ _
          (ModuleCat.extendScalars (Ideal.Quotient.mk J))
          (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk J)).left_adjoint_additive
          (.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) ∧
      ∃ E : CochainComplex (ModuleCat.{t} (B ⧸ J)) ℤ,
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Projective (B ⧸ J) (E.X i)) ∧
        Nonempty (L.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj E) := by
  classical
  let B := A ⧸ d.ideal ^ (n + 1)
  let J := d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let B₀ := A ⧸ d.ideal ^ (0 + 1)
  let : Algebra B (B ⧸ J) := (Ideal.Quotient.mk J).toAlgebra
  let : (ModuleCat.extendScalars (Ideal.Quotient.mk J)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk J)).left_adjoint_additive
  obtain ⟨L, ε, hL, _⟩ := ModuleCat.exists_baseDerivedExtension_resolution.{t, t, t} B
    (B ⧸ J)
  refine ⟨L, ε, hL, ?_⟩
  let ρ : (B ⧸ J) ≃+* B₀ :=
    (DoubleQuot.quotQuotEquivQuotOfLE
      (Ideal.pow_le_self (Nat.succ_ne_zero n))).trans
      (Ideal.quotEquivOfEq (by simp))
  have hρ : ρ.toRingHom.comp (Ideal.Quotient.mk J) =
      adicQuotientMap d.ideal (n + 1) (0 + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    change (Ideal.quotEquivOfEq (show d.ideal = d.ideal ^ (0 + 1) by simp))
      ((DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (Nat.succ_ne_zero n)))
      (DoubleQuot.quotQuotMk (d.ideal ^ (n + 1)) d.ideal x)) = _
    rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk, Ideal.quotEquivOfEq_mk]
    rfl
  let : RingHomInvPair ρ.toRingHom ρ.symm.toRingHom := RingHomInvPair.of_ringEquiv ρ
  let : RingHomInvPair ρ.symm.toRingHom ρ.toRingHom := RingHomInvPair.of_ringEquiv_symm ρ
  let K := DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P))
  let F := ModuleCat.restrictScalars.{t} ρ.symm.toRingHom
  let G := ModuleCat.restrictScalars.{t} ρ.toRingHom
  let C := (F.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨T, hT, hlocal⟩ := hresidue
  obtain ⟨w⟩ := hchart
  obtain ⟨Z, f, hf, z, _⟩ := (mem_smallEtaleTopology_iff (T.pullback g)).1
    (X.smallEtaleTopology.pullback_stable g hT) w
  obtain ⟨E₀, ha, hb, hproj, ⟨e₀⟩⟩ := hlocal Z (f ≫ g) hf
  obtain ⟨en⟩ := residueRestrictIso_further X (completedAdicFiniteRing X d n)
    ((toProEt X).map f) _ _ e.some
  obtain ⟨ec⟩ := finiteQuotient_model_residueComparison X d φ hφ hcompat M n Z P
    ⟨en⟩ L ε hL ρ hρ
  obtain ⟨ealg⟩ := finiteConstantSlice_iso_reflects X B₀
    (completedAdicFiniteCommRing X d 0) (φ 0) (hφ 0) Z ⟨z⟩ C E₀
    ⟨ec.symm ≪≫ e₀⟩
  let E := (G.mapHomologicalComplex (.up ℤ)).obj E₀
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff] at ha ⊢
    intro i hi
    exact G.map_isZero (ha i hi)
  · rw [CochainComplex.isStrictlyLE_iff] at hb ⊢
    intro i hi
    exact G.map_isZero (hb i hi)
  · intro i
    let := (hproj i).1
    let e₁ : E₀.X i ≃ₛₗ[ρ.symm.toRingHom] E.X i :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change r • x = ρ (ρ.symm r) • x
          rw [ρ.apply_symm_apply] }
    exact Module.Projective.of_equiv (σ' := ρ.toRingHom) e₁
  · let eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t} ρ
    let ret : F ⋙ G ≅ 𝟭 (ModuleCat.{t} (B ⧸ J)) := eqv.counitIso
    let eret : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
        𝟭 (DerivedCategory (ModuleCat.{t} (B ⧸ J))) :=
      Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso ret ≪≫ Functor.mapDerivedCategoryIdIso _
    exact ⟨(DerivedCategory.Q.objObjPreimageIso _).symm ≪≫
      (eret.app (DerivedCategory.Q.obj K)).symm ≪≫
      G.mapDerivedCategory.mapIso
        (F.mapDerivedCategoryFactors.app K ≪≫ ealg) ≪≫
      G.mapDerivedCategoryFactors.app E₀⟩

end AlgebraicGeometry.Scheme
