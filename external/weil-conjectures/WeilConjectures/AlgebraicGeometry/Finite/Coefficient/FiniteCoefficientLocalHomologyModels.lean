/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Finite homology and bounds from algebraic local models

Source: Stacks Project, Tags 094H and 094I.
(blueprint: lem-weil-pbc-finite-coefficient-local-homology-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Ordinary constant realization, with the prescribed coefficient identification.
Source: Stacks Project, Tags 03CY and 094H.
(blueprint: def-weil-pbc-finite-coefficient-local-homology-models). -/
def finiteCoefficientConstantFunctor (X : Scheme.{t}) (B : Type t) [CommRing B]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R) :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
    koszulConstantFunctor X B ⋙ completedAdicChange X φ

/-- Local algebraic complexes compute the homology, with finite terms and a fixed support.
This asks for algebraic complexes, not for finite homology modules. In particular,
finiteness of homology and descent of the bounds remain separate consequences.
Source: Stacks Project, Tags 094H and 094I.
(blueprint: def-weil-pbc-finite-coefficient-local-homology-models). -/
def FiniteCoefficientLocalHomologyModels (X : Scheme.{t}) (B : Type t) [CommRing B]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R)
    (K : DerivedCategory (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)))
    (V : X.Etale) (a b : ℤ) : Prop :=
  ∀ (W : X.Etale) (_g : W ⟶ V),
    ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
      ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
        ∃ P : CochainComplex (ModuleCat.{t} B) ℤ,
          (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
          (∀ q : ℤ, Module.Finite B (P.X q)) ∧
          ∀ q : ℤ, Nonempty
            ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
                ((DerivedCategory.homologyFunctor _ q).obj K) ≅
              (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
                ((finiteCoefficientConstantFunctor X B φ).obj (P.homology q)))

private theorem isZero_of_etale_cover (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1})
    (F : SheafOfModules.{t + 1} R) (V : X.Etale)
    (S : Sieve V) (hS : S ∈ X.smallEtaleTopology V)
    (hz : ∀ (Z : X.Etale) (g : Z ⟶ V), S g →
      IsZero ((SheafOfModules.overFunctor R ((toProEt X).obj Z)).obj F)) :
    IsZero ((SheafOfModules.overFunctor R ((toProEt X).obj V)).obj F) := by
  have hcover : S.functorPushforward (toProEt X) ∈
      ProEt.topology X ((toProEt X).obj V) :=
    (CoverPreserving.of_isContinuous (toProEt X) X.smallEtaleTopology
      (ProEt.topology X)).cover_preserve hS
  apply (IsZero.iff_id_eq_zero _).mpr
  ext U x
  apply F.isSheaf.isSeparated U.unop.left
    ((S.functorPushforward (toProEt X)).pullback U.unop.hom)
    ((ProEt.topology X).pullback_stable U.unop.hom hcover)
  intro Y f hf
  obtain ⟨Z, g, k, hg, _⟩ := hf
  have he := congrArg
    (fun h : F.over ((toProEt X).obj Z) ⟶ F.over ((toProEt X).obj Z) ↦
      h.val.app (op (Over.mk k)) (F.val.map f.op x))
    ((hz Z g hg).eq_of_src (𝟙 _) 0)
  change F.val.map f.op x = 0 at he
  change F.val.map f.op x = F.val.map f.op 0
  rw [map_zero]
  exact he

private theorem finite_homology (B : Type t) [CommRing B] [Finite B]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (hf : ∀ q : ℤ, Module.Finite B (P.X q)) (q : ℤ) :
    Module.Finite B (P.homology q) := by
  have : Module.Finite B (P.X q) := hf q
  have : Finite (P.X q) := Module.finite_of_finite B
  have : Finite (P.cycles q) := Finite.of_injective (P.iCycles q)
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Finite (P.homology q) := Finite.of_surjective (P.homologyπ q)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  exact Module.Finite.of_finite

/-- Finite bounded algebraic local models give bounded finite local cohomology.
Source: Stacks Project, Tags 094H and 094I.
(blueprint: lem-weil-pbc-finite-coefficient-local-homology-models).

Proof: The cycles inject into the finite degree-q module, and homology is their
quotient; hence homology is finite. Outside the support the degree-q term is zero,
so its homology and its constant realization are zero. An etale covering sieve
pushes forward to a pro-etale covering sieve. Pull it back over each object of the
slice over V and use sheaf separatedness to descend the vanishing. The local
homology comparison on each chart gives the required finite constant model. This
argument also handles an empty covering sieve and the zero coefficient ring. -/
theorem finiteCoefficient_local_homology_models
    (X : Scheme.{t}) (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R)
    (K : DerivedCategory (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)))
    (V : X.Etale) (a b : ℤ)
    (h : FiniteCoefficientLocalHomologyModels X B φ K V a b) :
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((SheafOfModules.overFunctor _ ((toProEt X).obj V)).obj
        ((DerivedCategory.homologyFunctor _ q).obj K))) ∧
    DerivedCategory.homologyProperty
      (fun F ↦ ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
                  ((finiteCoefficientConstantFunctor X B φ).obj N))) K := by
  have : (finiteCoefficientConstantFunctor X B φ).PreservesZeroMorphisms := by
    unfold finiteCoefficientConstantFunctor
    infer_instance
  constructor
  · intro q hq
    obtain ⟨S, hS, hmodel⟩ := h V (𝟙 V)
    apply isZero_of_etale_cover X _ _ V S hS
    intro Z g hg
    obtain ⟨P, hb, _, he⟩ := hmodel Z g hg
    obtain ⟨e⟩ := he q
    have : (SheafOfModules.overFunctor.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
        ((toProEt X).obj Z)).PreservesZeroMorphisms :=
      module_overFunctor_preservesZero _ _
    have hz : IsZero (P.homology q) :=
      (P.sc q).isZero_homology_of_isZero_X₂ (hb q hq)
    exact ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).map_isZero
      ((finiteCoefficientConstantFunctor X B φ).map_isZero hz)).of_iso e
  · intro q W g
    obtain ⟨S, hS, hmodel⟩ := h W g
    refine ⟨S, hS, ?_⟩
    intro Z f hf
    obtain ⟨P, _, hfin, he⟩ := hmodel Z f hf
    exact ⟨P.homology q, finite_homology B P hfin q, he q⟩

end AlgebraicGeometry.Scheme
