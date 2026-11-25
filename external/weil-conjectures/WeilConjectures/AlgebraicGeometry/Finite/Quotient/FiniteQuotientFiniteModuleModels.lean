/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientFiniteModuleCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleBoundedModels

/-! # Finite-module models after one coefficient extension

Source: Stacks Tags 09C2, 094I and 094G
(blueprint: lem-weil-pbc-finite-quotient-finite-module-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The empty-cover sheaf axiom makes every module on an empty slice zero. -/
private theorem finiteModels_emptySlice_module_isZero (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (W : X.Etale) [IsEmpty W.left]
    (N : SheafOfModules.{t + 1} (R.over ((toProEt X).obj W))) : IsZero N := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf.{t + 1} (R.over ((toProEt X).obj W))).map_injective
  ext T x
  have : IsEmpty T.unop.left.left :=
    ⟨fun z ↦ isEmptyElim (show W.left from T.unop.hom.left z)⟩
  have hbot : (⊥ : Sieve T.unop) ∈
      ((ProEt.topology X).over ((toProEt X).obj W)) T.unop := by
    rw [GrothendieckTopology.mem_over_iff, map_bot]
    exact ProEt.bot_mem_topology T.unop.left
  let F := (SheafOfModules.toSheaf.{t + 1} (R.over ((toProEt X).obj W))).obj N
  exact ConcreteCategory.congr_hom
    ((F.isTerminalOfBotCover T.unop hbot).isZero.eq_of_src (𝟙 _) 0) x

/-- Derived localization preserves the zero category on an empty slice. -/
private theorem finiteModels_emptySlice_derived_isZero (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (W : X.Etale) [IsEmpty W.left]
    (K : DerivedCategory (SheafOfModules.{t + 1} (R.over ((toProEt X).obj W)))) :
    IsZero K := by
  have hC : IsZero (DerivedCategory.Q.objPreimage K) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro i
    exact (finiteModels_emptySlice_module_isZero X R W _).eq_of_src _ _
  exact (DerivedCategory.Q.map_isZero hC).of_iso
    (DerivedCategory.Q.objObjPreimageIso K).symm

/-- The coefficient-filtration step gives bounded constant finite-module models.
It does not assert projectivity of their terms or finite Tor amplitude.

Source: Stacks Project, proetale.tex, lemma-describe-constructible-complexes (09C2),
sites-cohomology.tex, lemma-bounded (094I) and lemma-locally-constant (094G).
(blueprint: lem-weil-pbc-finite-quotient-finite-module-models).

Proof: intersect the residue and previous-level trivializing covers. On a flat-term
K-flat representative tensor the exact coefficient sequence with kernel
I^(n+1)/I^(n+2). Balancing identifies the kernel term with the residue model tensored
with this finite A/I-module. Both outer terms have finite locally constant cohomology
in [a,b]. Their long exact sequence and the weak Serre property over the finite
Noetherian coefficient ring give the same property for the middle term. The specified
coefficient squares identify it with the actual next quotient reduction. Finite-ring
constructible derived origin descends this bounded object to the etale site; full
faithfulness identifies its cohomology with the already obtained finite local systems.
Local bounded constant-model descent (094G) supplies
finite-module complexes in [a,b], including their differentials. Compose the covering
sieves. A nonempty chart satisfies the first alternative in the last conjunct. On an
empty chart the localized sheaf category is zero, so choose the zero algebraic complex
and its unique restriction isomorphism; it satisfies the second alternative. -/
theorem finiteQuotient_finiteModule_models_succ
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b) (n : ℕ)
    (hprevious : FinitePerfectModelsOn X d φ M n V a b) :
    ∃ T : Sieve V, T ∈ X.smallEtaleTopology V ∧
      ∀ (W : X.Etale) (g : W ⟶ V), T g →
        ∃ P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1 + 1))) ℤ,
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Finite (A ⧸ d.ideal ^ (n + 1 + 1)) (P.X i)) ∧
          Nonempty
          (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d (n + 1))
              ((toProEt X).obj W) ((completedAdicQuotientReduction X d (n + 1)).obj M) ≅
            ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d (n + 1))
              ((toProEt X).obj W) ((completedAdicDerivedChange X (φ (n + 1))).obj
                (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P)))) ∧
          (Nonempty W.left ∨ IsZero P) := by
  classical
  let B := A ⧸ d.ideal ^ (n + 1 + 1)
  let : Finite B := d.quotientFinite (n + 1)
  obtain ⟨hvan, hloc⟩ := finiteQuotient_finiteModule_cohomology_succ
    X d φ hφ hcompat M V a b hab hresidue n hprevious
  obtain ⟨T, hT, hmodels⟩ := finiteCoefficient_etale_bounded_models
    X B (completedAdicFiniteCommRing X d (n + 1)) (φ (n + 1)) (hφ (n + 1))
    ((completedAdicQuotientReduction X d (n + 1)).obj M) V a b hab hvan hloc
  refine ⟨T, hT, ?_⟩
  intro W g hg
  by_cases hW : Nonempty W.left
  · obtain ⟨P, hPa, hPb, hfinite, e⟩ := hmodels W g hg hW
    exact ⟨P, hPa, hPb, hfinite, e, Or.inl hW⟩
  · let : IsEmpty W.left := not_nonempty_iff.mp hW
    let P : CochainComplex (ModuleCat.{t} B) ℤ := HomologicalComplex.zero
    have hP : IsZero P := HomologicalComplex.isZero_zero
    refine ⟨P, ?_, ?_, ?_, ?_, Or.inr hP⟩
    · exact (P.isStrictlyGE_iff a).2 fun i _ ↦
        (HomologicalComplex.eval _ _ i).map_isZero hP
    · exact (P.isStrictlyLE_iff b).2 fun i _ ↦
        (HomologicalComplex.eval _ _ i).map_isZero hP
    · intro i
      have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.eval _ _ i).map_isZero hP)
      exact Module.Finite.of_finite
    · exact ⟨(finiteModels_emptySlice_derived_isZero X
        (completedAdicFiniteRing X d (n + 1)) W _).iso
          (finiteModels_emptySlice_derived_isZero X
            (completedAdicFiniteRing X d (n + 1)) W _)⟩

end AlgebraicGeometry.Scheme
