/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralTransport
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.ContinuousLisseStratifiedLattices
import Mathlib.Algebra.Field.ULift

/-! # Integral models on a locally finitely presented stratum

Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- A locally finitely presented rational module on one immersed stratum admits an
ordinary constructible integral model, with both coefficient rings pulled back from X.
Source: Hemo--Richarz--Scholbach, Example 3.1 (local triviality), and Bhatt--Scholze,
Lemma 6.8.13, with the coefficient restriction identification of Lemma 6.8.2.
(auxiliary; not a blueprint node)

Proof in words. An immersion identifies Y with a locally closed subspace of X, so Y
is topologically noetherian. Identify the two pulled-back coefficient rings and their
map with the continuous integral and rational coefficient rings on Y. A finite local
presentation over the rational ring is locally finite free: realize a presentation
matrix as continuous E-valued functions, refine by its locally constant rank, and use
an invertible maximal minor to identify its cokernel with a finite free module.
For this lisse module, the first paragraph of Lemma 6.8.13 gives lattices on a finite
refinement. More explicitly, Proposition 6.8.4(6) first gives lattices on an etale cover.
Take a finite affine subcover and stratify so its maps become finite etale. Etale
locally split each finite etale cover into sheets. View the finitely many supplied
lattices in the same rational module and take their sum; it is a finite free full
lattice over the valuation ring. The sum is invariant under permutations of the
sheets, and continuous transition maps preserve its locally constant lattice class,
so it descends. The resulting lisse integral module is locally finitely presented,
and the singleton identity stratification makes it constructible.
Apply the separate gluing theorem to these supplied models on the finite refinement,
and transport the result back across the coefficient identifications. For the zero
module and the empty stratum use zero. No derived comparison or bounded-complex
packaging is part of this statement. -/
theorem continuousConstructible_integral_stratum (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] {Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i]
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hF : ProEtale.IsLocallyFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)),
      ProEtale.IsConstructibleModuleObject
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)) N ∧
      Nonempty ((Mod.extendScalars
        ((ProEtale.upperStar Ab.{u + 1} i).map
          (coefficientMap (integralScalarMap ℓ E) X))).obj N ≅ F) := by
  let : TopologicalSpace.NoetherianSpace Y := i.isEmbedding.isInducing.noetherianSpace
  obtain ⟨D⟩ : Nonempty (PullbackCoefficientData ℓ E i) :=
    ⟨pullbackCoefficientData ℓ E i⟩
  obtain ⟨ai, bi, hai, hbi, iai, ibi, wi, _⟩ := D
  let : IsMonHom ai := hai
  let : IsMonHom bi := hbi
  let : IsIso ai := iai
  let : IsIso bi := ibi
  obtain ⟨P, hP, ⟨eP⟩⟩ : ∃ P : Mod _
      (condensedRingObj (Profinite.continuousMapRingObj E) Y),
      ProEtale.IsLocallyFinitelyPresented _ P ∧
        Nonempty (P ≅ (Mod.comap (inv bi)).obj F) :=
    ⟨(Mod.comap (inv bi)).obj F, ProEtale.lfp_comap (inv bi) hF, ⟨Iso.refl _⟩⟩
  obtain ⟨C, hC⟩ := smallField_finiteFree_cover ℓ E Y P hP
  obtain ⟨S, hS⟩ := continuousLisse_stratified_lattices ℓ E Y P ⟨C, hC⟩
  have hmodels : ∀ s : Fin S.n,
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).obj
            (condensedRingObj (integralCoeff ℓ E) Y)),
        ProEtale.IsConstructibleModuleObject
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).obj
            (condensedRingObj (integralCoeff ℓ E) Y)) M ∧
        Nonempty ((Mod.extendScalars
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).map
            (coefficientMap (integralScalarMap ℓ E) Y))).obj M ≅
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion s)).mapMod _).obj P) := fun s ↦ by
    obtain ⟨M, hM, ⟨e⟩⟩ := hS s
    exact pullbackCoefficient_model (integralCoeff ℓ E)
      (Profinite.continuousMapRingObj E) (integralScalarMap ℓ E)
      (X := Y) (Y := S.domain s) (S.immersion s) P M hM.isConstructibleModuleObject e
  obtain ⟨N, hN, ⟨e⟩⟩ := continuousConstructible_integral_gluing ℓ E Y P S hmodels
  exact model_transport (X := Y)
    (R := (ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X))
    (S := (ProEtale.upperStar Ab.{u + 1} i).obj
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (R' := condensedRingObj (integralCoeff ℓ E) Y)
    (S' := condensedRingObj (Profinite.continuousMapRingObj E) Y)
    ((ProEtale.upperStar Ab.{u + 1} i).map (coefficientMap (integralScalarMap ℓ E) X))
    (coefficientMap (integralScalarMap ℓ E) Y)
    ai bi wi F N hN (e ≪≫ eP)

end AlgebraicGeometry.ProEtale.CondensedRing
