import Langlands.Representation.Families.InducedTwistPersistenceAlgebra
import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Exponents.NestedLeviJacquetExponents
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.LanglandsClassification.LanglandsTripletOppositePieceSeparation
import Langlands.Representation.LanglandsClassification.RegularOppositeLanglandsHead

/-! # The two ends of the persistence argument

* `isGeneralizedEigencharacter_of_leviJacquet_restrict`: an exponent of the split component
  `A_L` on `r^M_Q(π)` restricts, along `A_M → A_L`, to an exponent of `A_M` on an admissible
  `π` (Renard VII.1.1 (ii), published as `normalizedJacquetExponent_restrict`).
* `isGeneralizedEigencharacter_jacquet_of_ne_zero_induction`: Frobenius reciprocity carries an
  exponent of an irreducible `Y` to `r_Q(X)` whenever `X` maps nontrivially to `i_Q(Y)`.
* `exists_injective_oppositeJacquet_of_quotient`: a supplied second adjunction embeds an
  irreducible `τ` into the opposite Jacquet module of every nonzero quotient of `i_P(τ)`.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistPersistence

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

section Ambient

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {H Q L U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

local instance persistenceEndpointsAmbientTopology : TopologicalSpace (rationalPoints H) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints H)] [NonarchimedeanGroup (rationalPoints H)]
  (q : Q ⟶ H) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {A B : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ H} {bL : B.toGrp ⟶ L}

/-- An `A_L`-exponent of `r^H_Q(π)` restricts along `e : A_H(k) → A_L(k)` to an
`A_H`-exponent of the admissible representation `π`. -/
theorem isGeneralizedEigencharacter_of_leviJacquet_restrict (ha : IsSplitComponent a)
    (hbL : IsSplitComponent bL) (e : rationalPoints A.toGrp →* rationalPoints B.toGrp)
    (he : ∀ t, rationalPoints.map (lQ ≫ q) (rationalPoints.map bL (e t)) =
      rationalPoints.map a t)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints H)) (hπ : π.IsAdmissible)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (h : letI := leviPointTopology lQ hlQ
      IsGeneralizedEigencharacter
        (((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj π).representation.comp
          (rationalPoints.map bL)) χ) :
    IsGeneralizedEigencharacter (π.representation.comp (rationalPoints.map a)) (χ.comp e) := by
  have hexp := (isNormalizedJacquetExponent_iff_leviJacquet q lQ rQ hq hlQ hrQ hmulQ hbL π χ).mpr h
  have hgrp := normalizedJacquetExponent_restrict q lQ rQ hq hlQ hrQ hmulQ hbL ha e
    (fun t => he t) π χ hπ hexp
  let := RationalPointFamily.splitComponentPointTopology ha
  exact isGeneralizedEigencharacter_of_isGeneralizedWeight _ _ _ _ hgrp

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- If an admissible `X` maps nontrivially to `i_Q(Y)` with `Y` irreducible, every
`A_L`-exponent of `Y` is an exponent of `r_Q(X)`. -/
theorem isGeneralizedEigencharacter_jacquet_of_ne_zero_induction
    (hH : IsConnectedReductive H) (hbL : IsCentral bL)
    (X : SmoothRep.{0, u, v} ℂ (rationalPoints H)) (hX : X.IsAdmissible)
    (Y : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))
    (hY : letI := leviPointTopology lQ hlQ; Y.IsIrreducible)
    (f : X.representation.IntertwiningMap
      ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj Y).representation) (hf : f ≠ 0)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : letI := leviPointTopology lQ hlQ
      IsGeneralizedEigencharacter (Y.representation.comp (rationalPoints.map bL)) χ) :
    letI := leviPointTopology lQ hlQ
    IsGeneralizedEigencharacter
      (((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj X).representation.comp
        (rationalPoints.map bL)) χ := by
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  obtain ⟨e, -⟩ := leviFrobeniusReciprocity k H hH Q L U q lQ rQ hq hlQ hrQ hmulQ X Y
  have hY' : Y.representation.IsIrreducible := hY
  have hef : e f ≠ 0 := by
    intro h0
    exact hf (e.injective (by rw [h0, map_zero]))
  have hsurj : Function.Surjective (e f) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (e f)).resolve_right hef
  have hJadm' := arbitraryParabolicJacquetAdmissibility k H hH Q L U q lQ rQ hq hlQ hrQ hmulQ
    X hX
  have hJadm : IsAdmissible ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj X).representation :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv q lQ hq hlQ) hJadm'
  have hcen : ∀ t, rationalPoints.map bL t ∈ Subgroup.center (rationalPoints L) :=
    hbL.map_mem_center
  exact InducedTwistExclusion.isGeneralizedEigencharacter_of_surjective (rationalPoints.map bL)
    hcen hJadm Y.isSmooth (e f) hsurj χ hχ

end Ambient

section Start

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M N Pbar Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance persistenceStartAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (pbar : Pbar ⟶ G) (lbar : M ⟶ Pbar) (rbar : Nbar ⟶ Pbar)
  (hpbar : IsParabolicSubgroup pbar) (hlbar : IsRationalLeviSubgroup lbar)
  (hrbar : LeviSubgroup.IsGeometricUnipotentRadical rbar)
  (hmulbar : IsIso (subgroupMultiplication lbar rbar))

/-- The quotient map onto a proper quotient is nonzero. -/
theorem hom_mkQ_ne_zero {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (X : SmoothRep ℂ Γ) (S : Subrepresentation X.representation) (hS : S ≠ ⊤) :
    SmoothRep.hom (SmoothRep.mkQ X S) ≠ 0 := by
  intro h0
  apply hS
  apply Subrepresentation.toSubmodule_injective
  change S.toSubmodule = ⊤
  rw [Submodule.eq_top_iff']
  intro x
  have hx : SmoothRep.hom (SmoothRep.mkQ X S) x = 0 := by rw [h0]; rfl
  exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp hx

/-- Second adjointness embeds an irreducible `τ` into the opposite Jacquet module of every
nonzero quotient of `i_P(τ)`. -/
theorem exists_injective_oppositeJacquet_of_quotient
    (adj : letI := leviPointTopology l hl
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul ⊣
        leviJacquetFunctor.{u, max u v} pbar lbar rbar hpbar hrbar hlbar hmulbar)
    (τ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hτ : letI := leviPointTopology l hl; τ.IsIrreducible)
    (S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation)
    (hS : S ≠ ⊤) :
    letI := leviPointTopology l hl
    ∃ j : τ.representation.IntertwiningMap
        ((leviJacquetFunctor pbar lbar rbar hpbar hrbar hlbar hmulbar).obj
          (SmoothRep.quotient _ S)).representation,
      Function.Injective j := by
  let := leviPointTopology l hl
  obtain ⟨j, hj⟩ := exists_nonzero_oppositeJacquetMap p l r hp hl hr hmul
    pbar lbar rbar hpbar hlbar hrbar hmulbar adj τ (SmoothRep.quotient _ S)
    (SmoothRep.hom (SmoothRep.mkQ _ S)) (hom_mkQ_ne_zero _ S hS)
  have hτ' : τ.representation.IsIrreducible := hτ
  exact ⟨j, (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj⟩

end Start

end Langlands.InducedTwistPersistence
