import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement

/-! # Irreducible cuspidal `L²` summands of `GL_n` from three named analytic inputs

This module reduces `GeneralLinearCuspidalSummandRealizationStatement` (Getz–Hahn,
Theorem 9.7.3, direction from `L²` summands to cuspidal operator realizations) to three
named statements. For a submodule `A` of `L²` of the positive-central rational quotient of
`GL_{r+1}`, `summandForms F r T i A` is the space of stable automorphic functions on
`GL_{r+1}(𝔸_F)` that are cuspidal and whose `L²` class (in the sense of
`IsGeneralLinearFormClass`) lies in `A`. The three inputs are:

* `GeneralLinearSummandFormsEnvelopingStatement`: for a closed invariant subspace `P` of the
  full almost-everywhere cuspidal subspace, the forms attached to `P` are stable under the
  genuine differential action of the universal enveloping algebra;
* `GeneralLinearSummandFormsDenseStatement`: for an irreducible such `P`, the classes of the
  forms attached to `P` are dense in `P`;
* `GeneralLinearSummandFormsIrreducibleStatement`: for an irreducible such `P`, every operator
  realization contained in the forms attached to `P` is zero or all of them.

The reduction proves stability under finite and compact translations, the uniqueness of
`L²` classes, and assembles the realization and the map to `L²`. The three inputs are not
proved here. See the paired Markdown. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance summandReductionGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance summandReductionGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance summandReductionRationalAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance summandReductionContinuousAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance summandReductionFiniteSmoothAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance summandReductionFormsAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _

local instance summandReductionStableAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- The matrix-model continuous function on `GL_n(𝔸_F)` of a stable automorphic function. -/
def stableToContinuous (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    Langlands.Automorphic.StableAutomorphicFunctions F n →ₗ[ℂ]
      Langlands.Automorphic.ContinuousRationalFunctions F n :=
  (Langlands.Automorphic.automorphicToContinuous F n).comp
    (Langlands.Automorphic.stableAutomorphicInclusion F n).toLinearMap

section FormClass

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))

local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i

theorem isGeneralLinearFormClass_zero : IsGeneralLinearFormClass F r T i 0 0 :=
  ⟨0, by rw [map_zero, map_zero], by
    filter_upwards [Lp.coeFn_zero ℂ 2 μQ] with q hq
    rw [hq]
    rfl⟩

variable {F r T i}

theorem IsGeneralLinearFormClass.add {φ ψ : Lp ℂ 2 μQ}
    {f g : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)}
    (hφ : IsGeneralLinearFormClass F r T i φ f) (hψ : IsGeneralLinearFormClass F r T i ψ g) :
    IsGeneralLinearFormClass F r T i (φ + ψ) (f + g) := by
  obtain ⟨h, hf, hh⟩ := hφ
  obtain ⟨k, hg, hk⟩ := hψ
  refine ⟨h + k, by rw [map_add, map_add, hf, hg], ?_⟩
  filter_upwards [Lp.coeFn_add φ ψ, hh, hk] with q hq h1 h2
  rw [hq, Pi.add_apply, h1, h2]
  rfl

theorem IsGeneralLinearFormClass.smul (c : ℂ) {φ : Lp ℂ 2 μQ}
    {f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)}
    (hφ : IsGeneralLinearFormClass F r T i φ f) :
    IsGeneralLinearFormClass F r T i (c • φ) (c • f) := by
  obtain ⟨h, hf, hh⟩ := hφ
  refine ⟨c • h, by rw [map_smul, map_smul, hf], ?_⟩
  filter_upwards [Lp.coeFn_smul c φ, hh] with q hq h1
  rw [hq, Pi.smul_apply, h1]
  rfl

/-- A matrix-model continuous function has at most one `L²` class on the quotient. -/
theorem IsGeneralLinearFormClass.unique {φ ψ : Lp ℂ 2 μQ}
    {f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)}
    (hφ : IsGeneralLinearFormClass F r T i φ f) (hψ : IsGeneralLinearFormClass F r T i ψ f) :
    φ = ψ := by
  obtain ⟨h, hf, hh⟩ := hφ
  obtain ⟨k, hg, hk⟩ := hψ
  have hhk : h = k := positiveQuotientContinuousPullback_injective F _ T i
    ((continuousGeneralLinearEquiv F (r + 1)).injective (hf.trans hg.symm))
  subst hhk
  exact Lp.ext (hh.trans hk.symm)

/-- Right translation of the matrix-model function by the matrix image of `g` corresponds to
right translation of its `L²` class by `g`. -/
theorem IsGeneralLinearFormClass.rightTranslate
    (hInv : QuotientMeasureRightInvariant F GLs T i μQ) (g : AdelicGroupPoints F GLs)
    {φ : Lp ℂ 2 μQ} {f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)}
    (hφ : IsGeneralLinearFormClass F r T i φ f) :
    IsGeneralLinearFormClass F r T i (quotientL2RightTranslate F GLs T i μQ hInv g φ)
      (Langlands.Automorphic.continuousRightAction F (r + 1)
        (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) g) f) := by
  obtain ⟨h, hf, hh⟩ := hφ
  refine ⟨continuousPositiveQuotientRightAction F GLs T i g h, ?_, ?_⟩
  · rw [positiveQuotientContinuousPullback_rightAction, continuousGeneralLinearEquiv_rightAction,
      hf]
  · filter_upwards [coeFn_quotientL2RightTranslate F GLs T i μQ hInv g φ,
      (hInv g).quasiMeasurePreserving.ae_eq_comp hh] with q h1 h2
    rw [h1]
    exact h2

end FormClass

section Forms

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))

local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i

/-- The forms attached to a submodule `A` of `L²` of the positive-central rational quotient of
`GL_{r+1}`: stable automorphic functions whose matrix-model function is cuspidal and has an
`L²` class (`IsGeneralLinearFormClass`) lying in `A`. -/
def summandForms (A : Submodule ℂ (Lp ℂ 2 μQ)) :
    Submodule ℂ (Langlands.Automorphic.StableAutomorphicFunctions F (r + 1)) where
  carrier := {f | Langlands.Automorphic.IsCuspidal F (r + 1) (stableToContinuous F (r + 1) f) ∧
    ∃ φ ∈ A, IsGeneralLinearFormClass F r T i φ (stableToContinuous F (r + 1) f)}
  zero_mem' := by
    refine ⟨?_, 0, A.zero_mem, ?_⟩
    · rw [map_zero]
      exact (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := r + 1)).toSubmodule.zero_mem
    · rw [map_zero]
      exact isGeneralLinearFormClass_zero F r T i
  add_mem' := by
    rintro f g ⟨hfc, φ, hφ, hf⟩ ⟨hgc, ψ, hψ, hg⟩
    refine ⟨?_, φ + ψ, A.add_mem hφ hψ, ?_⟩
    · rw [map_add]
      exact (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := r + 1)).toSubmodule.add_mem
        hfc hgc
    · rw [map_add]
      exact hf.add hg
  smul_mem' := by
    rintro c f ⟨hfc, φ, hφ, hf⟩
    refine ⟨?_, c • φ, A.smul_mem c hφ, ?_⟩
    · rw [map_smul]
      exact (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := r + 1)).toSubmodule.smul_mem
        c hfc
    · rw [map_smul]
      exact hf.smul c

theorem mem_summandForms (A : Submodule ℂ (Lp ℂ 2 μQ))
    (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1)) :
    f ∈ summandForms F r T i A ↔
      Langlands.Automorphic.IsCuspidal F (r + 1) (stableToContinuous F (r + 1) f) ∧
        ∃ φ ∈ A, IsGeneralLinearFormClass F r T i φ (stableToContinuous F (r + 1) f) :=
  Iff.rfl

end Forms

/-- **Differential stability of the forms attached to a closed invariant subspace** (input;
Getz–Hahn, Theorem 9.7.1 with differentiation in `L²`). With the data of
`GeneralLinearCuspidalSummandRealizationStatement`, for every closed subspace `P` of the full
almost-everywhere cuspidal subspace `S` invariant under its right regular action `πc`, the
genuine differential action of every element of the universal enveloping algebra maps the
forms attached to `P` to forms attached to `P`. -/
def GeneralLinearSummandFormsEnvelopingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ P : Submodule ℂ S, IsClosed (P : Set S) → (∀ a, ∀ x ∈ P, πc a x ∈ P) →
      ∀ (u : ArchimedeanGL.EnvelopingAlgebra F (r + 1))
        (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1)),
        f ∈ summandForms F r T i (P.map S.subtype) →
          Langlands.Automorphic.stableAutomorphicEnvelopingAction F (r + 1) u f ∈
            summandForms F r T i (P.map S.subtype)

/-- **Density of the forms attached to an irreducible cuspidal summand** (input; Getz–Hahn,
Lemma 9.7.2). With the data of `GeneralLinearCuspidalSummandRealizationStatement`, for every
nonzero closed `πc`-invariant subspace `P` of `S` with no closed invariant subspaces other than
`0` and itself, every vector of `P` lies in the closure of the set of vectors of `S` that are
the `L²` classes of forms attached to `P`. -/
def GeneralLinearSummandFormsDenseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ P : Submodule ℂ S,
      (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
          (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) →
      ∀ x ∈ P, x ∈ closure {y : S | ∃ f ∈ summandForms F r T i (P.map S.subtype),
        IsGeneralLinearFormClass F r T i (y : Lp ℂ 2 _) (stableToContinuous F (r + 1) f)}

/-- **Algebraic irreducibility of the forms attached to an irreducible cuspidal summand**
(input; Getz–Hahn, Theorems 6.6.2 and 6.6.4 with Lemma 9.7.2). With the data of
`GeneralLinearCuspidalSummandRealizationStatement`, for every nonzero closed `πc`-invariant
subspace `P` of `S` with no closed invariant subspaces other than `0` and itself, every operator
realization contained in the forms attached to `P` is zero or equal to them. -/
def GeneralLinearSummandFormsIrreducibleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ P : Submodule ℂ S,
      (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
          (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) →
      ∀ W : Langlands.Automorphic.OperatorRealization F (r + 1),
        W.toSubmodule ≤ summandForms F r T i (P.map S.subtype) →
          W = ⊥ ∨ W.toSubmodule = summandForms F r T i (P.map S.subtype)

/-- The summand-to-realization direction of Getz–Hahn, Theorem 9.7.3, follows from the three
named inputs. -/
def GeneralLinearCuspidalSummandRealizationReductionStatement : Prop :=
  GeneralLinearSummandFormsEnvelopingStatement.{u} →
    GeneralLinearSummandFormsDenseStatement.{u} →
      GeneralLinearSummandFormsIrreducibleStatement.{u} →
        GeneralLinearCuspidalSummandRealizationStatement.{u}

/-- A nonzero subrepresentation all of whose subrepresentations contained in it are zero or have
the same carrier is irreducible as a representation. -/
theorem subrepresentation_isIrreducible_of {A G W : Type*} [Semiring A] [Monoid G]
    [AddCommMonoid W] [Module A W] {ρ : Representation A G W}
    (R : Subrepresentation ρ) (hne : R ≠ ⊥)
    (hirr : ∀ U : Subrepresentation ρ, U.toSubmodule ≤ R.toSubmodule →
      U = ⊥ ∨ U.toSubmodule = R.toSubmodule) :
    IsSimpleOrder (Subrepresentation R.toRepresentation) := by
  have hmap := Submodule.map_injective_of_injective R.toSubmodule.injective_subtype
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · apply Subrepresentation.ext
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have h1 : (⟨v, hv⟩ : R.toSubmodule) ∈ (⊤ : Subrepresentation R.toRepresentation) := trivial
    rw [← h] at h1
    exact congrArg Subtype.val ((Submodule.mem_bot A).mp h1)
  · let V : Subrepresentation ρ :=
      ⟨U.toSubmodule.map R.toSubmodule.subtype, by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨R.toRepresentation g w, U.apply_mem_toSubmodule g hw, rfl⟩⟩
    have hle : V.toSubmodule ≤ R.toSubmodule := by
      rintro _ ⟨w, -, rfl⟩
      exact w.property
    rcases hirr V hle with h | h
    · left
      have h2 : U.toSubmodule.map R.toSubmodule.subtype = ⊥ :=
        congrArg Subrepresentation.toSubmodule h
      exact Subrepresentation.ext (hmap (h2.trans (Submodule.map_bot _).symm))
    · right
      have h2 : U.toSubmodule.map R.toSubmodule.subtype = R.toSubmodule := h
      exact Subrepresentation.ext (hmap (h2.trans (Submodule.map_subtype_top _).symm))


theorem operatorRealization_isIrreducible_of (F : Type u) [Field F] [NumberField F] {n : ℕ}
    (R : Langlands.Automorphic.OperatorRealization F n) (hne : R ≠ ⊥)
    (hirr : ∀ W : Langlands.Automorphic.OperatorRealization F n,
      W.toSubmodule ≤ R.toSubmodule → W = ⊥ ∨ W.toSubmodule = R.toSubmodule) :
    R.IsIrreducible := by
  have h := subrepresentation_isIrreducible_of R hne hirr
  exact h

section Reduction

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
  (hPD : ParabolicDynamicStatement.{u})
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "hGL" => GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
local notation "SC" => fullAEL2CuspidalSubmodule F GLs hPD hGL T i hi I e hc
local notation "πC" => fullAEL2CuspidalBoundedRightAction F GLs hPD hGL T i hi I e hc

/-- If a right translate of a form attached to a `πc`-invariant subspace is a stable
automorphic function, it is again attached to that subspace. -/
theorem summandForms_rightTranslate (P : Submodule ℂ SC)
    (hP : ∀ a, ∀ x ∈ P, πC a x ∈ P) (x : AdelicGL F (r + 1))
    (f f' : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1))
    (hf' : stableToContinuous F (r + 1) f' =
      Langlands.Automorphic.continuousRightAction F (r + 1) x (stableToContinuous F (r + 1) f))
    (hf : f ∈ summandForms F r T i (P.map (SC).subtype)) :
    f' ∈ summandForms F r T i (P.map (SC).subtype) := by
  obtain ⟨hcusp, φ, hφ, hcl⟩ := hf
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hφ
  obtain ⟨g, rfl⟩ := (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).surjective x
  refine ⟨?_, ((πC g y : SC) : Lp ℂ 2 _), Submodule.mem_map_of_mem (hP g y hy), ?_⟩
  · rw [hf']
    exact (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := r + 1)).apply_mem_toSubmodule
      _ hcusp
  · exact (congrArg (IsGeneralLinearFormClass F r T i _) hf').mpr
      (hcl.rightTranslate (haarQuotientMeasureRightInvariant F GLs T i hi I e hc) g)

/-- With the differential input, the forms attached to a closed invariant subspace are stable
under the whole concrete operator algebra. -/
theorem summandForms_operator_invariant
    (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (P : Submodule ℂ SC) (hPc : IsClosed (P : Set SC)) (hP : ∀ a, ∀ x ∈ P, πC a x ∈ P)
    (a : Langlands.Automorphic.automorphicOperatorAlgebra F (r + 1))
    (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1))
    (hf : f ∈ summandForms F r T i (P.map (SC).subtype)) :
    Langlands.Automorphic.stableAutomorphicAction F (r + 1) a f ∈
      summandForms F r T i (P.map (SC).subtype) := by
  let W := summandForms F r T i (P.map (SC).subtype)
  let V : Submodule ℂ (Langlands.Automorphic.FiniteSmoothRationalFunctions F (r + 1)) :=
    W.map (Langlands.Automorphic.StableAutomorphicFunctions F (r + 1)).subtype
  have hV : ∀ (b : Langlands.Automorphic.automorphicOperatorAlgebra F (r + 1)) g,
      g ∈ V → b.val g ∈ V := by
    refine (Langlands.Automorphic.operator_invariant_iff F (r + 1) V).mpr ⟨?_, ?_, ?_⟩
    · rintro d _ ⟨g, hg, rfl⟩
      exact ⟨Langlands.Automorphic.stableAutomorphicFiniteAction F (r + 1) d g,
        summandForms_rightTranslate F r hPD T i hi I e hc P hP
          (AdelicGL.ofFinite F (r + 1) d) g _ rfl hg, rfl⟩
    · rintro k _ ⟨g, hg, rfl⟩
      exact ⟨Langlands.Automorphic.stableAutomorphicCompactAction F (r + 1) k g,
        summandForms_rightTranslate F r hPD T i hi I e hc P hP
          (AdelicGL.ofInfinite F (r + 1) k.val) g _ rfl hg, rfl⟩
    · rintro u _ ⟨g, hg, rfl⟩
      exact ⟨Langlands.Automorphic.stableAutomorphicEnvelopingAction F (r + 1) u g,
        hLie F r hPD T i hi I e hc P hPc hP u g hg, rfl⟩
  obtain ⟨g, hg, hga⟩ := hV a f.val ⟨f, hf, rfl⟩
  have hgf : g = Langlands.Automorphic.stableAutomorphicAction F (r + 1) a f := Subtype.ext hga
  rw [← hgf]
  exact hg

/-- The operator realization formed by the forms attached to a closed invariant subspace `P`
(given the differential input). -/
def summandRealization (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (P : Submodule ℂ SC) (hPc : IsClosed (P : Set SC)) (hP : ∀ a, ∀ x ∈ P, πC a x ∈ P) :
    Langlands.Automorphic.OperatorRealization F (r + 1) where
  toSubmodule := summandForms F r T i (P.map (SC).subtype)
  apply_mem_toSubmodule a f hf :=
    summandForms_operator_invariant F r hPD T i hi I e hc hLie P hPc hP a f hf

theorem summandRealization_toContinuous (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (P : Submodule ℂ SC) (hPc : IsClosed (P : Set SC)) (hP : ∀ a, ∀ x ∈ P, πC a x ∈ P)
    (f : (summandRealization F r hPD T i hi I e hc hLie P hPc hP).Space) :
    (summandRealization F r hPD T i hi I e hc hLie P hPc hP).toContinuous f =
      stableToContinuous F (r + 1) f.val :=
  rfl

omit [(Measure.haar : Measure (normOneSubgroup F GLs)).IsMulRightInvariant] in
/-- Every form attached to `P` has an `L²` class lying in `P`. -/
theorem exists_summandClass (P : Submodule ℂ SC)
    (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1))
    (hf : f ∈ summandForms F r T i (P.map (SC).subtype)) :
    ∃ y : SC, y ∈ P ∧
      IsGeneralLinearFormClass F r T i (y : Lp ℂ 2 _) (stableToContinuous F (r + 1) f) := by
  obtain ⟨-, φ, hφ, hcl⟩ := hf
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hφ
  exact ⟨y, hy, hcl⟩

/-- The `L²` class in `P` of a form attached to `P`. -/
def summandClass (P : Submodule ℂ SC)
    (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1))
    (hf : f ∈ summandForms F r T i (P.map (SC).subtype)) : SC :=
  Classical.choose (exists_summandClass F r hPD T i hi I e hc P f hf)

omit [(Measure.haar : Measure (normOneSubgroup F GLs)).IsMulRightInvariant] in
theorem summandClass_mem (P : Submodule ℂ SC)
    (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1))
    (hf : f ∈ summandForms F r T i (P.map (SC).subtype)) :
    summandClass F r hPD T i hi I e hc P f hf ∈ P :=
  (Classical.choose_spec (exists_summandClass F r hPD T i hi I e hc P f hf)).1

omit [(Measure.haar : Measure (normOneSubgroup F GLs)).IsMulRightInvariant] in
theorem summandClass_isClass (P : Submodule ℂ SC)
    (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1))
    (hf : f ∈ summandForms F r T i (P.map (SC).subtype)) :
    IsGeneralLinearFormClass F r T i (summandClass F r hPD T i hi I e hc P f hf : Lp ℂ 2 _)
      (stableToContinuous F (r + 1) f) :=
  (Classical.choose_spec (exists_summandClass F r hPD T i hi I e hc P f hf)).2

omit [(Measure.haar : Measure (normOneSubgroup F GLs)).IsMulRightInvariant] in
/-- A vector of `S` which is an `L²` class of a form attached to `P` is its class in `P`. -/
theorem eq_summandClass (P : Submodule ℂ SC)
    (f : Langlands.Automorphic.StableAutomorphicFunctions F (r + 1))
    (hf : f ∈ summandForms F r T i (P.map (SC).subtype)) (y : SC)
    (hy : IsGeneralLinearFormClass F r T i (y : Lp ℂ 2 _) (stableToContinuous F (r + 1) f)) :
    y = summandClass F r hPD T i hi I e hc P f hf :=
  Subtype.ext (hy.unique (summandClass_isClass F r hPD T i hi I e hc P f hf))

/-- The linear map sending a form attached to `P` to its `L²` class in `P`. -/
def summandClassMap (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (P : Submodule ℂ SC) (hPc : IsClosed (P : Set SC)) (hP : ∀ a, ∀ x ∈ P, πC a x ∈ P) :
    (summandRealization F r hPD T i hi I e hc hLie P hPc hP).Space →ₗ[ℂ] SC where
  toFun f := summandClass F r hPD T i hi I e hc P f.val f.property
  map_add' f g := by
    refine (eq_summandClass F r hPD T i hi I e hc P (f + g).val (f + g).property _ ?_).symm
    exact (congrArg (IsGeneralLinearFormClass F r T i _)
      ((stableToContinuous F (r + 1)).map_add f.val g.val)).mpr
      ((summandClass_isClass F r hPD T i hi I e hc P f.val f.property).add
        (summandClass_isClass F r hPD T i hi I e hc P g.val g.property))
  map_smul' c f := by
    refine (eq_summandClass F r hPD T i hi I e hc P (c • f).val (c • f).property _ ?_).symm
    exact (congrArg (IsGeneralLinearFormClass F r T i _)
      ((stableToContinuous F (r + 1)).map_smul c f.val)).mpr
      ((summandClass_isClass F r hPD T i hi I e hc P f.val f.property).smul c)

theorem summandClassMap_isClass (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (P : Submodule ℂ SC) (hPc : IsClosed (P : Set SC)) (hP : ∀ a, ∀ x ∈ P, πC a x ∈ P)
    (f : (summandRealization F r hPD T i hi I e hc hLie P hPc hP).Space) :
    IsGeneralLinearFormClass F r T i
      (summandClassMap F r hPD T i hi I e hc hLie P hPc hP f : Lp ℂ 2 _)
      ((summandRealization F r hPD T i hi I e hc hLie P hPc hP).toContinuous f) :=
  summandClass_isClass F r hPD T i hi I e hc P f.val f.property

theorem range_summandClassMap_le (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (P : Submodule ℂ SC) (hPc : IsClosed (P : Set SC)) (hP : ∀ a, ∀ x ∈ P, πC a x ∈ P) :
    LinearMap.range (summandClassMap F r hPD T i hi I e hc hLie P hPc hP) ≤ P := by
  rintro _ ⟨f, rfl⟩
  exact summandClass_mem F r hPD T i hi I e hc P f.val f.property

/-- With the density input, the classes of the forms attached to an irreducible `P` have
closure `P`. -/
theorem summandClassMap_closure (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (hDense : GeneralLinearSummandFormsDenseStatement.{u})
    (P : Submodule ℂ SC)
    (hPmin : P ≠ ⊥ ∧ IsClosed (P : Set SC) ∧ (∀ a, ∀ x ∈ P, πC a x ∈ P) ∧
      ∀ P' : Submodule ℂ SC, P' ≤ P → IsClosed (P' : Set SC) →
        (∀ a, ∀ x ∈ P', πC a x ∈ P') → P' = ⊥ ∨ P' = P) :
    (LinearMap.range
      (summandClassMap F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1)).topologicalClosure =
        P := by
  refine le_antisymm (Submodule.topologicalClosure_minimal _
    (range_summandClassMap_le F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1) hPmin.2.1) ?_
  intro x hx
  have hd := hDense F r hPD T i hi I e hc P hPmin x hx
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine closure_mono ?_ hd
  rintro y ⟨f, hf, hy⟩
  exact ⟨⟨f, hf⟩, (eq_summandClass F r hPD T i hi I e hc P f hf y hy).symm⟩

/-- With the density input, the realization attached to an irreducible `P` is nonzero. -/
theorem summandRealization_ne_bot (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (hDense : GeneralLinearSummandFormsDenseStatement.{u})
    (P : Submodule ℂ SC)
    (hPmin : P ≠ ⊥ ∧ IsClosed (P : Set SC) ∧ (∀ a, ∀ x ∈ P, πC a x ∈ P) ∧
      ∀ P' : Submodule ℂ SC, P' ≤ P → IsClosed (P' : Set SC) →
        (∀ a, ∀ x ∈ P', πC a x ∈ P') → P' = ⊥ ∨ P' = P) :
    summandRealization F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1 ≠ ⊥ := by
  intro hbot
  have h0 : (summandRealization F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1).toSubmodule =
      ⊥ := congrArg Subrepresentation.toSubmodule hbot
  have hΦ : LinearMap.range
      (summandClassMap F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1) = ⊥ := by
    let Φ := summandClassMap F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1
    refine LinearMap.range_eq_bot.mpr (LinearMap.ext fun f => ?_)
    have hf : f = 0 := Subtype.ext ((Submodule.eq_bot_iff _).mp h0 f.val f.property)
    exact (congrArg Φ hf).trans Φ.map_zero
  have hcl := summandClassMap_closure F r hPD T i hi I e hc hLie hDense P hPmin
  have hPbot : (⊥ : Submodule ℂ SC).topologicalClosure = ⊥ :=
    le_bot_iff.mp (Submodule.topologicalClosure_minimal _ le_rfl (by
      rw [Submodule.bot_coe]
      exact isClosed_singleton))
  exact hPmin.1 (hcl.symm.trans ((congrArg Submodule.topologicalClosure hΦ).trans hPbot))

/-- The assembly: from the three inputs, an irreducible closed invariant subspace `P` is the
closure of the `L²` classes of an irreducible cuspidal operator realization. -/
theorem exists_cuspidalOperatorRealization_of_summand
    (hLie : GeneralLinearSummandFormsEnvelopingStatement.{u})
    (hDense : GeneralLinearSummandFormsDenseStatement.{u})
    (hIrr : GeneralLinearSummandFormsIrreducibleStatement.{u})
    (P : Submodule ℂ SC)
    (hPmin : P ≠ ⊥ ∧ IsClosed (P : Set SC) ∧ (∀ a, ∀ x ∈ P, πC a x ∈ P) ∧
      ∀ P' : Submodule ℂ SC, P' ≤ P → IsClosed (P' : Set SC) →
        (∀ a, ∀ x ∈ P', πC a x ∈ P') → P' = ⊥ ∨ P' = P) :
    ∃ (R : Langlands.Automorphic.CuspidalOperatorRealization F r) (Φ : R.Space →ₗ[ℂ] SC),
      (∀ f : R.Space,
        IsGeneralLinearFormClass F r T i (Φ f : Lp ℂ 2 _) (R.realization.toContinuous f)) ∧
      (LinearMap.range Φ).topologicalClosure = P :=
  ⟨⟨summandRealization F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1,
      operatorRealization_isIrreducible_of F _
        (summandRealization_ne_bot F r hPD T i hi I e hc hLie hDense P hPmin)
        (hIrr F r hPD T i hi I e hc P hPmin),
      (summandRealization F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1).isCuspidal_iff.mpr
        fun f => f.property.1⟩,
    summandClassMap F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1,
    summandClassMap_isClass F r hPD T i hi I e hc hLie P hPmin.2.1 hPmin.2.2.1,
    summandClassMap_closure F r hPD T i hi I e hc hLie hDense P hPmin⟩

end Reduction

/-- **Reduction of Getz–Hahn, Theorem 9.7.3 (summands to realizations)** to the differential,
density and irreducibility inputs. -/
theorem generalLinearCuspidalSummandRealizationReduction :
    GeneralLinearCuspidalSummandRealizationReductionStatement.{u} := by
  intro hLie hDense hIrr F _ _ _ r hPD T i hi _ I _ e hc _ hG S πc P hPmin
  exact exists_cuspidalOperatorRealization_of_summand F r hPD T i hi I e hc hLie hDense hIrr P
    hPmin

end Langlands.Automorphic.GroupSchemeFunctions
