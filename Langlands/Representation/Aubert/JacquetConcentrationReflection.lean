import Langlands.Representation.Aubert.QuasicuspidalCutSupport
import Langlands.Representation.Aubert.CutTerminalEffectivity

/-! Reflecting actual Jacquet concentration to the actual cut complex. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open CategoryTheory GeneralLinear SmoothRep CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ}

/-- The actual Jacquet maps are exact before `m`, and their degree carriers
vanish above `m`, at every shape in the chosen family. -/
def JacquetConcentratedAt (P : BlockShape n → Prop) :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) → ℕ → Prop :=
  letI := T.topology
  fun A m =>
    (0 < m → ∀ C, P C →
      Function.Injective
        (T.normalizedJacquetMap C (hom (degreeMorphism T A.representation 0)))) ∧
    (∀ i, i + 1 < m → ∀ C, P C →
      LinearMap.range
          (T.normalizedJacquetMap C (hom (degreeMorphism T A.representation i))).toLinearMap =
        LinearMap.ker
          (T.normalizedJacquetMap C
            (hom (degreeMorphism T A.representation (i + 1)))).toLinearMap) ∧
    (∀ k, m < k → ∀ C, P C →
      Subsingleton (C.JacquetModule (degreeObject T A.representation k).representation))

/-- Degreewise all-subquotient detection reflects the explicit actual
Jacquet concentration conditions. -/
theorem concentratedAt_of_jacquet (P : BlockShape n → Prop) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (m : ℕ),
      (∀ k, JacquetReflection.DetectsSubquotients.{uF,max uF uV} F T P
        (degreeObject T A.representation k)) →
      JacquetConcentratedAt F T P A m → ConcentratedAt F T A m := by
  let := T.topology
  intro A m hdet hJ
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    exact JacquetReflection.injective_of_jacquet F T P
      (degreeMorphism T A.representation 0) (hdet 0) (hJ.1 hm)
  · intro i hi
    exact JacquetReflection.exact_of_jacquet F T P
      (degreeMorphism T A.representation i)
      (degreeMorphism T A.representation (i + 1))
      (differential_square T A.representation i)
      (hdet (i + 1)) (hJ.2.1 i hi)
  · intro k hk
    have hself : IsSubquotient (degreeObject T A.representation k)
        (degreeObject T A.representation k) :=
      IsSubrepresentation.isSubquotient
        ⟨𝟙 (degreeObject T A.representation k), fun _ _ h => h⟩
    exact JacquetReflection.subsingleton_of_vanishing F T P
      (hdet k) hself (hJ.2.2 k hk)

/-- The proved constituent-support detector makes associated-Levi Jacquet
concentration sufficient for actual quasicuspidal cut concentration. -/
theorem concentratedAt_of_associatedJacquet (B : BlockShape n) (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (_hπ : π.HasFiniteLength),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        ∀ m, JacquetConcentratedAt F T (LevisAssociated (F := F.Carrier) B) π m →
          ConcentratedAt F T π m := by
  let := T.topology
  intro σ hσ hqc π hπ hsub m hJ
  exact concentratedAt_of_jacquet F T (LevisAssociated (F := F.Carrier) B) π m
    (QuasicuspidalCutSupport.degreesDetected F T B hn σ hσ hqc π hπ hsub) hJ

/-- Associated-Levi Jacquet concentration at the support degree gives the
prescribed common-sign effectivity in the actual irreducible lattice. -/
theorem effective_of_associatedJacquet (B : BlockShape n) (hn : 0 < n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier))
      (_hσ : σ.HasFiniteLength), IsLeviQuasicuspidal B σ.representation →
      ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπ : π.HasFiniteLength),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        JacquetConcentratedAt F T (LevisAssociated (F := F.Carrier) B) π (B.length - 1) →
        IrreducibleGrothendieckProof.factorMap
          (((-1 : ℤ) ^ (n - B.length)) • alternatingOperator.{uF,uV} F T n
            (GeneralLinear.finiteLengthClass n F.Carrier π hπ)) ∈
          VirtualRepresentation.effective := by
  let := T.topology
  intro σ hσ hqc π hπ hsub hJ
  have hcon := concentratedAt_of_associatedJacquet F T B hn σ hσ hqc π hπ hsub
    (B.length - 1) hJ
  have hB : 0 < B.length := length_pos_of_pos B hn
  have hm : B.length - 1 + 1 = B.length := Nat.sub_add_cancel hB
  have hle : B.length - 1 + 1 ≤ n := by rw [hm]; exact B.length_le
  simpa only [hm] using
    effective_of_concentration.{uF,uV} F T (B.length - 1) hle π hπ hcon

end Langlands.Aubert.ActualCutComplex
