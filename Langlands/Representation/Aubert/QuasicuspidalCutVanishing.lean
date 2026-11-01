import Langlands.Representation.CuspidalSupport.QuasicuspidalJacquetBlockBound
import Langlands.Representation.Aubert.CutEulerExpansion

/-! Actual upper cut-degree vanishing for subquotients of quasicuspidal induction. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open CategoryTheory GeneralLinear SmoothRep CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n)

/-- Every actual cut-degree carrier above the source support degree is zero. -/
def DegreesVanishAboveSupport :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) → Prop :=
  letI := T.topology
  fun π => ∀ k, B.length - 1 < k →
    Subsingleton ((diagram T π.representation).Degree k)

/-- A zero actual Jacquet coefficient carrier makes its actual induced cut
term zero. -/
theorem term_subsingleton_of_jacquet (s : Finset (Fin (n - 1))) :
    letI := T.topology
    ∀ π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
      Subsingleton ((T.normalizedJacquetFunctor (shape s)).obj π) →
      Subsingleton (Term T π.representation s) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hJ
  let : Subsingleton ((shape s).JacquetModule π.representation) := hJ
  change Subsingleton (Induction.SmoothFunctions _ _)
  infer_instance

/-- The source Jacquet block bound makes every coordinate of each higher
actual cut degree zero. -/
theorem degreesVanishAboveSupport_of_jacquetBlockBound (hn : 0 < n) :
    letI := T.topology
    ∀ π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
      HasJacquetBlockBound F T B π → DegreesVanishAboveSupport F T B π := by
  let := T.topology
  intro π hbound k hk
  have hB : 0 < B.length := length_pos_of_pos B hn
  have hterm (s : {s : Finset (Fin (n - 1)) // s.card = k}) :
      Subsingleton (Term T π.representation s.1) := by
    apply term_subsingleton_of_jacquet F T s.1 π
    apply hbound
    rw [shape_length s.1 hn, s.property]
    omega
  let := hterm
  exact inferInstanceAs (Subsingleton (∀ s : {s : Finset (Fin (n - 1)) // s.card = k},
    Term T π.representation s.1))

/-- Every actual subquotient of quasicuspidal induction has no actual cut
degrees above the common support degree. -/
theorem quasicuspidal_degreesVanishAboveSupport (hn : 0 < n) :
    letI := T.topology
    ∀ σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B σ.representation →
      ∀ π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
        IsSubquotient π ((T.normalizedParabolicInductionFunctor B).obj σ) →
        DegreesVanishAboveSupport F T B π := by
  let := T.topology
  intro σ hqc π hπ
  exact degreesVanishAboveSupport_of_jacquetBlockBound F T B hn π
    (quasicuspidal_subquotient_hasJacquetBlockBound F T B σ hqc π hπ)

/-- Every Jacquet carrier of a higher zero actual cut degree is zero. -/
theorem jacquet_degree_subsingleton_of_aboveSupport (C : BlockShape n) :
    letI := T.topology
    ∀ π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
      DegreesVanishAboveSupport F T B π →
      ∀ k, B.length - 1 < k →
        Subsingleton (C.JacquetModule (degreeObject T π.representation k).representation) := by
  let := T.topology
  intro π hzero k hk
  let : Subsingleton (degreeObject T π.representation k).obj := hzero k hk
  exact (C.jacquetMk_surjective (degreeObject T π.representation k).representation).subsingleton

end Langlands.Aubert.ActualCutComplex
