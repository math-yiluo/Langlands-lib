import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Representation.Parabolic.InductionFactorMatchingStatement
import Langlands.Representation.Parabolic.InductionFactorMatchingProof

/-!
# All-field port of `Langlands.Representation.Parabolic.InductionFactorMatchingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.InductionFactorMatchingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uK uG uV uW uX

open _root_.Langlands.LengthCriterionProof (quotientRep lower)
variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.FactorMatchingProof
open Langlands.FactorMatchingProof
universe uK uG uV uW

open _root_.Langlands.LengthCriterionProof (quotientRep lower)
variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

end Langlands.AllFieldBZ.FactorMatchingProof
namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uK uG uV uX

open _root_.Langlands.LengthCriterionProof (quotientRep lower)
variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {V : Type uV} {X : Type uX}
  [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedInducedSurjectivity NormalizedInductionFactorMatchingTheorem NormalizedInductionOutputFiniteLength NormalizedInductionOutputMatching NormalizedInductionSourceMatching nonempty_valueQuotient_equiv_induced normalizedInducedSurjectivity_of_smoothInductionSurjectivity normalizedInductionFactorMatchingTheorem normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity normalizedInductionObject normalizedInductionOutputMatching_of_surjectivity
open Langlands.GeneralLinear
open _root_.Langlands.LengthCriterionProof (quotientRep lower)
universe uF uV uW uX

section Surjectivity
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Right exactness of normalized parabolic induction for given carrier
universes: the induced map of a surjective intertwiner of smooth Levi
representations is surjective. -/
def NormalizedInducedSurjectivity.{uA, uB} : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (Y : Type uA) [AddCommGroup Y] [Module ℂ Y] (Z : Type uB) [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (B.Levi F.Carrier) Y) (σ : Representation ℂ (B.Levi F.Carrier) Z)
    (f : ρ.IntertwiningMap σ), IsSmooth ρ → IsSmooth σ → Function.Surjective f →
      Function.Surjective (T.normalizedParabolicInducedMap B f)

/-- Generic surjectivity of smooth induction from a closed subgroup gives right
exactness of normalized parabolic induction: compact open subgroups of the
actual general linear group are cofinal, the standard block parabolic is
closed, and inflation and twisting by the half modulus preserve smoothness. -/
theorem normalizedInducedSurjectivity_of_smoothInductionSurjectivity.{uA, uB}
    (h : Induction.SmoothInductionSurjectivityStatement.{uF, uA, uB}) :
    NormalizedInducedSurjectivity.{uF, uA, uB} T B := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  intro Y _ _ Z _ _ ρ σ f hρ hσ hf
  refine h (GeneralLinear n F.Carrier) ?_ (B.parabolic F.Carrier)
    (B.isClosed_parabolic F.Carrier) Y Z _ _ ?_ ?_ _ hf
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).2
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous hρ)
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).2
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous hσ)

end Surjectivity
section Matching
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- For a filtration `s` of a smooth Levi representation `σ`, the successive
quotient of the functions with values in two consecutive steps is the
normalized induction of any smooth representation equivalent to the graded
piece, provided normalized induction preserves surjectivity. -/
theorem nonempty_valueQuotient_equiv_induced (σ : Representation ℂ (B.Levi F.Carrier) V)
    {m : ℕ} (s : ObjectRepFiltration (Rep.of σ) m) (i : Fin m)
    (π : Representation ℂ (B.Levi F.Carrier) X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    NormalizedInducedSurjectivity.{uF, uV, uX} T B → IsSmooth σ → IsSmooth π →
      (s.gradedRepresentation i).ρ.Equiv π →
      Nonempty ((quotientRep
        (Induction.valueSubrep (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
          (s.subrepresentation i.castSucc).toSubmodule)
        (Induction.valueSubrep (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
          (s.subrepresentation i.succ).toSubmodule)).Equiv
        (T.normalizedParabolicInduced B π)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hsurj hσ hπ φ
  have hstep : IsSmooth (s.subrepresentation i.succ).toRepresentation :=
    isSmooth_of_injective (FactorMatchingProof.subrepInclusion _) Subtype.val_injective hσ
  let ψ : (s.subrepresentation i.succ).toRepresentation.IntertwiningMap π :=
    φ.toIntertwiningMap.comp (s.gradedProjection i).hom
  have hψ : Function.Surjective ψ :=
    (EquivLike.surjective φ).comp (s.gradedProjection_surjective i)
  refine Induction.nonempty_valueQuotient_equiv (B.parabolic F.Carrier) _
    (twist (T.parabolicHalfModulus B)
      ((s.subrepresentation i.succ).toRepresentation.comp (B.leviProjection F.Carrier)))
    (fun _ _ => rfl) (T.normalizedParabolicInducedMap B ψ) (hsurj _ _ _ _ ψ hstep hπ hψ) ?_
  intro f
  rw [Induction.smoothFunctions_eq_zero_iff]
  refine forall_congr' fun x => ?_
  change φ ((s.gradedProjection i).hom _) = 0 ↔ _
  rw [EmbeddingLike.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- Normalized parabolic induction preserves matching of actual Jordan–Hölder
factors when the first induced output has finite length, provided normalized
induction preserves surjectivity at the needed carrier universes. -/
theorem normalizedInductionOutputMatching_of_surjectivity
    (hVW : NormalizedInducedSurjectivity.{uF, uV, uW} T B)
    (hWW : NormalizedInducedSurjectivity.{uF, uW, uW} T B) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier)),
      NormalizedInductionSourceMatching T B σ τ →
      NormalizedInductionOutputFiniteLength T B σ →
      NormalizedInductionOutputMatching T B σ τ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro σ τ hsrc hfin
  obtain ⟨m, s, t, -, -, e, he⟩ := hsrc
  have hτ (j : Fin m) : IsSmooth (t.gradedRepresentation j).ρ :=
    isSmooth_of_surjective (t.gradedProjection j).hom (t.gradedProjection_surjective j)
      (isSmooth_of_injective (FactorMatchingProof.subrepInclusion _) Subtype.val_injective
        τ.isSmooth)
  let Sσ : ObjectRepFiltration (normalizedInductionObject T B σ) m :=
    Induction.valueFiltration (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (σ.representation.comp (B.leviProjection F.Carrier)))
      (fun i => (s.subrepresentation i).toSubmodule)
      (fun _ _ h => s.monotone_subrepresentation h)
      (congrArg Subrepresentation.toSubmodule s.subrepresentation_zero)
      (congrArg Subrepresentation.toSubmodule s.subrepresentation_last)
  let Sτ : ObjectRepFiltration (normalizedInductionObject T B τ) m :=
    Induction.valueFiltration (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (τ.representation.comp (B.leviProjection F.Carrier)))
      (fun i => (t.subrepresentation i).toSubmodule)
      (fun _ _ h => t.monotone_subrepresentation h)
      (congrArg Subrepresentation.toSubmodule t.subrepresentation_zero)
      (congrArg Subrepresentation.toSubmodule t.subrepresentation_last)
  refine gradedJordanHolderRefinement ℂ (GeneralLinear n F.Carrier)
    (normalizedInductionObject T B σ) (normalizedInductionObject T B τ) m Sσ Sτ e
    fun i => ?_
  obtain ⟨φ⟩ := he i
  obtain ⟨E₁⟩ := nonempty_valueQuotient_equiv_induced T B σ.representation s i _ hVW
    σ.isSmooth (hτ (e i)) φ
  obtain ⟨E₂⟩ := nonempty_valueQuotient_equiv_induced T B τ.representation t (e i) _ hWW
    τ.isSmooth (hτ (e i)) (Representation.Equiv.refl _)
  exact FactorMatchingProof.haveSameJordanHolderFactors_of_equiv (E₁.trans E₂.symm)
    (FactorMatchingProof.exists_hasCompositionSeriesLength_graded Sσ hfin i)

end Matching
/-- The factor-matching theorem, conditional on generic surjectivity of smooth
induction at the two needed pairs of carrier universes. The finite length of
the second induced output is not needed. -/
theorem normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity
    (hVW : Induction.SmoothInductionSurjectivityStatement.{uF, uV, uW})
    (hWW : Induction.SmoothInductionSurjectivityStatement.{uF, uW, uW}) :
    NormalizedInductionFactorMatchingTheorem.{uF, uV, uW} := by
  intro F T n B σ τ hsrc hfin _
  exact normalizedInductionOutputMatching_of_surjectivity T B
    (normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B hVW)
    (normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B hWW) σ τ hsrc hfin

/-- Normalized parabolic induction preserves matching of actual Jordan–Hölder
factors when both induced outputs have finite length. -/
theorem normalizedInductionFactorMatchingTheorem :
    NormalizedInductionFactorMatchingTheorem.{uF, uV, uW} :=
  normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity
    Induction.smoothInductionSurjectivity Induction.smoothInductionSurjectivity

end Langlands.AllFieldBZ.Parabolic
