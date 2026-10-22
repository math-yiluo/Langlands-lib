import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticStatement
import Langlands.ClassFieldTheory.Local.FixedFieldStages
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.Weil.Local.Assembly

/-! # Finite unramified Galois extensions of every positive degree -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open CategoryTheory ProfiniteGrp Langlands.LocalClassField Langlands.Weil Langlands.Weil.Local

universe u

/-- Reduction of integers modulo `n`, written multiplicatively. -/
def degreeModHom (n : ℕ) : Degree →* Multiplicative (ZMod n) :=
  (Int.castAddHom (ZMod n)).toMultiplicative

/-- Reduction modulo `n` is surjective. -/
theorem degreeModHom_surjective (n : ℕ) : Function.Surjective (degreeModHom n) := by
  intro x
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
  refine ⟨Multiplicative.ofAdd m, ?_⟩
  change Multiplicative.ofAdd (m : ZMod n) = x
  rw [hm]
  rfl

/-- The finite-index normal subgroup `n ℤ` of the integer group. -/
def degreeModSubgroup (n : ℕ) [NeZero n] : FiniteIndexNormalSubgroup Degree :=
  FiniteIndexNormalSubgroup.ofSubgroup (degreeModHom n).ker

/-- The subgroup `n ℤ` has index `n`. -/
theorem degreeModSubgroup_index (n : ℕ) [NeZero n] :
    (degreeModSubgroup n).toSubgroup.index = n := by
  change (degreeModHom n).ker.index = n
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (degreeModHom_surjective n),
    Subgroup.card_top]
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod n)

/-- The coordinate of a profinite integer in the finite quotient `ℤ / n ℤ`. -/
def profiniteModProjection (n : ℕ) [NeZero n] :
    ProfiniteIntegers →ₜ* (ProfiniteCompletion.diagram (GrpCat.of Degree)).obj
      (degreeModSubgroup n) :=
  ((limitCone (ProfiniteCompletion.diagram (GrpCat.of Degree))).π.app
    (degreeModSubgroup n)).hom

/-- On integer Frobenius powers the projection is the quotient map. -/
theorem profiniteModProjection_frobenius (n : ℕ) [NeZero n] (m : Degree) :
    profiniteModProjection n (frobenius m) = (QuotientGroup.mk m : Degree ⧸ _) := rfl

/-- The projection to `ℤ / n ℤ` is surjective. -/
theorem profiniteModProjection_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (profiniteModProjection n) := by
  intro x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨frobenius m, profiniteModProjection_frobenius n m⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The residue degree of an absolute Galois element modulo `n`. -/
def residueDegreeMod (n : ℕ) [NeZero n] :
    Field.absoluteGaloisGroup F.Carrier →ₜ* (ProfiniteCompletion.diagram (GrpCat.of Degree)).obj
      (degreeModSubgroup n) :=
  (profiniteModProjection n).comp (localResidueDegree F)

/-- The residue degree modulo `n` is surjective. -/
theorem residueDegreeMod_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (residueDegreeMod F n) :=
  (profiniteModProjection_surjective n).comp (localResidueDegree_surjective F)

/-- The kernel of the residue degree modulo `n`, as an open normal subgroup. -/
def residueDegreeModKernel (n : ℕ) [NeZero n] :
    OpenNormalSubgroup (Field.absoluteGaloisGroup F.Carrier) where
  toSubgroup := (residueDegreeMod F n).toMonoidHom.ker
  isOpen' := by
    have : Finite ((ProfiniteCompletion.diagram (GrpCat.of Degree)).obj
        (degreeModSubgroup n)) := by
      change Finite (Degree ⧸ (degreeModSubgroup n).toSubgroup)
      infer_instance
    have : DiscreteTopology ((ProfiniteCompletion.diagram (GrpCat.of Degree)).obj
        (degreeModSubgroup n)) := inferInstance
    exact (residueDegreeMod F n).continuous.isOpen_preimage {1} (isOpen_discrete _)
  isNormal' := inferInstance

/-- The kernel of the residue degree modulo `n` has index `n`. -/
theorem residueDegreeModKernel_index (n : ℕ) [NeZero n] :
    (residueDegreeModKernel F n).toSubgroup.index = n := by
  change (residueDegreeMod F n).toMonoidHom.ker.index = n
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (residueDegreeMod_surjective F n),
    Subgroup.card_top]
  exact degreeModSubgroup_index n

/-- Absolute inertia lies in the kernel of the residue degree modulo `n`. -/
theorem absoluteInertia_le_residueDegreeModKernel (n : ℕ) [NeZero n] :
    F.absoluteInertia F.canonicalTopologicalData ≤ (residueDegreeModKernel F n).toSubgroup := by
  rw [← localResidueDegree_ker F]
  intro σ hσ
  change profiniteModProjection n (localResidueDegree F σ) = 1
  rw [MonoidHom.mem_ker] at hσ
  change localResidueDegree F σ = 1 at hσ
  rw [hσ, map_one]

/-- Every positive degree occurs for a finite Galois intermediate field of the
algebraic closure with the same canonical ramification index as the base. -/
theorem unramifiedExtensionDegreeExistence : UnramifiedExtensionDegreeExistence.{u} := by
  intro p _ F n hn
  have : NeZero n := ⟨hn.ne'⟩
  let _ : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let _ : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let N := residueDegreeModKernel F n
  let E : FiniteIntermediateExtension F.Carrier :=
    ⟨finiteStageFixedField F.Carrier N, inferInstance⟩
  have hE : IsGalois F.Carrier E.field :=
    finiteStageFixedField_isGalois F.Carrier N
  have hfix : E.field.fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField (finiteStageClosedSubgroup F.Carrier N)
  refine ⟨E, hE, ?_, ?_⟩
  · apply (Langlands.PadicField.canonicalUnramifiedCriterion p F E).mpr
    rw [hfix]
    exact absoluteInertia_le_residueDegreeModKernel F n
  · rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact residueDegreeModKernel_index F n

end Langlands.ClassFieldTheory.Local
