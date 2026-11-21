import Langlands.Representation.Induction.BlockInducingRecovery
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Exponents.SquareIntegrableInductionEmbeddingConeProof
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.CompactCoefficient.AdmissibleRetraction
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.PullbackProof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-! # Irreducible square-integrable representations are not proper inductions over p-adic data -/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands

universe uG uC uF uV uX

namespace Classification

/-- The smooth dual inverts a scalar character. -/
theorem HasScalarCharacter.smoothContragredient
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {C : Type uC} [Group C] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {z : C →* G} {χ : C →* ℂˣ}
    (hχ : HasScalarCharacter ρ z χ) :
    HasScalarCharacter (Langlands.smoothContragredient ρ) z χ⁻¹ := by
  intro a ℓ
  apply Subtype.ext
  ext v
  change ℓ.val (ρ (z a)⁻¹ v) = ((χ⁻¹ a : ℂˣ) : ℂ) * ℓ.val v
  rw [← map_inv, hχ, map_smul, smul_eq_mul, MonoidHom.inv_apply, map_inv]

end Classification

/-- Taking the full center as the prescribed central subgroup recovers the original
square-integrability predicate. -/
theorem isSquareIntegrableModCentralSubgroup_center_iff
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] :
    Plancherel.IsSquareIntegrableModCentralSubgroup (Subgroup.center G) le_rfl ρ μ ↔
      IsSquareIntegrableModCenter ρ μ := by
  have heq (c : UnitaryCentralCharacter ρ) (ℓ : SmoothDual ρ) (v : V) :
      Plancherel.centralSubgroupCoefficientNorm (Subgroup.center G) le_rfl c ℓ.val v =
        c.coefficientNorm ℓ.val v := by
    funext q
    induction q using Quotient.inductionOn
    rfl
  simp only [Plancherel.IsSquareIntegrableModCentralSubgroup, IsSquareIntegrableModCenter, heq]

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ}

open GeneralLinear

/-- The smooth contragredient of a square-integrable representation of the actual
`GL_n` is square-integrable. -/
theorem isSquareIntegrable_smoothContragredient
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : T.IsSquareIntegrable ρ) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup n
    T.IsSquareIntegrable (smoothContragredient ρ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  let := T.centralQuotientBorelSpace n
  intro μ hμ
  have h := (glBlockCentralQuotientTopology p F T n).1
  let := h.2.1
  let := h.2.2.1
  let := h.2.2.2.1
  let := T.centralQuotientHaar_rightInvariant n μ
  let := Langlands.isInvInvariant_of_isMulRightInvariant μ
  exact (isSquareIntegrableModCentralSubgroup_center_iff _ μ).mp
    (HarishChandraSchwartz.IsSquareIntegrableModCentralSubgroup.smoothContragredient
      _ le_rfl μ (GeneralLinear.compactOpen_cofinal F T n)
      ((isSquareIntegrableModCentralSubgroup_center_iff _ μ).mpr (hρ μ)))

/-- The inverse scalar character has the opposite real-part vector. -/
theorem isRealPartOf_inv {r : ℕ} {χ : (Fin r → F.Carrierˣ) →* ℂˣ} {x : Fin r → ℝ}
    (hx : T.IsRealPartOf χ x) : T.IsRealPartOf χ⁻¹ (-x) := by
  intro a
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hx a, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => (Real.rpow_neg (T.normalizedAbs_nonneg _) _).symm

section Induction

variable (B : BlockShape n) {X : Type uX} [AddCommGroup X] [Module ℂ X]

private theorem induction_scalar_cone
    (hn : 0 < n) (σ : Representation ℂ (B.Levi F.Carrier) X) :
    letI := T.topology
    IsSmooth σ → (T.normalizedParabolicInduced B σ).IsIrreducible →
    T.IsSquareIntegrable (T.normalizedParabolicInduced B σ) →
    ∀ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
      Classification.HasScalarCharacter σ (B.blockScalarLevi F.Carrier) χ →
      ∀ {x : Fin B.length → ℝ}, T.IsRealPartOf χ x → Exponents.IsPositiveRootCone x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hs hi hsq χ hχ x hx
  let π : SmoothRep.{0, uF, max uF uX} ℂ (GeneralLinear n F.Carrier) :=
    SmoothRep.of (T.normalizedParabolicInduced B σ) (T.isSmooth_normalizedParabolicInduced B σ)
  let σ' : SmoothRep.{0, uF, max uF uX} ℂ (B.Levi F.Carrier) :=
    (SmoothRep.of σ hs).universeLift.{uF}
  let e := T.normalizedParabolicInducedEquiv B (universeLiftEquiv.{uF} σ)
  let f : π ⟶ (T.normalizedParabolicInductionFunctor B).obj σ' :=
    SmoothRep.ofHom e.toIntertwiningMap
  have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      π.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule π.representation).mp hi
  have : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π.representation.asModule
  exact squareIntegrableInductionEmbeddingCone.{uF, uX} p F T n hn π hsq B σ'
    ⟨f, e.injective⟩ χ (fun a v => congrArg ULift.up (hχ a v.down)) x hx

/-- A same-parabolic normalized induction of admissible Levi data with a scalar
block-center character cannot be both irreducible and square-integrable when
there are at least two blocks. -/
theorem not_squareIntegrable_normalizedParabolicInduced
    (hB : 2 ≤ B.length) (σ : Representation ℂ (B.Levi F.Carrier) X) :
    letI := T.topology
    IsAdmissible σ → (T.normalizedParabolicInduced B σ).IsIrreducible →
      ∀ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) →
        Classification.HasScalarCharacter σ (B.blockScalarLevi F.Carrier) χ →
        ¬ T.IsSquareIntegrable (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  intro hσ hi χ hχopen hχ hsq
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < B.length) B.length_le
  obtain ⟨x, hx⟩ := T.exists_isRealPartOf χ hχopen
  have hpos := T.induction_scalar_cone B hn σ hσ.1 hi hsq χ hχ hx
  obtain ⟨E, _⟩ := (Parabolic.naturalNormalizedInductionDuality.{uF, uX}).1 p F T n B
  let e := E (Rep.of σ) hσ
  have hdual := T.isSquareIntegrable_smoothContragredient _ hsq
  have hsqd := (T.isSquareIntegrable_iff_of_equiv e).mp hdual
  have hid := (isIrreducible_iff_of_equiv e).mp
    (CompactSplitting.isIrreducible_smoothContragredient
      (GeneralLinear.compactOpen_cofinal F T n) _ hsq.isAdmissible hi)
  have hneg := T.induction_scalar_cone B hn (smoothContragredient σ)
    (isSmooth_smoothContragredient σ) hid hsqd χ⁻¹ hχ.smoothContragredient
    (T.isRealPartOf_inv hx)
  have h1 := hpos.2 1 Nat.zero_lt_one (by omega)
  have h2 := hneg.2 1 Nat.zero_lt_one (by omega)
  rw [show Exponents.partialSum (-x) 1 = -Exponents.partialSum x 1 by
    simp [Exponents.partialSum, Finset.sum_neg_distrib]] at h2
  linarith

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 400000 in
/-- Over the actual carrier and topology of a bundled p-adic field, an irreducible
square-integrable representation of `GL_n` is not isomorphic to any unnormalized
smooth induction from a proper standard block parabolic. -/
theorem isEmpty_equiv_smoothInduced_of_squareIntegrable
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hirr : π.IsIrreducible) (hsq : T.IsSquareIntegrable π) (hB : 2 ≤ B.length)
    (Ξ : Representation ℂ (B.Levi F.Carrier) X) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup n
    IsSmooth Ξ → IsEmpty (π.Equiv
      (Induction.smoothInduced (B.parabolic F.Carrier) (Ξ.comp (B.leviProjection F.Carrier)))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro hΞ
  refine ⟨fun e => ?_⟩
  have hIi := (isIrreducible_iff_of_equiv e).mp hirr
  have hIa := (isAdmissible_iff_of_equiv e).mp hsq.isAdmissible
  obtain ⟨hΞi, hΞa⟩ := B.isIrreducible_isAdmissible_of_smoothInduced hΞ hIi hIa
  let δ := T.leviHalfModulus B
  let σ := twist δ⁻¹ Ξ
  have hσa : IsAdmissible σ := (isAdmissible_twist_iff _ _
    (isOpen_ker_inv (T.isOpen_ker_leviHalfModulus B))).mpr hΞa
  have hσi : σ.IsIrreducible := (isIrreducible_twist_iff _ _).mpr hΞi
  obtain ⟨χ, hχo, hχ⟩ := B.exists_blockScalarCharacter hσa hσi
  have ht : twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)) =
      Ξ.comp (B.leviProjection F.Carrier) := by
    rw [show σ = twist δ⁻¹ Ξ by rfl, twist_comp]
    have hδ : δ⁻¹.comp (B.leviProjection F.Carrier) = (T.parabolicHalfModulus B)⁻¹ := rfl
    rw [hδ, twist_twist_inv]
  let e' : (T.normalizedParabolicInduced B σ).Equiv
      (Induction.smoothInduced (B.parabolic F.Carrier) (Ξ.comp (B.leviProjection F.Carrier))) :=
    Induction.smoothInducedEquiv _ (equivOfRepresentationEq ht)
  let eN := e.trans e'.symm
  exact T.not_squareIntegrable_normalizedParabolicInduced B hB σ hσa
    ((isIrreducible_iff_of_equiv eN).mp hirr) χ hχo hχ
    ((T.isSquareIntegrable_iff_of_equiv eN).mp hsq)

end Induction

end PadicField.TopologicalData

end Langlands
