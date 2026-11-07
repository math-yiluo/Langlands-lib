import Langlands.Representation.RankinSelberg.SmoothDualPairFactors
import Langlands.Representation.RankinSelberg.SupercuspidalParameterDualityStatement
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Representation.Smooth.Contragredient.Equivalence
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.Whittaker.DualTransform

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear

universe uF uV uW uV₂ uW₂

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W₂}

local instance parameterDualityCanonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance parameterDualityCanonicalTopologicalGroup :
    IsTopologicalGroup (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)

/-- Actual representation equivalences preserve the unramified parameter. -/
theorem IsContragredientTwistParameter.congr_equiv
    (eπ : π.Equiv π₂) (eσ : σ.Equiv σ₂) {a : ℂ}
    (ha : IsContragredientTwistParameter F π σ a) :
    IsContragredientTwistParameter F π₂ σ₂ a := by
  obtain ⟨u, hau, χ, hχ, ⟨e⟩⟩ := ha
  exact ⟨u, hau, χ, hχ,
    ⟨((twistEquiv (χ.comp determinant) eπ).symm.trans e).trans
      (smoothContragredientEquiv eσ.symm)⟩⟩

/-- Dualizing a twist equivalence inverts its parameter. No admissibility is
needed in this direction. -/
theorem IsContragredientTwistParameter.dual {a : ℂ}
    (ha : IsContragredientTwistParameter F π σ a) :
    IsContragredientTwistParameter F
      (smoothContragredient π) (smoothContragredient σ) a⁻¹ := by
  obtain ⟨u, rfl, χ, hχ, ⟨e⟩⟩ := ha
  have hchar : χ.comp determinant =
      F.canonicalTopologicalData.determinantComplexPower (r + 1) (-u) := by
    ext g
    rw [MonoidHom.comp_apply, hχ,
      PadicField.TopologicalData.determinantComplexPower_apply]
    rfl
  have hopen : IsOpen ((χ.comp (determinant :
      Langlands.GeneralLinear (r + 1) F.Carrier →* F.Carrierˣ)).ker :
      Set (Langlands.GeneralLinear (r + 1) F.Carrier)) := by
    rw [hchar]
    exact F.canonicalTopologicalData.isOpen_ker_determinantComplexPower _ _
  refine ⟨-u, ?_, χ⁻¹, ?_, ?_⟩
  · simp only [neg_neg, Complex.cpow_neg, inv_inv]
  · intro x
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hχ,
      neg_neg, Complex.cpow_neg, inv_inv]
  · have hdual := ((smoothContragredientEquiv e).trans
      (smoothContragredientTwistEquiv (χ.comp determinant) π hopen)).symm
    exact ⟨by simpa only [MonoidHom.inv_comp] using hdual⟩

/-- The parameter sets of an admissible pair and its smooth dual pair are
inverse to each other. -/
theorem supercuspidalParameterDuality :
    SupercuspidalParameterDualityStatement.{uF, uV, uW} := by
  intro p _ F r V _ _ W _ _ π σ hπ hσ a
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
  have hcof := GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData (r + 1)
  let eπ := (smoothBidual hπ.1).ofBijective
    ⟨smoothBidual_injective_of_compact_cofinal hcof π hπ.1,
      smoothBidual_surjective_of_compact_cofinal hcof π hπ⟩
  let eσ := (smoothBidual hσ.1).ofBijective
    ⟨smoothBidual_injective_of_compact_cofinal hcof σ hσ.1,
      smoothBidual_surjective_of_compact_cofinal hcof σ hσ⟩
  refine ⟨?_, fun ha => ha.dual⟩
  intro ha
  have hd := ha.dual.congr_equiv eπ.symm eσ.symm
  simpa only [inv_inv] using hd

/-- The inverse-transpose pair used in the functional equation has exactly
the inverse parameters of an irreducible admissible original pair. -/
theorem IsContragredientTwistParameter.inverseTranspose_iff
    (hπa : IsAdmissible π) (hσa : IsAdmissible σ)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible) (a : ℂ) :
    IsContragredientTwistParameter F
        (Whittaker.inverseTransposePullback π) (Whittaker.inverseTransposePullback σ) a⁻¹ ↔
      IsContragredientTwistParameter F π σ a := by
  let eπ := inverseTransposeSmoothDualEquiv F π hπa hπ
  let eσ := inverseTransposeSmoothDualEquiv F σ hσa hσ
  refine ⟨?_, fun ha => ha.dual.congr_equiv eπ.symm eσ.symm⟩
  intro ha
  exact (supercuspidalParameterDuality p F r π σ hπa hσa a).mp
    (ha.congr_equiv eπ eσ)

end Langlands.RankinSelberg
