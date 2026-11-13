import Langlands.Representation.Classification.A6iiShapes
import Langlands.Representation.Classification.TwistedProductCharacterTwistProof
import Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof
import Langlands.Representation.RankinSelberg.InducedWhittakerQuotient

/-!
# Segment quotients under twists, and products of surjections

An irreducible quotient of `i(A, νA, …, ν^(m-1)A)` twisted by `ν^s` is an
irreducible quotient of the same induction built from `ν^s A`. Normalized
products of blockwise surjections are surjective, and a common real twist of all
blocks can be moved outside a normalized product.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The twist of a supercuspidal representative by `ν^s`. -/
abbrev twistSC {r : ℕ} (s : ℝ)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r) :=
  letI := T.topology
  GeneralLinear.SupercuspidalRep.twist (T.determinantPowerCharacter r s)
    (T.isOpen_ker_determinantPowerCharacter r s)
    (T.ker_determinant_le_ker_determinantPowerCharacter r s) A

/-- An irreducible quotient of a segment induction, twisted by `ν^s`, is an
irreducible quotient of the segment induction of the twisted representative. -/
theorem segment_twisted_quotient (Δ : T.Segment.{max uF uV, uF})
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hq : letI := T.topology
      IsIrreducibleQuotient (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation
        π.representation) (s : ℝ) :
    letI := T.topology
    IsIrreducibleQuotient
      (T.segmentInduced (twistSC F T s A).obj Δ.length Δ.rank_pos).representation
      (T.segmentFactor π s).representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨realPowerCharacter T.normalizedAbsUnits s,
      isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s⟩
  obtain ⟨e⟩ := twistedProductCharacterTwist.{uF, max uF uV} F T
    Δ.degree Δ.degree_pos (GeneralLinear.BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)
    χ (fun _ => A.obj) (fun i => ((i : ℕ) : ℝ))
  have hq' := (isIrreducibleQuotient_twist_iff
    (T.determinantPowerCharacter Δ.degree s)
    (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation).mpr hq
  exact hq'.of_equiv e

/-- Normalized products of blockwise surjections are surjective. -/
theorem productMap_surjective {n : ℕ} (B : BlockShape n)
    {X Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (f : letI := T.topology; ∀ i, X i ⟶ Y i)
    (hf : letI := T.topology; ∀ i, Function.Surjective (SmoothRep.hom (f i))) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom ((T.normalizedProductInductionFunctor B).map f)) := by
  let := T.topology
  exact T.normalizedProductInducedMap_surjective B _ _ (fun i => (X i).isSmooth)
    (fun i => (Y i).isSmooth) (fun i => SmoothRep.hom (f i)) hf

/-- A common real twist of all blocks moves outside the normalized product. -/
theorem commonExponentIso {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) (s : ℝ) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
      T.segmentFactor ((T.normalizedProductInductionFunctor B).obj
        (fun i => T.segmentFactor (σ i) (-s))) s) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ := {
    toMonoidHom := realPowerCharacter T.normalizedAbsUnits s
    isOpen_ker := isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s }
  obtain ⟨E⟩ := twistedProductCharacterTwist.{uF, uV} F T n hn B χ σ (fun _ => -s)
  let σ' : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.segmentFactor (T.segmentFactor (σ i) s) (-s)
  have eσ (i) : σ' i ≅ σ i := by
    apply SmoothRep.mkIso
    change (realPowerTwist (T.determinantNorm (B.size i)) (-s)
      (realPowerTwist (T.determinantNorm (B.size i)) s (σ i).representation)).Equiv _
    rw [realPowerTwist_neg_cancel]
    exact Representation.Equiv.refl _
  let eI := (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk eσ)
  have eE : T.segmentFactor ((T.normalizedProductInductionFunctor B).obj
      (fun i => T.segmentFactor (σ i) (-s))) s ≅
      (T.normalizedProductInductionFunctor B).obj σ' := by
    apply SmoothRep.mkIso
    exact E
  exact ⟨eI.symm ≪≫ eE.symm⟩

/-- The bundled induction of a block tensor is the object of the product
induction functor. -/
theorem induced_obj_eq {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    CuspidalJacquetMultiplicity.induced T B (Rep.of (B.blockTensor fun i => (σ i).representation)) =
      ((T.normalizedProductInductionFunctor B).obj σ).obj :=
  rfl

end Langlands.Classification.A6ii
