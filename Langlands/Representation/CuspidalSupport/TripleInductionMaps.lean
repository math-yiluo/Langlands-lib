import Langlands.Representation.CuspidalSupport.UniformTripleTransferStatement
import Langlands.Representation.CuspidalSupport.IrreducibleInductionOccurrence
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Filtration.IrreducibleExactComparison

/-! Actual induction maps used in the local repeated-factor triple reduction. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Constituent commutativity of two irreducible factors becomes an actual
isomorphism of the two products when one product is irreducible. -/
def irreducibleTwoFactorSwapIso {n : ℕ} (B : BlockShape n) (hB : B.length = 2) :
    letI := T.topology
    ∀ (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (_hA : ∀ i, (A i).IsIrreducible)
      (_hP : ((T.normalizedProductInductionFunctor B).obj A).IsIrreducible),
      (T.normalizedProductInductionFunctor B).obj A ≅
        (T.normalizedProductInductionFunctor (B.permute (B.adjacentSwap 0 (by omega)))).obj
          (fun i => A (B.adjacentSwap 0 (by omega) i)) := by
  let := T.topology
  intro A hA hP
  have hJH := Classification.twoFactorProductConstituentCommutativity F T n B hB A hA
  let e := Classical.choice (RepresentationExactComparison.nonempty_equiv_of_sameFactors
    (Rep.of ((T.normalizedProductInductionFunctor B).obj A).representation)
    (Rep.of ((T.normalizedProductInductionFunctor (B.permute (B.adjacentSwap 0 (by omega)))).obj
      (fun i => A (B.adjacentSwap 0 (by omega) i))).representation) hP hJH)
  exact SmoothRep.mkIso e

/-- An irreducible admissible ambient object with an actual irreducible
cuspidal Jacquet occurrence injects into that cuspidal induction. The
induced object need not be irreducible. -/
theorem exists_inductionInjection_of_cuspidalOccurrence {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      E.IsIrreducible → E.IsAdmissible →
      D.IsIrreducible → IsLeviCuspidal B D.representation →
      SmoothRep.IsSubquotient D ((T.normalizedJacquetFunctor B).obj E) →
      ∃ f : E.representation.IntertwiningMap (T.normalizedParabolicInduced B D.representation),
        Function.Injective f := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro E D hEi hEa hDi hDc hOcc
  have hJa : ((T.normalizedJacquetFunctor B).obj E).IsAdmissible :=
    FiniteLengthAssembly.isAdmissible_normalizedJacquet T B E.representation hEa
  obtain ⟨q, hq⟩ :=
    (leviCuspidalConstituentTheorem F T B _ D hJa hDi hDc hOcc).2
  let q' : (T.normalizedJacquet B E.representation).IntertwiningMap D.representation :=
    SmoothRep.hom q
  let := hDi
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F.Carrier)) D.representation.asModule
  have hq0 : q' ≠ 0 := by
    intro hq0
    obtain ⟨d, hd⟩ := exists_ne (0 : D)
    obtain ⟨v, hv⟩ := hq d
    exact hd (hv.symm.trans (congrArg (fun h => h v) hq0))
  let e := Parabolic.FirstAdjointness.equiv T B E.isSmooth (σ := D.representation)
  let f := e.symm q'
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hq0
    have hf := congrArg e hf0
    simpa only [f, e.apply_symm_apply, map_zero] using hf
  let := hEi
  exact ⟨f, (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf0⟩

/-- The actual uniform tensor of three supplied supercuspidals is irreducible
and cuspidal as a representation of the three-block Levi. -/
theorem uniformTripleTensor_irreducible_cuspidal {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ A B C : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d),
      (uniformTripleTensor F T hd A.obj B.obj C.obj).IsIrreducible ∧
      IsLeviCuspidal (threeBlocks d d d hd hd hd)
        (uniformTripleTensor F T hd A.obj B.obj C.obj).representation := by
  let := T.topology
  intro A B C
  let K : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier)
      (n := (threeBlocks d d d hd hd hd).size i) :=
    Fin.cases A (Fin.cases B (Fin.cases C finZeroElim))
  have hK : (fun i => (K i).obj) = threeBlockSmoothFamily A.obj B.obj C.obj := by
    funext i
    fin_cases i <;> rfl
  have h := glCuspidalTensor p F T (d + (d + d)) (by omega)
    (threeBlocks d d d hd hd hd) K
  dsimp only at h
  rw [hK] at h
  exact h

/-- An actual uniform triple Jacquet occurrence supplies an actual injection
into the full ordered three-factor induction. -/
theorem exists_uniformTripleInductionInjection {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (d + (d + d)) F.Carrier))
      (A B C : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d)),
      E.IsIrreducible → E.IsAdmissible →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj C.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) →
      ∃ f : E.representation.IntertwiningMap
        (T.normalizedProductInduced (threeBlocks d d d hd hd hd)
          (fun i => (threeBlockSmoothFamily A.obj B.obj C.obj i).representation)),
        Function.Injective f := by
  let := T.topology
  intro E A B C hEi hEa hOcc
  have hD := uniformTripleTensor_irreducible_cuspidal F T hd A B C
  exact exists_inductionInjection_of_cuspidalOccurrence F T
    (threeBlocks d d d hd hd hd) E
    (uniformTripleTensor F T hd A.obj B.obj C.obj) hEi hEa hD.1 hD.2 hOcc

/-- An actual injection into the ordered triple induction recovers the
actual cuspidal tensor as a quotient of the normalized Jacquet module. -/
theorem uniformTripleOccurrence_of_inductionInjection {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (d + (d + d)) F.Carrier))
      (A B C : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)),
      E.IsIrreducible →
      ∀ f : E.representation.IntertwiningMap
        (T.normalizedParabolicInduced (threeBlocks d d d hd hd hd)
          (uniformTripleTensor F T hd A.obj B.obj C.obj).representation),
        Function.Injective f →
        SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj C.obj)
          ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) := by
  let := T.topology
  intro E A B C hEi f hf
  let := hEi
  let : Nontrivial E :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (d + (d + d)) F.Carrier))
      E.representation.asModule
  have hf0 : f ≠ 0 := by
    intro hf0
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    apply hv
    apply hf
    simp [hf0]
  exact (isQuotient_normalizedJacquet_of_inductionHom F T (threeBlocks d d d hd hd hd)
    E (uniformTripleTensor F T hd A.obj B.obj C.obj)
    (uniformTripleTensor_irreducible_cuspidal F T hd A B C).1 f hf0).isSubquotient

end Langlands.CuspidalSupport
