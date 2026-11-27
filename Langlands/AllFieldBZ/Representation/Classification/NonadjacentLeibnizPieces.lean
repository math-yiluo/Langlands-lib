import Langlands.AllFieldBZ.Representation.Classification.NonadjacentTwoBlock
import Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalBinaryProductBridge
import Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalDerivativeBridge
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicDerivativeVanishing
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicHighestDerivativePairingProof
import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Classification.NonadjacentLeibnizPieces

/-!
# All-field port of `Langlands.Representation.Classification.NonadjacentLeibnizPieces`

The intermediate proposition `TwoBlockDerivativePieces` derived from the
statements `GeneralLinearDerivativeLeibnizFiltrationStatement` (BZ77 4.14(c))
and `SupercuspidalDerivatives` (BZ77 4.4), and Ze80 Proposition 1.11(a) with exactness,
detection, BZ77 3.8 and BZ77 4.4 discharged by their proofs in the Library, conditional only
on the Leibniz filtration statement.

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.AllFieldBZ.Classification.NonadjacentAssembly

open Langlands.Classification

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Derivative Langlands.Classification.BinaryProductBridge

universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
  (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The derivative pattern of a supercuspidal representation: vanishing derivatives
of intermediate order and a one-dimensional top derivative. -/
def SupercuspidalDerivativePattern {a : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) : Prop :=
  letI := T.topology
  (∀ (i : ℕ) (hi : i ≤ a), 0 < i → i < a →
    Subsingleton ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ a i hi).obj A)) ∧
  Module.finrank ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ a a le_rfl).obj A) = 1

/-- `SupercuspidalDerivatives` gives the derivative pattern of every supercuspidal
representation of positive rank. -/
theorem supercuspidalDerivativePattern (hSD : Langlands.AllFieldBZ.Classification.SupercuspidalDerivatives.{uF, uV} F T)
    {k : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    SupercuspidalDerivativePattern F T ψ ρ.obj := by
  let _ := T.topology
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h1, h2⟩ := hSD ψ n ρ.obj ρ.property.1 ρ.property.2
  exact ⟨fun i hi h0 hlt => h1 i hi h0 hlt, h2⟩

/-- At an intermediate order, a Leibniz piece of `A × B` for factors with the
supercuspidal derivative pattern is zero, or equivalent to the rank cast of `A`
(index `(0, b)`), or to the rank cast of `B` (index `(a, 0)`). -/
theorem leibnizPiece_cases {a b d : ℕ} (hd0 : 0 < d) (hd1 : d < a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B)
    (x : LeibnizIndex a b d) :
    letI := T.topology
    Subsingleton ((Langlands.AllFieldBZ.Derivative.leibnizPiece T ψ a b d x).obj (A, B)) ∨
      (∃ h : a = a + b - d, Nonempty (((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj A).representation.Equiv
        ((Langlands.AllFieldBZ.Derivative.leibnizPiece T ψ a b d x).obj (A, B)).ρ)) ∨
      (∃ h : b = a + b - d, Nonempty (((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj B).representation.Equiv
        ((Langlands.AllFieldBZ.Derivative.leibnizPiece T ψ a b d x).obj (A, B)).ρ)) := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hx
  dsimp only at hij hia hjb
  by_cases hi : 0 < i ∧ i < a
  · exact Or.inl (Langlands.AllFieldBZ.Classification.BinaryProductBridge.subsingleton_rankCast_product F T _ _ _ (Or.inl (hA.1 i hia hi.1 hi.2)))
  by_cases hj : 0 < j ∧ j < b
  · exact Or.inl (Langlands.AllFieldBZ.Classification.BinaryProductBridge.subsingleton_rankCast_product F T _ _ _ (Or.inr (hB.1 j hjb hj.1 hj.2)))
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    have hjb' : j = b := by omega
    subst hjb'
    exact Or.inr (Or.inl ⟨by omega, Langlands.AllFieldBZ.Classification.BinaryProductBridge.nonempty_equiv_rankCast_product_right F T (Nat.sub_self j)
      (leibnizIndices_rank hx) (by dsimp only; omega) _ _ hB.2⟩)
  · have hia' : i = a := by omega
    have hj0 : j = 0 := by omega
    subst hia' hj0
    exact Or.inr (Or.inr ⟨by omega, Langlands.AllFieldBZ.Classification.BinaryProductBridge.nonempty_equiv_rankCast_product_left F T (Nat.sub_self i)
      (leibnizIndices_rank hx) (by dsimp only; omega) _ _ hA.2⟩)

/-- The unique Leibniz piece at the top order is one-dimensional. -/
theorem finrank_leibnizPiece_top {a b : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B)
    (x : LeibnizIndex a b (a + b)) :
    Module.finrank ℂ ((Langlands.AllFieldBZ.Derivative.leibnizPiece T ψ a b (a + b) x).obj (A, B)) = 1 := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hx
  dsimp only at hij hia hjb
  have hi : i = a := by omega
  have hj : j = b := by omega
  subst hi hj
  exact Langlands.AllFieldBZ.Classification.BinaryProductBridge.finrank_rankCast_product_of_zero_zero F T (Nat.sub_self i) (Nat.sub_self j)
    (leibnizIndices_rank hx) _ _ hA.2 hB.2

/-- Under the Leibniz filtration statement, the top derivative of `A × B` is
one-dimensional when both factors have the supercuspidal derivative pattern. -/
theorem finrank_top_binary
    (hL : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T) {a b d : ℕ}
    (hd : d ≤ a + b) (hda : d = a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B) :
    letI := T.topology
    Module.finrank ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (a + b) d hd).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A, B))) = 1 := by
  let _ := T.topology
  subst hda
  obtain ⟨e, s, hs⟩ := hL.filtration T ψ a b (a + b) le_rfl
  let i0 : Fin (leibnizIndices a b (a + b)).card := ⟨0, by rw [Langlands.Classification.NonadjacentAssembly.card_leibnizIndices_top]; omega⟩
  obtain ⟨L⟩ := Langlands.Classification.NonadjacentAssembly.nonempty_linearEquiv_graded_of_length_one
    (CuspidalSupport.objectFiltrationAt s (A, B)) (Langlands.Classification.NonadjacentAssembly.card_leibnizIndices_top a b) i0
  obtain ⟨φ⟩ := hs i0
  exact L.finrank_eq.symm.trans
    ((Representation.equivOfIso (φ.app (A, B))).toLinearEquiv.finrank_eq.trans
      (finrank_leibnizPiece_top F T ψ A B hA hB _))

/-- Under the Leibniz filtration statement, at every intermediate order the
derivative of `A × B` has a filtration whose graded pieces are zero or equivalent
to rank casts of `A` or `B`. -/
theorem exists_filtration_binary
    (hL : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    {a b d : ℕ} (hd : d ≤ a + b) (hd0 : 0 < d) (hd1 : d < a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B) :
    letI := T.topology
    ∃ (n : ℕ) (s : ObjectRepFiltration (SmoothRep.toRep.obj
        ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (a + b) d hd).obj
          ((T.binaryNormalizedProductFunctor a b).obj (A, B)))) n),
      ∀ i, Subsingleton (s.gradedRepresentation i) ∨
        (∃ h : a = a + b - d, Nonempty (((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj A).representation.Equiv
          (s.gradedRepresentation i).ρ)) ∨
        (∃ h : b = a + b - d, Nonempty (((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj B).representation.Equiv
          (s.gradedRepresentation i).ρ)) := by
  let _ := T.topology
  obtain ⟨e, s, hs⟩ := hL.filtration T ψ a b d hd
  refine ⟨_, CuspidalSupport.objectFiltrationAt s (A, B), fun i => ?_⟩
  obtain ⟨φ⟩ := hs i
  let f := Representation.equivOfIso (φ.app (A, B))
  rcases leibnizPiece_cases F T ψ hd0 hd1 A B hA hB (e.symm i) with h | ⟨h, ⟨f'⟩⟩ | ⟨h, ⟨f'⟩⟩
  · exact Or.inl f.toLinearEquiv.subsingleton
  · exact Or.inr (Or.inl ⟨h, ⟨f'.trans f.symm⟩⟩)
  · exact Or.inr (Or.inr ⟨h, ⟨f'.trans f.symm⟩⟩)

/-- The restricted derivative of the two-block product is the actual derivative of
the binary product. -/
theorem restrictedDerivative_twoBlockProduct {k l : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1))
    (d : ℕ) (hd : 0 < d ∧ d ≤ k + l + 1) :
    letI := T.topology
    (restrictedDerivative F T ψ (k + l) d hd).obj (twoBlockProduct F T hk ρ ρ') =
      (Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (k + (l + 1)) d hd.2).obj
        ((T.binaryNormalizedProductFunctor k (l + 1)).obj (ρ.obj, ρ'.obj)) := by
  let _ := T.topology
  rw [Langlands.AllFieldBZ.Classification.BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks F T hk l.succ_pos]
  exact (Langlands.AllFieldBZ.Derivative.generalLinearDerivative_obj_eq_restriction T ψ (k + l) d hd.2 hd _).symm

/-- `TwoBlockDerivativePieces` follows from the statements
`GeneralLinearDerivativeLeibnizFiltrationStatement` and `SupercuspidalDerivatives`. -/
theorem twoBlockDerivativePieces_of_leibniz
    (hL : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (hSD : Langlands.AllFieldBZ.Classification.SupercuspidalDerivatives.{uF, uV} F T) :
    TwoBlockDerivativePieces.{uF, uV} F T := by
  intro ψ k l hk ρ ρ'
  let _ := T.topology
  have hρ := supercuspidalDerivativePattern F T ψ hSD hk ρ
  have hρ' := supercuspidalDerivativePattern F T ψ hSD l.succ_pos ρ'
  refine ⟨?_, fun d hd hdlt => ?_⟩
  · rw [restrictedDerivative_twoBlockProduct F T ψ hk ρ ρ']
    exact finrank_top_binary F T ψ hL _ (by omega) ρ.obj ρ'.obj hρ hρ'
  · rw [restrictedDerivative_twoBlockProduct F T ψ hk ρ ρ' d hd]
    exact exists_filtration_binary F T ψ hL (a := k) (b := l + 1) hd.2 hd.1 hdlt ρ.obj ρ'.obj
      hρ hρ'

/-- Ze80 Proposition 1.11(a), conditional on the exactness, detection,
BZ77 3.8, Leibniz filtration and `SupercuspidalDerivatives` statements. -/
theorem nonadjacent_of_leibniz
    (hE : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T)
    (hPL : Langlands.AllFieldBZ.Derivative.MirabolicDerivativeDetection.{uF, max uF uV} F T)
    (hHP : Langlands.AllFieldBZ.Derivative.MirabolicHighestDerivativePairingStatement.{uF, max uF uV, max uF uV} F T)
    (hL : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (hSD : Langlands.AllFieldBZ.Classification.SupercuspidalDerivatives.{uF, uV} F T) :
    Langlands.AllFieldBZ.Classification.TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_twoBlockDerivativePieces F T hE hPL hHP
    (twoBlockDerivativePieces_of_leibniz F T hL hSD)

/-- Ze80 Proposition 1.11(a), with detection and BZ77 3.8 discharged by their
proofs `Mirabolic.derivativeDetection` and `mirabolicHighestDerivativePairing`; still
conditional on the exactness, Leibniz filtration and `SupercuspidalDerivatives` statements. -/
theorem nonadjacent_of_exactness_leibniz
    (hE : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T)
    (hL : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (hSD : Langlands.AllFieldBZ.Classification.SupercuspidalDerivatives.{uF, uV} F T) :
    Langlands.AllFieldBZ.Classification.TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_leibniz F T hE (Langlands.AllFieldBZ.Derivative.Mirabolic.derivativeDetection F T)
    (Langlands.AllFieldBZ.Derivative.mirabolicHighestDerivativePairing F T) hL hSD

/-- Ze80 Proposition 1.11(a), with `SupercuspidalDerivatives` also discharged by its
proof `supercuspidalDerivatives`; still conditional on the exactness and
Leibniz filtration statements. -/
theorem nonadjacent_of_exactness_leibnizFiltration
    (hE : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T)
    (hL : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T) :
    Langlands.AllFieldBZ.Classification.TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_exactness_leibniz F T hE hL (Langlands.AllFieldBZ.Classification.supercuspidalDerivatives F T)

/-- Ze80 Proposition 1.11(a), with exactness also discharged by its proof in the Library
`Derivative.generalLinearDerivativeExactness` (at carrier universe `max uF uV`); still
conditional on the Leibniz filtration statement. -/
theorem nonadjacent_of_leibnizFiltration
    (hL : Langlands.AllFieldBZ.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T) :
    Langlands.AllFieldBZ.Classification.TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_exactness_leibnizFiltration F T
    (Langlands.AllFieldBZ.Derivative.generalLinearDerivativeExactness.{uF, max uF uV} F T) hL

end Langlands.AllFieldBZ.Classification.NonadjacentAssembly
