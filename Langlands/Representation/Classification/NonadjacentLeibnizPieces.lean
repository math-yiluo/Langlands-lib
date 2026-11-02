import Langlands.Representation.Classification.NonadjacentTwoBlock
import Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge
import Langlands.Representation.Classification.TwoSupercuspidalDerivativeBridge
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.Derivative.MirabolicDerivativeVanishing
import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof

/-! The intermediate proposition `TwoBlockDerivativePieces` derived from the
published statements `GeneralLinearDerivativeLeibnizFiltrationStatement` (BZ77 4.14(c))
and `SupercuspidalDerivatives` (BZ77 4.4), and Ze80 Proposition 1.11(a) with exactness,
detection, BZ77 3.8 and BZ77 4.4 discharged by their published proofs, conditional only
on the Leibniz filtration statement. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.NonadjacentAssembly

open GeneralLinear HarmonicAnalysis Derivative BinaryProductBridge

universe uF uV

/-- The only graded piece of a filtration of length one is linearly equivalent to
the whole representation. -/
theorem nonempty_linearEquiv_graded_of_length_one {R G : Type*} [CommRing R] [Monoid G]
    {X : Rep.{uV} R G} {n : ℕ} (s : ObjectRepFiltration X n) (hn : n = 1) (i : Fin n) :
    Nonempty ((s.gradedRepresentation i) ≃ₗ[R] X) := by
  subst hn
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : s.subrepresentation 0 = ⊥ := s.subrepresentation_zero
  have h1 : s.subrepresentation (Fin.last 1) = ⊤ := s.subrepresentation_last
  let q := ((s.step (0 : Fin 1).castSucc).lowerInUpper (s.step (0 : Fin 1).succ)
    (Discrete.mk PUnit.unit)).toSubmodule
  have hq : q = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : ((s.step (0 : Fin 1).succ).obj (Discrete.mk PUnit.unit)).toSubmodule.subtype v ∈
        (s.subrepresentation 0).toSubmodule := hv
    rw [h0] at hv'
    exact (Submodule.mem_bot R).2 (Subtype.ext hv')
  have htop : (s.subrepresentation (Fin.last 1)).toSubmodule = ⊤ := by rw [h1]; rfl
  exact ⟨(Submodule.quotEquivOfEqBot q hq).trans (LinearEquiv.ofTop _ htop)⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The derivative pattern of a supercuspidal representation: vanishing derivatives
of intermediate order and a one-dimensional top derivative. -/
def SupercuspidalDerivativePattern {a : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) : Prop :=
  letI := T.topology
  (∀ (i : ℕ) (hi : i ≤ a), 0 < i → i < a →
    Subsingleton ((generalLinearDerivative T ψ a i hi).obj A)) ∧
  Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj A) = 1

/-- `SupercuspidalDerivatives` gives the derivative pattern of every supercuspidal
representation of positive rank. -/
theorem supercuspidalDerivativePattern (hSD : SupercuspidalDerivatives.{uF, uV} F T)
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
    Subsingleton ((leibnizPiece T ψ a b d x).obj (A, B)) ∨
      (∃ h : a = a + b - d, Nonempty (((generalLinearRankCast T h).obj A).representation.Equiv
        ((leibnizPiece T ψ a b d x).obj (A, B)).ρ)) ∨
      (∃ h : b = a + b - d, Nonempty (((generalLinearRankCast T h).obj B).representation.Equiv
        ((leibnizPiece T ψ a b d x).obj (A, B)).ρ)) := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hx
  dsimp only at hij hia hjb
  by_cases hi : 0 < i ∧ i < a
  · exact Or.inl (subsingleton_rankCast_product F T _ _ _ (Or.inl (hA.1 i hia hi.1 hi.2)))
  by_cases hj : 0 < j ∧ j < b
  · exact Or.inl (subsingleton_rankCast_product F T _ _ _ (Or.inr (hB.1 j hjb hj.1 hj.2)))
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    have hjb' : j = b := by omega
    subst hjb'
    exact Or.inr (Or.inl ⟨by omega, nonempty_equiv_rankCast_product_right F T (Nat.sub_self j)
      (leibnizIndices_rank hx) (by dsimp only; omega) _ _ hB.2⟩)
  · have hia' : i = a := by omega
    have hj0 : j = 0 := by omega
    subst hia' hj0
    exact Or.inr (Or.inr ⟨by omega, nonempty_equiv_rankCast_product_left F T (Nat.sub_self i)
      (leibnizIndices_rank hx) (by dsimp only; omega) _ _ hA.2⟩)

/-- The unique Leibniz piece at the top order is one-dimensional. -/
theorem finrank_leibnizPiece_top {a b : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B)
    (x : LeibnizIndex a b (a + b)) :
    Module.finrank ℂ ((leibnizPiece T ψ a b (a + b) x).obj (A, B)) = 1 := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hx
  dsimp only at hij hia hjb
  have hi : i = a := by omega
  have hj : j = b := by omega
  subst hi hj
  exact finrank_rankCast_product_of_zero_zero F T (Nat.sub_self i) (Nat.sub_self j)
    (leibnizIndices_rank hx) _ _ hA.2 hB.2

/-- The feasible index set at the top order has one element. -/
theorem card_leibnizIndices_top (a b : ℕ) : (leibnizIndices a b (a + b)).card = 1 := by
  rw [leibnizIndices_top, Finset.card_singleton]

/-- Under the Leibniz filtration statement, the top derivative of `A × B` is
one-dimensional when both factors have the supercuspidal derivative pattern. -/
theorem finrank_top_binary
    (hL : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T) {a b d : ℕ}
    (hd : d ≤ a + b) (hda : d = a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B) :
    letI := T.topology
    Module.finrank ℂ ((generalLinearDerivative T ψ (a + b) d hd).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A, B))) = 1 := by
  let _ := T.topology
  subst hda
  obtain ⟨e, s, hs⟩ := hL.filtration T ψ a b (a + b) le_rfl
  let i0 : Fin (leibnizIndices a b (a + b)).card := ⟨0, by rw [card_leibnizIndices_top]; omega⟩
  obtain ⟨L⟩ := nonempty_linearEquiv_graded_of_length_one
    (CuspidalSupport.objectFiltrationAt s (A, B)) (card_leibnizIndices_top a b) i0
  obtain ⟨φ⟩ := hs i0
  exact L.finrank_eq.symm.trans
    ((Representation.equivOfIso (φ.app (A, B))).toLinearEquiv.finrank_eq.trans
      (finrank_leibnizPiece_top F T ψ A B hA hB _))

/-- Under the Leibniz filtration statement, at every intermediate order the
derivative of `A × B` has a filtration whose graded pieces are zero or equivalent
to rank casts of `A` or `B`. -/
theorem exists_filtration_binary
    (hL : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    {a b d : ℕ} (hd : d ≤ a + b) (hd0 : 0 < d) (hd1 : d < a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B) :
    letI := T.topology
    ∃ (n : ℕ) (s : ObjectRepFiltration (SmoothRep.toRep.obj
        ((generalLinearDerivative T ψ (a + b) d hd).obj
          ((T.binaryNormalizedProductFunctor a b).obj (A, B)))) n),
      ∀ i, Subsingleton (s.gradedRepresentation i) ∨
        (∃ h : a = a + b - d, Nonempty (((generalLinearRankCast T h).obj A).representation.Equiv
          (s.gradedRepresentation i).ρ)) ∨
        (∃ h : b = a + b - d, Nonempty (((generalLinearRankCast T h).obj B).representation.Equiv
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
      (generalLinearDerivative T ψ (k + (l + 1)) d hd.2).obj
        ((T.binaryNormalizedProductFunctor k (l + 1)).obj (ρ.obj, ρ'.obj)) := by
  let _ := T.topology
  rw [binaryNormalizedProductFunctor_obj_eq_twoBlocks F T hk l.succ_pos]
  exact (generalLinearDerivative_obj_eq_restriction T ψ (k + l) d hd.2 hd _).symm

/-- `TwoBlockDerivativePieces` follows from the published statements
`GeneralLinearDerivativeLeibnizFiltrationStatement` and `SupercuspidalDerivatives`. -/
theorem twoBlockDerivativePieces_of_leibniz
    (hL : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (hSD : SupercuspidalDerivatives.{uF, uV} F T) :
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

/-- Ze80 Proposition 1.11(a), conditional on the published exactness, detection,
BZ77 3.8, Leibniz filtration and `SupercuspidalDerivatives` statements. -/
theorem nonadjacent_of_leibniz
    (hE : GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T)
    (hPL : MirabolicDerivativeDetection.{uF, max uF uV} F T)
    (hHP : MirabolicHighestDerivativePairingStatement.{uF, max uF uV, max uF uV} F T)
    (hL : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (hSD : SupercuspidalDerivatives.{uF, uV} F T) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_twoBlockDerivativePieces F T hE hPL hHP
    (twoBlockDerivativePieces_of_leibniz F T hL hSD)

/-- Ze80 Proposition 1.11(a), with detection and BZ77 3.8 discharged by their published
proofs `Mirabolic.derivativeDetection` and `mirabolicHighestDerivativePairing`; still
conditional on the exactness, Leibniz filtration and `SupercuspidalDerivatives` statements. -/
theorem nonadjacent_of_exactness_leibniz
    (hE : GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T)
    (hL : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (hSD : SupercuspidalDerivatives.{uF, uV} F T) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_leibniz F T hE (Mirabolic.derivativeDetection F T)
    (mirabolicHighestDerivativePairing F T) hL hSD

/-- Ze80 Proposition 1.11(a), with `SupercuspidalDerivatives` also discharged by its
published proof `supercuspidalDerivatives`; still conditional on the exactness and
Leibniz filtration statements. -/
theorem nonadjacent_of_exactness_leibnizFiltration
    (hE : GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T)
    (hL : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_exactness_leibniz F T hE hL (supercuspidalDerivatives F T)

/-- Ze80 Proposition 1.11(a), with exactness also discharged by its published proof
`Derivative.generalLinearDerivativeExactness` (at carrier universe `max uF uV`); still
conditional on the Leibniz filtration statement. -/
theorem nonadjacent_of_leibnizFiltration
    (hL : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T :=
  nonadjacent_of_exactness_leibnizFiltration F T
    (Derivative.generalLinearDerivativeExactness.{uF, max uF uV} F T) hL

end Langlands.Classification.NonadjacentAssembly
