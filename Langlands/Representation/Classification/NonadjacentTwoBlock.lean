import Langlands.Representation.Classification.NonadjacentSpecialization

/-! The BZ77 Theorem 4.2 core applied to the two-block product `ρ × ρ'` of
supercuspidal representations.

The intermediate proposition `TwoBlockDerivativePieces` records the consequence of
the BZ77 Leibniz rule (Corollary 4.14(c)) and of the derivatives of supercuspidal
representations (BZ77 4.4) that this argument consumes; `NonadjacentLeibnizPieces`
proves it from their published proofs. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.NonadjacentAssembly

open GeneralLinear HarmonicAnalysis Derivative InvariantBilinear ProductDualTwist

universe uF u uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section Pieces

/-- A representation of `GL_m` that is zero or equivalent to the rank cast of
`Φ A` for a supercuspidal `A` whose rank-indexed class lies in `S`. -/
def PieceIn
    (S : letI := T.topology; Set (Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)))
    (Φ : ∀ a : ℕ, (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) →
      (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)))
    {m : ℕ} (X : letI := T.topology; Rep.{u} ℂ (GeneralLinear m F.Carrier)) : Prop :=
  letI := T.topology
  Subsingleton X ∨ ∃ (a : ℕ) (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a))
    (h : a = m),
      (⟨a, A.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ∈ S ∧
      Nonempty (((generalLinearRankCast T h).obj (Φ a A).obj).representation.Equiv X.ρ)

/-- If no class of `S` is the `ν`-twist of a class of `S`, a piece built from `S`
carries no invariant form against a piece built from the `ν`-twisted duals of `S`. -/
theorem length_eq_zero_of_pieceIn
    (S : letI := T.topology; Set (Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)))
    (hS : ∀ x ∈ S, ∀ y ∈ S, y ≠ ⟨x.1, T.supercuspidalClassRealPowerTwist x.1 1 x.2⟩)
    {m : ℕ} (X Y : letI := T.topology; Rep.{u} ℂ (GeneralLinear m F.Carrier))
    (hX : PieceIn F T S (fun _ A => A) X) (hY : PieceIn F T S (fun _ B => dualTwist F T B) Y) :
    length X.ρ Y.ρ (fun _ => (1 : ℂ)) = 0 := by
  let _ := T.topology
  rcases hX with hX | ⟨a, A, h1, hA, ⟨e1⟩⟩
  · exact length_eq_zero_of_subsingleton_left _ _ _
  rcases hY with hY | ⟨b, B, h2, hB, ⟨e2⟩⟩
  · rw [length_flip]
    exact length_eq_zero_of_subsingleton_left _ _ _
  rw [← length_congr_left _ _ e1, length_flip, ← length_congr_left _ _ e2, length_flip]
  by_contra hne
  exact hS _ hA _ hB (twist_class_eq_of_length_ne_zero F T A B h1 h2 hne)

end Pieces

section TwoBlock

/-- The two-block shape `(k, l+1)`, with its rank written `k + l + 1`. -/
abbrev twoBlocksSucc (k l : ℕ) (hk : 0 < k) : BlockShape (k + l + 1) :=
  Shahidi.twoBlocks k (l + 1) hk l.succ_pos

/-- The normalized product `ρ × ρ'` on `GL_(k+l+1)`, for `ρ` on `GL_k` and `ρ'`
on `GL_(l+1)`. -/
abbrev twoBlockProduct {k l : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (k + l + 1) F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (twoBlocksSucc k l hk)).obj
    (twoBlockFactors hk l.succ_pos ρ.obj ρ'.obj)

/-- `ρ × ρ'` in the form of the target statement, on the shape
`Shahidi.twoBlocks k (l+1)` of rank `k + (l + 1)`. -/
abbrev twoBlockProductRaw {k l : ℕ} (hk : 0 < k) (hl : 0 < l + 1)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (k + l + 1) F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k (l + 1) hk hl)).obj
    (twoBlockFactors hk hl ρ.obj ρ'.obj)

/-- Consequence of the BZ77 Leibniz rule (Corollary 4.14(c)) and of the derivatives
of supercuspidal representations (BZ77 4.4), proved in `NonadjacentLeibnizPieces`:
the top derivative of
`ρ × ρ'` is one-dimensional, and at every intermediate order `d` its derivative has
a filtration whose graded pieces are zero, or equivalent to `ρ` (possible only when
`d = l+1`), or equivalent to `ρ'` (possible only when `d = k`). -/
def TwoBlockDerivativePieces : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k l : ℕ) (hk : 0 < k)
    (ρ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1)),
    Module.finrank ℂ ((restrictedDerivative F T ψ (k + l) (k + l + 1)
      ⟨Nat.succ_pos _, le_rfl⟩).obj (twoBlockProduct F T hk ρ ρ')) = 1 ∧
    ∀ (d : ℕ) (hd : 0 < d ∧ d ≤ k + l + 1), d < k + l + 1 →
      ∃ (m : ℕ) (s : ObjectRepFiltration
        ((restrictedDerivative F T ψ (k + l) d hd).obj (twoBlockProduct F T hk ρ ρ')).obj m),
        ∀ i, Subsingleton (s.gradedRepresentation i) ∨
          (∃ h : k = k + l + 1 - d, Nonempty
            (((generalLinearRankCast T h).obj ρ.obj).representation.Equiv
              (s.gradedRepresentation i).ρ)) ∨
          (∃ h : l + 1 = k + l + 1 - d, Nonempty
            (((generalLinearRankCast T h).obj ρ'.obj).representation.Equiv
              (s.gradedRepresentation i).ρ))

/-- Rank casts preserve irreducibility. -/
theorem isIrreducible_rankCast {a b : ℕ} (h : a = b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) :
    letI := T.topology; ((generalLinearRankCast T h).obj A).IsIrreducible := by
  subst h
  exact hA

/-- A piece built from supercuspidal classes is zero or irreducible. -/
theorem zeroOrIrreducible_of_pieceIn
    (S : letI := T.topology; Set (Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)))
    (Φ : ∀ a : ℕ, (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) →
      (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)))
    {m : ℕ} (X : letI := T.topology; Rep.{u} ℂ (GeneralLinear m F.Carrier))
    (hX : PieceIn F T S Φ X) : ZeroOrIrreducible X.ρ := by
  let _ := T.topology
  rcases hX with hX | ⟨a, A, h, -, ⟨e⟩⟩
  · exact Or.inl hX
  · exact Or.inr (LengthTwo.isIrreducible_of_equiv e
      (isIrreducible_rankCast F T h (Φ a A).obj (Φ a A).property.1))

/-- Pieces are stable under equivalence. -/
theorem pieceIn_of_equiv
    (S : letI := T.topology; Set (Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)))
    (Φ : ∀ a : ℕ, (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) →
      (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)))
    {m : ℕ} {X Y : letI := T.topology; Rep.{u} ℂ (GeneralLinear m F.Carrier)}
    (e : X.ρ.Equiv Y.ρ) (hX : PieceIn F T S Φ X) : PieceIn F T S Φ Y := by
  let _ := T.topology
  rcases hX with hX | ⟨a, A, h, hA, ⟨e'⟩⟩
  · exact Or.inl e.toLinearEquiv.symm.subsingleton
  · exact Or.inr ⟨a, A, h, hA, ⟨e'.trans e⟩⟩

/-- `TwoBlockDerivativePieces` places every piece of the derivative of `Φ ρ × Φ ρ'` among
the pieces built from `{ρ, ρ'}` through `Φ`. -/
theorem pieceIn_of_twoBlock {k l : ℕ}
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1))
    (Φ : ∀ a : ℕ, (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) →
      (letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)))
    {m : ℕ} (X : letI := T.topology; Rep.{max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hX : letI := T.topology; Subsingleton X ∨
      (∃ h : k = m, Nonempty
        (((generalLinearRankCast T h).obj (Φ k ρ).obj).representation.Equiv X.ρ)) ∨
      (∃ h : l + 1 = m, Nonempty
        (((generalLinearRankCast T h).obj (Φ (l + 1) ρ').obj).representation.Equiv X.ρ))) :
    PieceIn F T (letI := T.topology; {⟨k, ρ.isoClass⟩, ⟨l + 1, ρ'.isoClass⟩}) Φ X := by
  rcases hX with hX | ⟨h, e⟩ | ⟨h, e⟩
  · exact Or.inl hX
  · exact Or.inr ⟨k, ρ, h, Or.inl rfl, e⟩
  · exact Or.inr ⟨l + 1, ρ', h, Or.inr rfl, e⟩

/-- `ν (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~` as representations, with the rank written
`k + l + 1`. -/
theorem twoBlockDualTwistSucc {k l : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1)) :
    letI := T.topology
    Nonempty ((dualTwistRep F T (twoBlockProduct F T hk ρ ρ')).representation.Equiv
      (twoBlockProduct F T hk (dualTwist F T ρ) (dualTwist F T ρ')).representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + l + 1)
  have hadm : ∀ i, IsAdmissible (twoBlockFactors hk l.succ_pos ρ.obj ρ'.obj i).representation := by
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact ρ.property.2.1
    · exact ρ'.property.2.1
  obtain ⟨e⟩ := productDualTwist F T (twoBlocksSucc k l hk) _ hadm
  have hfam : (fun i => letI := T.generalLinearTopologicalGroup ((twoBlocksSucc k l hk).size i)
      (twoBlockFactors hk l.succ_pos ρ.obj ρ'.obj i).contragredient.twist
        (T.determinantPowerCharacter ((twoBlocksSucc k l hk).size i) 1)
        (T.isOpen_ker_determinantPowerCharacter ((twoBlocksSucc k l hk).size i) 1)) =
      twoBlockFactors hk l.succ_pos (dualTwist F T ρ).obj (dualTwist F T ρ').obj := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> rfl
  rw [hfam] at e
  exact ⟨e⟩

/-- The smooth-category isomorphism `ν (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~`. -/
def twoBlockDualTwistIso {k l : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1)) :
    letI := T.topology
    dualTwistRep F T (twoBlockProduct F T hk ρ ρ') ≅
      twoBlockProduct F T hk (dualTwist F T ρ) (dualTwist F T ρ') :=
  letI := T.topology
  SmoothRep.mkIso (Classical.choice (twoBlockDualTwistSucc F T hk ρ ρ'))

/-- Under `TwoBlockDerivativePieces`, the derivative pieces of `ρ × ρ'` and of `ν (ρ × ρ')~`
carry no invariant forms between them when `ρ, ρ'` are nonadjacent. -/
theorem piecesWithoutForms_twoBlock (hLP : TwoBlockDerivativePieces.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {k l : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l + 1))
    (h1 : letI := T.topology
      (⟨l + 1, ρ'.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨k, T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass⟩)
    (h2 : letI := T.topology
      (⟨k, ρ.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨l + 1, T.supercuspidalClassRealPowerTwist (l + 1) 1 ρ'.isoClass⟩) :
    PiecesWithoutForms F T ψ (k + l) (twoBlockProduct F T hk ρ ρ') := by
  let _ := T.topology
  let S : Set (Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) :=
    {⟨k, ρ.isoClass⟩, ⟨l + 1, ρ'.isoClass⟩}
  have hS : ∀ x ∈ S, ∀ y ∈ S, y ≠ ⟨x.1, T.supercuspidalClassRealPowerTwist x.1 1 x.2⟩ := by
    rintro x (rfl | rfl) y (rfl | rfl)
    · exact sigma_ne_twist F T hk ρ
    · exact h1
    · exact h2
    · exact sigma_ne_twist F T l.succ_pos ρ'
  intro d hd hdlt
  let D := restrictedDerivative.{uF, max uF uV} F T ψ (k + l) d hd
  obtain ⟨m, s, hs⟩ := (hLP ψ k l hk ρ ρ').2 d hd hdlt
  obtain ⟨n, t0, ht0⟩ := (hLP ψ k l hk (dualTwist F T ρ) (dualTwist F T ρ')).2 d hd hdlt
  let e := SmoothRep.equivOfIso (D.mapIso (twoBlockDualTwistIso F T hk ρ ρ').symm)
  let t := LengthTwo.transport e t0
  have hsP : ∀ i, PieceIn F T S (fun _ A => A) (s.gradedRepresentation i) :=
    fun i => pieceIn_of_twoBlock F T ρ ρ' (fun _ A => A) _ (hs i)
  have htP : ∀ j, PieceIn F T S (fun _ B => dualTwist F T B) (t.gradedRepresentation j) :=
    fun j => pieceIn_of_equiv F T S _ (ObjectRepFiltration.equivTransportGradedEquiv t0 e j)
      (pieceIn_of_twoBlock F T ρ ρ' (fun _ B => dualTwist F T B) _ (ht0 j))
  exact ⟨m, n, s, t, fun i => zeroOrIrreducible_of_pieceIn F T S _ _ (hsP i),
    fun j => zeroOrIrreducible_of_pieceIn F T S _ _ (htP j),
    fun i j => length_eq_zero_of_pieceIn F T S hS _ _ (hsP i) (htP j)⟩

end TwoBlock

/-- Ze80 Proposition 1.11(a), conditional on the published exactness, detection and
BZ77 3.8 statements and on `TwoBlockDerivativePieces`. -/
theorem nonadjacent_of_twoBlockDerivativePieces
    (hE : GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T)
    (hPL : MirabolicDerivativeDetection.{uF, max uF uV} F T)
    (hHP : MirabolicHighestDerivativePairingStatement.{uF, max uF uV, max uF uV} F T)
    (hLP : TwoBlockDerivativePieces.{uF, uV} F T) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T := by
  intro k l hk hl ρ ρ' h1 h2
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  obtain ⟨ψ⟩ := padicUnitaryAdditiveCharacterExists F T
  have h := irreducible_of_pieces F T hE hPL hHP ψ (k + l) (twoBlockProduct F T hk ρ ρ')
    (hLP ψ k l hk ρ ρ').1 (piecesWithoutForms_twoBlock F T hLP ψ hk ρ ρ' h1 h2)
  have e : twoBlockProduct F T hk ρ ρ' = twoBlockProductRaw F T hk hl ρ ρ' := rfl
  rw [e] at h
  exact h

end Langlands.Classification.NonadjacentAssembly
