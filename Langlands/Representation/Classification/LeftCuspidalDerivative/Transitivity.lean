import Langlands.Representation.Classification.LeftCuspidalDerivative.Pieces
import Langlands.Representation.Parabolic.OrderedTensorOccurrences
import Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentReduction

/-!
# Transitivity of first-block Jacquet constituents

* `exists_family_of_isSubquotient_block`: an irreducible subquotient of the restriction to one
  block of a normalized Jacquet module of a finite-length representation is (equivalent to) the
  corresponding factor of an irreducible admissible family whose external tensor product is a
  subquotient of the whole Jacquet module.
* `isFirstBlockConstituent_trans`: if `ρ` is an irreducible first-block Jacquet constituent of a
  finite-length `Y`, and `σ` an irreducible first-block Jacquet constituent of `ρ`, then `σ` is a
  first-block Jacquet constituent of `Y`. The proof passes through the three-block Jacquet
  module `r_(b,l,k)(Y)`, with the two bracketings `((b,l),k)` and `(b,(l,k))`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport BinaryGeometricPieces

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- **Factorization of a block constituent.** An irreducible subquotient `ρ` of the
restriction to the block `j₀` of the normalized Jacquet module `r_D(Y)` of a finite-length `Y`
is equivalent to the factor in the block `j₀` of an irreducible admissible family `X` whose
external tensor product is a subquotient of `r_D(Y)`. -/
theorem exists_family_of_isSubquotient_block {m : ℕ} (hm : 0 < m) (D : BlockShape m)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hY : letI := T.topology; Y.HasFiniteLength) (j₀ : Fin D.length)
    (ρ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (D.size j₀) F.Carrier))
    (hρ : letI := T.topology; ρ.IsIrreducible)
    (h : letI := T.topology
      WeylBranchPieces.IsSubquotient
        ((T.normalizedJacquet D Y.representation).comp
          (MonoidHom.mulSingle (fun i => GeneralLinear (D.size i) F.Carrier) j₀))
        ρ.representation) :
    letI := T.topology
    ∃ X : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier),
      (∀ i, (X i).IsIrreducible) ∧ (∀ i, (X i).IsAdmissible) ∧
      Nonempty ((X j₀).representation.Equiv ρ.representation) ∧
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
        ((T.normalizedJacquetFunctor D).obj Y) := by
  let := T.topology
  let W := (T.normalizedJacquetFunctor.{uF, max uF uV} D).obj Y
  have hW : W.HasFiniteLength :=
    (Parabolic.normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 m D Y hY
  have hcont : Continuous
      (MonoidHom.mulSingle (fun i => GeneralLinear (D.size i) F.Carrier) j₀) := by
    exact continuous_mulSingle (A := fun i : Fin D.length => GeneralLinear (D.size i) F.Carrier) j₀
  have h' : SmoothRep.IsSubquotient ρ
      ((restrictionFunctor (MonoidHom.mulSingle (fun i => GeneralLinear (D.size i) F.Carrier) j₀)
        hcont).obj W) :=
    SmoothRep.isSubquotient_iff_representation.mpr h
  obtain ⟨Z, hZ, hZW, hρZ⟩ := exists_irreducible_of_isSubquotient_map_of_finiteLength
    (restrictionFunctor_preservesFiniteLengthShortExact _ hcont) hW hρ h'
  have hZa : Z.IsAdmissible :=
    CuspidalSupport.irreducibleLeviAdmissibility.{uF, max uF uV} F T m D Z hZ
  obtain ⟨X, hXi, hXa, ⟨eX⟩⟩ := CuspidalSupport.padicLeviAdmissibleFactorization.{uF, max uF uV}
    p F T m hm D Z hZ hZa
  refine ⟨X, hXi, hXa, ?_, ?_⟩
  · have h1 : WeylBranchPieces.IsSubquotient
        (Z.representation.comp
          (MonoidHom.mulSingle (fun i => GeneralLinear (D.size i) F.Carrier) j₀))
        ρ.representation :=
      SmoothRep.isSubquotient_iff_representation.mp hρZ
    have h2 := WeylBranchPieces.IsSubquotient.of_equiv_left
      (FiniteTensorFiltration.compCongr eX.symm
        (MonoidHom.mulSingle (fun i => GeneralLinear (D.size i) F.Carrier) j₀)) h1
    have h3 := isSubquotient_factor_of_external_comp_mulSingle
      (H := fun i => GeneralLinear (D.size i) F.Carrier)
      (fun i => (X i).representation) j₀ ρ.representation hρ h2
    exact CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient (hXi j₀) hρ h3
  · exact SmoothRep.IsSubquotient.of_iso_left
      (SmoothRep.mkIso (B := FiniteTensor.externalSmoothObject X) eX) hZW

/-- The normalized Jacquet module along a one-block shape contains the rank-transported
representation as a subquotient (it is equivalent to it). -/
theorem isSubquotient_singleBlock_jacquet {n : ℕ} (D : BlockShape n) (hD : D.length = 1)
    (Y : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun j =>
      ((D.singleBlock_size hD j).symm ▸ Y :
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size j) F.Carrier))))
      ((T.normalizedJacquetFunctor.{uF, uV} D).obj Y) := by
  let := T.topology
  exact SmoothRep.isSubquotient_iff_representation.mpr
    (WeylBranchPieces.IsSubquotient.of_equiv (T.singleBlockNormalizedJacquetTensorEquiv D hD Y))

/-- The three representations on the blocks of the three-block shape `(b, l, k)`. -/
def threeBlockFactors {b l k : ℕ} (hb : 0 < b) (hl : 0 < l) (hk : 0 < k)
    (A₀ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (A₁ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear l F.Carrier))
    (A₂ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) :
    letI := T.topology
    ∀ i : Fin (Parabolic.threeBlocksRight b l k hb hl hk).length,
      SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((Parabolic.threeBlocksRight b l k hb hl hk).size i) F.Carrier) :=
  Fin.cases A₀ (Fin.cases A₁ (Fin.cases A₂ finZeroElim))

/-- A first-block constituent of a one-block Jacquet module is a subquotient of the
representation. -/
theorem isSubquotient_of_oneBlock {b : ℕ} (hb : 0 < b)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (Z : letI := T.topology
      ∀ j : Fin (LeviAdmissibility.oneBlock b hb).length,
        SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear ((LeviAdmissibility.oneBlock b hb).size j) F.Carrier))
    (hZ : letI := T.topology; ∀ j, (Z j).IsIrreducible)
    (h : letI := T.topology
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject Z)
        ((T.normalizedJacquetFunctor (LeviAdmissibility.oneBlock b hb)).obj X)) :
    letI := T.topology
    WeylBranchPieces.IsSubquotient X.representation (Z ⟨0, Nat.one_pos⟩).representation := by
  let := T.topology
  have hF := isFirstBlockConstituent_of_isSubquotient_jacquet.{uF, uV} T X
    (LeviAdmissibility.oneBlock b hb) (by simp [LeviAdmissibility.oneBlock]) Z hZ h
    ⟨0, Nat.one_pos⟩ rfl
  rcases hF with ⟨hm, hsub⟩ | ⟨k', -, hk', hsum, -⟩
  · exact hsub
  · change b + k' = b at hsum
    omega

/-- **The main case of transitivity**, with explicit two-block shapes. -/
theorem isFirstBlockConstituent_trans_main {b l k : ℕ} (hb : 0 < b) (hl : 0 < l) (hk : 0 < k)
    (ha : 0 < b + l)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (b + l + k) F.Carrier))
    (hY : letI := T.topology; Y.HasFiniteLength)
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (b + l) F.Carrier))
    (hρ : letI := T.topology; ρ.IsIrreducible)
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (h₁ : letI := T.topology
      WeylBranchPieces.IsSubquotient
        ((T.normalizedJacquet (BlockShape.ofPair (b + l) k ha hk rfl) Y.representation).comp
          (MonoidHom.mulSingle
            (fun i => GeneralLinear ((BlockShape.ofPair (b + l) k ha hk rfl).size i) F.Carrier)
            (0 : Fin 2)))
        ρ.representation)
    (h₂ : letI := T.topology
      WeylBranchPieces.IsSubquotient
        ((T.normalizedJacquet (BlockShape.ofPair b l hb hl rfl) ρ.representation).comp
          (MonoidHom.mulSingle
            (fun i => GeneralLinear ((BlockShape.ofPair b l hb hl rfl).size i) F.Carrier)
            (0 : Fin 2)))
        σ.representation) :
    IsFirstBlockConstituent.{uF, uV} F T Y σ := by
  let := T.topology
  -- The factor `ρ ⊠ τ` of `r_(b+l,k)(Y)`.
  obtain ⟨X, hXi, hXa, ⟨eX⟩, hX⟩ := exists_family_of_isSubquotient_block.{uF, uV} T (by omega)
    (BlockShape.ofPair (b + l) k ha hk rfl) Y hY (0 : Fin 2) ρ hρ h₁
  -- The factor `σ ⊠ ρ'` of `r_(b,l)(ρ)`, transported to `X (0 : Fin 2)`.
  obtain ⟨Z, hZi, hZa, ⟨eZ⟩, hZ⟩ := exists_family_of_isSubquotient_block.{uF, uV} T (by omega)
    (BlockShape.ofPair b l hb hl rfl) ρ (SmoothRep.hasFiniteLength_of_isIrreducible hρ)
    (0 : Fin 2) σ hσ h₂
  have hZ' : SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject Z)
      ((T.normalizedJacquetFunctor (BlockShape.ofPair b l hb hl rfl)).obj (X (0 : Fin 2))) :=
    SmoothRep.IsSubquotient.of_iso_right hZ
      ((T.normalizedJacquetFunctor (BlockShape.ofPair b l hb hl rfl)).mapIso
        (SmoothRep.mkIso (B := X (0 : Fin 2)) eX.symm))
  -- The three-block factor `σ ⊠ ρ' ⊠ τ` of `r_(b,l,k)(Y)`.
  let B₃ := Parabolic.threeBlocksRight b l k hb hl hk
  let A := threeBlockFactors T hb hl hk (Z (0 : Fin 2)) (Z (1 : Fin 2)) (X (1 : Fin 2))
  have hAi : ∀ i, (A i).IsIrreducible := by
    intro i
    fin_cases i
    · exact hZi (0 : Fin 2)
    · exact hZi (1 : Fin 2)
    · exact hXi (1 : Fin 2)
  have hAa : ∀ i, (A i).IsAdmissible := by
    intro i
    fin_cases i
    · exact hZa (0 : Fin 2)
    · exact hZa (1 : Fin 2)
    · exact hXa (1 : Fin 2)
  have g0 : SmoothRep.IsSubquotient
      (Parabolic.orderedRefinementTensorFactors F T B₃
        (Shahidi.twoBlocks (b + l) k ha hk) (Parabolic.rightRefinement b l k hb hl hk)
        (Parabolic.rightLabelEquiv b l k hb hl hk)
        (Parabolic.rightLabelEquiv_size b l k hb hl hk) A (0 : Fin 2))
      ((T.normalizedJacquetFunctor (Parabolic.rightRefinement b l k hb hl hk (0 : Fin 2))).obj
        (X (0 : Fin 2))) := by
    have hfam : Parabolic.orderedRefinementTensorFactors F T B₃
        (Shahidi.twoBlocks (b + l) k ha hk) (Parabolic.rightRefinement b l k hb hl hk)
        (Parabolic.rightLabelEquiv b l k hb hl hk)
        (Parabolic.rightLabelEquiv_size b l k hb hl hk) A (0 : Fin 2) =
        FiniteTensor.externalSmoothObject Z := by
      unfold Parabolic.orderedRefinementTensorFactors
      congr 1
      funext j
      fin_cases j <;> rfl
    rw [hfam]
    exact hZ'
  have g1 : SmoothRep.IsSubquotient
      (Parabolic.orderedRefinementTensorFactors F T B₃
        (Shahidi.twoBlocks (b + l) k ha hk) (Parabolic.rightRefinement b l k hb hl hk)
        (Parabolic.rightLabelEquiv b l k hb hl hk)
        (Parabolic.rightLabelEquiv_size b l k hb hl hk) A (1 : Fin 2))
      ((T.normalizedJacquetFunctor (Parabolic.rightRefinement b l k hb hl hk (1 : Fin 2))).obj
        (X (1 : Fin 2))) := by
    have hfam : Parabolic.orderedRefinementTensorFactors F T B₃
        (Shahidi.twoBlocks (b + l) k ha hk) (Parabolic.rightRefinement b l k hb hl hk)
        (Parabolic.rightLabelEquiv b l k hb hl hk)
        (Parabolic.rightLabelEquiv_size b l k hb hl hk) A (1 : Fin 2) =
        FiniteTensor.externalSmoothObject (fun j =>
          (((Parabolic.rightRefinement b l k hb hl hk (1 : Fin 2)).singleBlock_size rfl j).symm ▸
              X (1 : Fin 2) :
            SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
              ((Parabolic.rightRefinement b l k hb hl hk (1 : Fin 2)).size j) F.Carrier))) := by
      unfold Parabolic.orderedRefinementTensorFactors
      congr 1
    rw [hfam]
    exact isSubquotient_singleBlock_jacquet.{uF, max uF uV} T
      (Parabolic.rightRefinement b l k hb hl hk (1 : Fin 2)) rfl (X (1 : Fin 2))
  have hA3 : SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject A)
      ((T.normalizedJacquetFunctor B₃).obj Y) := by
    refine Parabolic.subquotient_orderedJacquet_of_coarse_factors.{uF, max uF uV} F T B₃
      (Shahidi.twoBlocks (b + l) k ha hk) (Parabolic.rightRefinement b l k hb hl hk)
      (Parabolic.rightLabelEquiv b l k hb hl hk) (Parabolic.rightLabelEquiv_size b l k hb hl hk)
      (Parabolic.rightLabelEquiv_lex b l k hb hl hk) Y X A hX ?_
    intro i
    fin_cases i
    · exact g0
    · exact g1
  -- The coarse factor `X' 0 ⊠ X' 1` of `r_(b,l+k)(Y)`, with `σ` a subquotient of `X' 0`.
  have hYa : Y.IsAdmissible := (finiteLengthAdmissibility.{uF, max uF uV} F T).1 _ Y hY
  obtain ⟨X', hX'i, -, -, hX', hX'0⟩ :=
    Parabolic.exists_factorized_coarseJacquet_of_ordered.{uF, max uF uV} F T B₃
      (BlockShape.ofPair b (l + k) hb (Nat.add_pos_left hl k) (Nat.add_assoc b l k).symm)
      (Parabolic.leftRefinement b l k hb hl hk) (Parabolic.leftLabelEquiv b l k hb hl hk)
      (Parabolic.leftLabelEquiv_size b l k hb hl hk) (Parabolic.leftLabelEquiv_lex b l k hb hl hk)
      (by omega) Y A hYa hY hAi hAa hA3
  have h00 := hX'0 (0 : Fin 2)
  have hfam0 : Parabolic.orderedRefinementTensorFactors F T B₃
      (BlockShape.ofPair b (l + k) hb (Nat.add_pos_left hl k) (Nat.add_assoc b l k).symm)
      (Parabolic.leftRefinement b l k hb hl hk) (Parabolic.leftLabelEquiv b l k hb hl hk)
      (Parabolic.leftLabelEquiv_size b l k hb hl hk) A (0 : Fin 2) =
      FiniteTensor.externalSmoothObject (fun j =>
        (((LeviAdmissibility.oneBlock b hb).singleBlock_size rfl j).symm ▸ Z (0 : Fin 2) :
          SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear ((LeviAdmissibility.oneBlock b hb).size j) F.Carrier))) := by
    unfold Parabolic.orderedRefinementTensorFactors
    congr 1
  rw [hfam0] at h00
  have hsub : WeylBranchPieces.IsSubquotient (X' (0 : Fin 2)).representation
      (Z (0 : Fin 2)).representation :=
    isSubquotient_of_oneBlock.{uF, uV} T hb (X' (0 : Fin 2)) _
      (fun j => by fin_cases j; exact hZi (0 : Fin 2)) h00
  have hσX : WeylBranchPieces.IsSubquotient (X' (0 : Fin 2)).representation σ.representation :=
    hsub.of_equiv_right eZ
  have hF := isFirstBlockConstituent_of_isSubquotient_jacquet.{uF, uV} T Y
    (BlockShape.ofPair b (l + k) hb (Nat.add_pos_left hl k) (Nat.add_assoc b l k).symm)
    (by simp) X' hX'i hX' (0 : Fin 2) rfl
  exact isFirstBlockConstituent_of_isSubquotient T hF hσX

/-- **Transitivity of first-block Jacquet constituents.** -/
theorem isFirstBlockConstituent_trans {m a b : ℕ}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hY : letI := T.topology; Y.HasFiniteLength)
    {ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hρ : letI := T.topology; ρ.IsIrreducible)
    {σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    (hσ : letI := T.topology; σ.IsIrreducible)
    (h₁ : IsFirstBlockConstituent.{uF, uV} F T Y ρ)
    (h₂ : IsFirstBlockConstituent.{uF, uV} F T ρ σ) :
    IsFirstBlockConstituent.{uF, uV} F T Y σ := by
  let := T.topology
  rcases h₁ with ⟨rfl, h₁⟩ | ⟨k, ha, hk, rfl, h₁⟩
  · rcases h₂ with ⟨rfl, h₂⟩ | ⟨l, hb, hl, rfl, h₂⟩
    · exact Or.inl ⟨rfl, h₁.trans h₂⟩
    · refine Or.inr ⟨l, hb, hl, rfl, ?_⟩
      have hJ := CuspidalSupport.normalizedJacquetSubquotient.{uF, max uF uV} p F T _
        (BlockShape.ofPair b l hb hl rfl) Y ρ (SmoothRep.isSubquotient_iff_representation.mpr h₁)
      exact ((SmoothRep.isSubquotient_iff_representation.mp hJ).comp _).trans h₂
  · rcases h₂ with ⟨rfl, h₂⟩ | ⟨l, hb, hl, rfl, h₂⟩
    · exact Or.inr ⟨k, ha, hk, rfl, h₁.trans h₂⟩
    · exact isFirstBlockConstituent_trans_main.{uF, uV} T hb hl hk ha Y hY ρ hρ σ hσ h₁ h₂

end Langlands.Classification.LeftCuspidalDerivative
