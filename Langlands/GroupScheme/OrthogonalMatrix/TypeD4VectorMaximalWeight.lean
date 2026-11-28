import Langlands.GroupScheme.OrthogonalMatrix.NumberedCoverVectorProof
import Langlands.GroupScheme.Reductive.AdjointWeightBasis
import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.Reductive.IntegralWeylVector

/-! # The maximal vector weight of an aligned split D4 cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)
  (e : p.base.support ≃ Fin 4)

private theorem vectorWeight_zero_eq_fundamental
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (hCartan : ∀ a b : p.base.support,
      p.rootDatum.pairing a.val b.val = CartanMatrix.D 4 (e a) (e b))
    (ε : Fin 4 → characterLattice p.torus)
    (h₀ : p.rootDatum.root (e.symm 0).val = ε 0 - ε 1)
    (h₁ : p.rootDatum.root (e.symm 1).val = ε 1 - ε 2)
    (h₂ : p.rootDatum.root (e.symm 2).val = ε 2 - ε 3)
    (h₃ : p.rootDatum.root (e.symm 3).val = ε 2 + ε 3) :
    ε 0 = Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan (e.symm 0) := by
  classical
  apply IntegralWeylVector.eq_of_pairing_simple_eq p.rootDatum p.base hspan
  intro a
  let j := e a
  have ha : a = e.symm j := (e.symm_apply_apply a).symm
  rw [ha]
  clear ha
  let f := p.rootDatum.toLinearMap.flip (p.rootDatum.coroot (e.symm j).val)
  have hroot (i : Fin 4) : f (p.rootDatum.root (e.symm i).val) = CartanMatrix.D 4 i j := by
    change p.rootDatum.pairing (e.symm i).val (e.symm j).val = _
    simpa only [Equiv.apply_symm_apply] using hCartan (e.symm i) (e.symm j)
  have h0 : f (ε 0) - f (ε 1) = CartanMatrix.D 4 0 j := by
    simpa only [h₀, map_sub] using hroot 0
  have h1 : f (ε 1) - f (ε 2) = CartanMatrix.D 4 1 j := by
    simpa only [h₁, map_sub] using hroot 1
  have h2 : f (ε 2) - f (ε 3) = CartanMatrix.D 4 2 j := by
    simpa only [h₂, map_sub] using hroot 2
  have h3 : f (ε 2) + f (ε 3) = CartanMatrix.D 4 3 j := by
    simpa only [h₃, map_add] using hroot 3
  rw [Langlands.RootDatum.fundamentalWeightBasis_pairing]
  change f (ε 0) = if e.symm j = e.symm 0 then 1 else 0
  simp only [Equiv.apply_eq_iff_eq]
  have h : ∀ i : Fin 4, (2 * (CartanMatrix.D 4 0 i + CartanMatrix.D 4 1 i) +
      CartanMatrix.D 4 2 i + CartanMatrix.D 4 3 i) = if i = 0 then 2 else 0 := by decide
  have hsum := h j
  by_cases hj : j = 0
  · rw [ite_eq_left hj] at hsum ⊢
    omega
  · rw [ite_eq_right hj] at hsum ⊢
    omega

/-- The actual dual vector representation pulled back to an aligned split
D4 cover has the vector fundamental weight as a maximal weight of
multiplicity one. -/
def TypeD4VectorMaximalWeightStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (p : SplitPinning G),
    let S := OrthogonalMatrix.groupScheme (Fin 4) (CommRingCat.of k)
    haveI := OrthogonalMatrix.smooth_groupScheme (Fin 4) (CommRingCat.of k)
    haveI := OrthogonalMatrix.isAffineHom_groupScheme (Fin 4) (CommRingCat.of k)
    ∀ (pi : G ⟶ identityComponent S) (e : p.base.support ≃ Fin 4),
      IsSimplyConnected G → IsCentralIsogeny pi →
      (∀ a b : p.base.support,
        p.rootDatum.pairing a.val b.val = CartanMatrix.D 4 (e a) (e b)) →
      (∀ v : p.base.support, (e v).val = 0 →
        ∀ chi : characterLattice p.torus,
          latticePairing _ chi (p.rootDatum.coroot v.val) = 1 →
          (∀ w : p.base.support, w ≠ v → latticePairing _ chi (p.rootDatum.coroot w.val) = 0) →
          ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ p.torus.X),
            t ≫ (p.inclusion ≫ pi).hom.hom = 1 →
            t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1) →
      ∀ hspan : p.rootDatum.corootSpan ℤ = ⊤,
        let r := MatrixRepresentation.dual
          (pi ≫ identityComponentι S ≫ inclusion (Fin 4) (CommRingCat.of k))
        let weight := Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan (e.symm 0)
        Module.finrank k (p.representationWeightSpace r weight) = 1 ∧
          ∀ χ, p.representationWeightSpace r χ ≠ ⊥ →
            χ - weight ∈ p.positiveRootMonoid → χ = weight

set_option maxHeartbeats 1800000 in
theorem typeD4VectorMaximalWeight : TypeD4VectorMaximalWeightStatement.{u} := by
  classical
  intro k _ G _ p S pi e hsc hpi hCartan hAlign hspan r weight
  let : Smooth S.X.hom := OrthogonalMatrix.smooth_groupScheme (Fin 4) (CommRingCat.of k)
  let : IsAffineHom S.X.hom := OrthogonalMatrix.isAffineHom_groupScheme (Fin 4) (CommRingCat.of k)
  obtain ⟨ε, hchain, hlast, _, b, hb⟩ := numberedCoverVector k 4 (by decide) G p hsc pi hpi
    e hCartan hAlign
  have h₀ : p.rootDatum.root (e.symm 0).val = ε 0 - ε 1 := by
    simpa only [Equiv.apply_symm_apply] using! hchain (e.symm 0) (by simp)
  have h₁ : p.rootDatum.root (e.symm 1).val = ε 1 - ε 2 := by
    simpa only [Equiv.apply_symm_apply] using! hchain (e.symm 1) (by simp)
  have h₂ : p.rootDatum.root (e.symm 2).val = ε 2 - ε 3 := by
    simpa only [Equiv.apply_symm_apply] using! hchain (e.symm 2) (by simp)
  have h₃ : p.rootDatum.root (e.symm 3).val = ε 2 + ε 3 :=
    hlast (e.symm 3) (by simp)
  have hweight : ε 0 = weight := vectorWeight_zero_eq_fundamental p e hspan hCartan ε h₀ h₁ h₂ h₃
  let s : (Fin 4 × ℤˣ) ≃ Fin 4 ⊕ Fin 4 := signedWeightIndexEquiv
  let B := b.reindex s
  let w (a : Fin 4 ⊕ Fin 4) := ((s.symm a).2 : ℤ) • ε (s.symm a).1
  have hB (a : Fin 4 ⊕ Fin 4) : B a ∈ p.representationWeightSpace r (w a) := by
    rw [p.mem_representationWeightSpace_iff_affine]
    intro R t
    have h := hb R t (s.symm a)
    let M := MatrixRepresentation.affineMatrix
      (pi ≫ identityComponentι S ≫ inclusion (Fin 4) (CommRingCat.of k))
      R (t ≫ p.inclusion.hom.hom)
    rw [show r = MatrixRepresentation.dual
      (pi ≫ identityComponentι S ≫ inclusion (Fin 4) (CommRingCat.of k)) from rfl,
      MatrixRepresentation.dual_affineMatrix, GeneralLinear.matrixContragredient_coe]
    change (((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) R) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) R)ᵀ) *ᵥ _ = _
    rw [Matrix.mulVec_transpose]
    have hval : (Lie.characterValue (w a) t : R) =
        (Gm.affineUnitsEquiv (CommRingCat.of k) R
          (t ≫ (CommGroupScheme.groupHom (w a)).hom.hom) : Rˣ) := by
      dsimp only [Lie.characterValue, Gm.affineUnitsEquiv, Gm.affinePointsEquiv]
      rfl
    rw [hval]
    funext j
    simpa only [B, Module.Basis.reindex_apply, w, M, S, Pi.smul_apply, smul_eq_mul,
      Matrix.GeneralLinearGroup.coe_inv] using! congrFun h j
  let ν := ∑ i : Fin 4, (![16, 24, 13, 15] : Fin 4 → ℤ) i • p.rootDatum.coroot (e.symm i).val
  let f := p.rootDatum.toLinearMap.flip ν
  have hroot (i : Fin 4) : f (p.rootDatum.root (e.symm i).val) =
      (![8, 4, 2, 6] : Fin 4 → ℤ) i := by
    have h : ∀ i : Fin 4, (∑ j : Fin 4, (![16, 24, 13, 15] : Fin 4 → ℤ) j *
        CartanMatrix.D 4 i j) = (![8, 4, 2, 6] : Fin 4 → ℤ) i := by decide
    change p.rootDatum.toLinearMap (p.rootDatum.root (e.symm i).val) ν = _
    simp only [ν, map_sum, map_zsmul, zsmul_eq_mul, RootPairing.root_coroot_eq_pairing,
      hCartan, Equiv.apply_symm_apply]
    exact h i
  have hf0 : f (ε 0) - f (ε 1) = 8 := by simpa only [h₀, map_sub] using! hroot 0
  have hf1 : f (ε 1) - f (ε 2) = 4 := by simpa only [h₁, map_sub] using! hroot 1
  have hf2 : f (ε 2) - f (ε 3) = 2 := by simpa only [h₂, map_sub] using! hroot 2
  have hf3 : f (ε 2) + f (ε 3) = 6 := by simpa only [h₃, map_add] using! hroot 3
  have hf (i : Fin 4) : f (ε i) = (![16, 8, 4, 2] : Fin 4 → ℤ) i := by
    fin_cases i <;> norm_num <;> omega
  have h0 : f weight = 16 := (congrArg f hweight).symm.trans (hf 0)
  have hunique (a : Fin 4 ⊕ Fin 4) (ha : 16 ≤ f (w a)) : a = .inl 0 := by
    obtain ⟨⟨i, t⟩, rfl⟩ := s.surjective a
    change 16 ≤ f (((s.symm (s (i, t))).2 : ℤ) • ε (s.symm (s (i, t))).1) at ha
    simp only [Equiv.symm_apply_apply, map_zsmul, hf, zsmul_eq_mul] at ha
    rcases Int.units_eq_one_or t with rfl | rfl
    · have h : ∀ i : Fin 4, 16 ≤ (![16, 8, 4, 2] : Fin 4 → ℤ) i → i = 0 := by decide
      change 16 ≤ (1 : ℤ) * (![16, 8, 4, 2] : Fin 4 → ℤ) i at ha
      have hi : i = 0 := h i (by simpa only [one_mul] using ha)
      subst i
      simp [s, signedWeightIndexEquiv]
    · have h : ∀ i : Fin 4, ¬ 16 ≤ -(![16, 8, 4, 2] : Fin 4 → ℤ) i := by decide
      exact (h i (by simpa using ha)).elim
  have hw0 : w (.inl 0) = weight := by
    change ((s.symm (Sum.inl 0)).2 : ℤ) • ε (s.symm (Sum.inl 0)).1 = weight
    change (1 : ℤ) • ε 0 = weight
    simpa only [one_zsmul] using hweight
  have hnonneg {χ : characterLattice p.torus} (hχ : χ ∈ p.positiveRootMonoid) : 0 ≤ f χ := by
    induction hχ using AddSubmonoid.closure_induction with
    | mem _ ha =>
      obtain ⟨a, rfl⟩ := ha
      have ha : a = e.symm (e a) := (e.symm_apply_apply a).symm
      rw [ha, hroot]
      generalize e a = i
      fin_cases i <;> decide
    | zero => rw [map_zero]
    | add _ _ _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
  refine ⟨?_, ?_⟩
  · let : Subsingleton {a // w a = weight} := ⟨fun a b =>
      Subtype.ext ((hunique a.val (by rw [a.property, h0])).trans
        (hunique b.val (by rw [b.property, h0])).symm)⟩
    let : Unique {a // w a = weight} := uniqueOfSubsingleton ⟨.inl 0, hw0⟩
    rw [p.finrank_representationWeightSpace_eq_card r B w hB]
    exact Fintype.card_unique
  · intro χ hχ hpos
    have hdim : 0 < Module.finrank k (p.representationWeightSpace r χ) :=
      Nat.pos_of_ne_zero fun h => hχ (Submodule.finrank_eq_zero.mp h)
    rw [p.finrank_representationWeightSpace_eq_card r B w hB] at hdim
    obtain ⟨a, ha⟩ := Fintype.card_pos_iff.mp hdim
    have hh := hnonneg hpos
    rw [map_sub, h0, ← ha] at hh
    rw [hunique a (by omega), hw0] at ha
    exact ha.symm

end Langlands.GroupScheme.OrthogonalMatrix
