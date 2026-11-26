import Langlands.GroupScheme.Rational.BorelInducedSocleAndWeightsStatement
import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationProof
import Langlands.GroupScheme.Rational.HighestWeightRootEndpoint

/-! # Proof: socle and weight bounds of opposite-Borel induction (Milne 22.27(b,c)) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineCoordinates AffineLinearEmbedding Chevalley MatrixRepresentation
open HomogeneousQuotientFromEmbedding

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

private theorem weylWeightFinrank {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (w : p.rootDatum.Aut) (hw : w ∈ p.rootDatum.weylGroup)
    (mu : characterLattice p.torus) :
    finrank k (p.representationWeightSpace ρ (w • mu)) =
      finrank k (p.representationWeightSpace ρ mu) := by
  induction hw using RootPairing.weylGroup.induction generalizing mu with
  | mem i =>
    rw [RootPairing.Equiv.reflection_smul]
    exact p.finrank_representationWeightSpace_root_reflection ρ mu i
  | one => rw [one_smul]
  | mul x y _ _ hx hy => rw [mul_smul, hx, hy]

private theorem negWeylSendsPositive (w : p.rootDatum.weylGroup)
    (hw : ∀ i : p.rootIndex, p.base.IsPos (w.val.indexEquiv i) ↔ ¬ p.base.IsPos i)
    {x : characterLattice p.torus} (hx : x ∈ p.positiveRootMonoid) :
    -(w.val • x) ∈ p.positiveRootMonoid := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [← RootPairing.Equiv.root_indexEquiv_eq_smul]
    let := p.rootDatum.indexNeg
    let i := w.val.indexEquiv a
    have hn : ¬ p.base.IsPos i := fun hi => (hw a).1 hi
      (by rw [RootPairing.Base.isPos_iff, p.base.height_one_of_mem_support a.2]; exact one_pos)
    have hroot : p.rootDatum.root (-i) = -p.rootDatum.root i := by
      change p.rootDatum.root (p.rootDatum.reflectionPerm i i) = -p.rootDatum.root i
      rw [p.rootDatum.root_reflectionPerm, p.rootDatum.reflection_apply_self]
    change -p.rootDatum.root i ∈ p.positiveRootMonoid
    rw [← hroot]
    exact p.root_mem_positiveRootMonoid ((RootPairing.Base.IsPos.neg_iff_not p.base i).2 hn)
  | zero => rw [smul_zero, neg_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add, neg_add_rev]; exact add_mem hy hx

private theorem coordinateInclusionCommutes
    (S V : Submodule k (algebra G)) {d c : ℕ} (bS : Basis (Fin d) k S) (b : Basis (Fin c) k V)
    (hSV : S ≤ V) (x : Fin d → k) :
    letI := (bialgebra (corepresentation G)).toCoalgebra
    affineRegularCoordinateMap G V b ((coactionCoordinates V b
      (fun j => (bS j : algebra G))).mulVecLin x) = affineRegularCoordinateMap G S bS x := by
  let := (bialgebra (corepresentation G)).toCoalgebra
  simp only [affineRegularCoordinateMap_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    coactionCoordinates, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc
    _ = x j • ∑ i, extendedCoord V b i (bS j : algebra G) • (b i : algebra G) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
    _ = x j • (bS j : algebra G) := congrArg (x j • ·) (basis_expand V b (hSV (bS j).2))

section Covariant

variable {lam : characterLattice p.torus} {d : ℕ}
    (V : Submodule k (algebra G)) (b : Basis (Fin d) k V)
    (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
      ∀ (ψ : Module.Dual k (algebra G)) (v : algebra G), v ∈ V → rightAct ψ v ∈ V)
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam))

include hcov in
private theorem covariant_hasUniqueSimpleSubspace {f : algebra G} (hf : p.IsRealizedBy lam f)
    (hSV : affineCovariantSocle G f ≤ V) :
    let ρ := affineRegularRepresentation G V b hV
    ∃ W : Submodule k (Fin d → k),
      ρ.IsSimpleStableSubspace W ∧ (∀ T, ρ.IsSimpleStableSubspace T → T = W) ∧
      ∃ C : StableSubspaceRepresentation ρ W, p.IsHighestWeight C.representation lam := by
  classical
  let := (bialgebra (corepresentation G)).toCoalgebra
  let ρ := affineRegularRepresentation G V b hV
  let S := affineCovariantSocle G f
  let bS := Module.finBasis k S
  let C := coactionCoordinates V b (fun j => (bS j : algebra G))
  have hC : (affineCovariantSocleRepresentation G f).Intertwines ρ C :=
    intertwines_affine_coactionCoordinates G S V bS b
      (rightAct_mem_affineCovariantSocle G f) hV hSV
  have hi : Function.Injective C.mulVecLin := coactionCoordinates_mulVecLin_injective S V bS b hSV
  let W := LinearMap.range C.mulVecLin
  have hh := hf.isHighestWeight_affineCovariantSocleRepresentation
  have hs : ρ.IsSimpleStableSubspace W := hh.1.isSimpleStableSubspace_range hC hi
  refine ⟨W, hs, ?_, ⟨⟨_, _, C, hC, hi, rfl⟩, hh⟩⟩
  intro T ht
  let F := affineRegularCoordinateMap G V b
  have hF : Function.Injective F := affineRegularCoordinateMap_injective G V b
  have hT0 : T.map F ≠ ⊥ := by
    intro hb
    apply ht.2.1
    apply Submodule.map_injective_of_injective hF
    simpa only [Submodule.map_bot] using hb
  have hTc : T.map F ≤ V := by
    rintro _ ⟨x, -, rfl⟩
    exact affineRegularCoordinateMap_mem G V b x
  have hST : S ≤ T.map F :=
    affineCovariantSocle_le_of_nonzero_rightAct_mem G p.negativeBorelHom p.positiveUnipotentHom
      p.isUnipotent_positiveUnipotent _ (T.map F)
      (rightAct_mem_map_affineRegularCoordinateMap G V b hV T ht.1) (hTc.trans hcov) hT0
      p.cellCoordinate_mem_nonZeroDivisors p.exists_factors_of_isUnit_cellCoordinate
      hf.1 hf.2.1 hf.2.2
  have hWT : W ≤ T := by
    rintro _ ⟨x, rfl⟩
    have hm : F (C.mulVecLin x) ∈ T.map F := by
      change affineRegularCoordinateMap G V b
        ((coactionCoordinates V b (fun j => (bS j : algebra G))).mulVecLin x) ∈ T.map F
      rw [coordinateInclusionCommutes S V bS b hSV]
      exact hST (affineRegularCoordinateMap_mem G S bS x)
    obtain ⟨y, hy, he⟩ := hm
    exact hF he ▸ hy
  exact ((ht.2.2 W hs.1 hWT).resolve_left hs.2.1).symm

include hcov in
private theorem covariant_weight_bounds (mu : characterLattice p.torus)
    (hmu : p.representationWeightSpace (affineRegularRepresentation G V b hV) mu ≠ ⊥) :
    lam - mu ∈ p.positiveRootMonoid ∧ ∀ w : p.rootDatum.weylGroup,
      (∀ i : p.rootIndex, p.base.IsPos (w.val.indexEquiv i) ↔ ¬ p.base.IsPos i) →
        mu - w.val • lam ∈ p.positiveRootMonoid := by
  let ρ := affineRegularRepresentation G V b hV
  refine ⟨p.affineRegularRepresentation_weight_le V b hV hcov hmu, ?_⟩
  intro w hw
  have hmu' : p.representationWeightSpace ρ (w.val⁻¹ • mu) ≠ ⊥ := by
    intro h
    have hd := weylWeightFinrank p ρ w.val⁻¹ (p.rootDatum.weylGroup.inv_mem w.property) mu
    rw [h, finrank_bot] at hd
    exact hmu (Submodule.finrank_eq_zero.mp hd.symm)
  have hlo := negWeylSendsPositive p w hw
    (p.affineRegularRepresentation_weight_le V b hV hcov hmu')
  rwa [smul_sub, smul_inv_smul, neg_sub] at hlo

end Covariant

/-- Milne 22.27(b,c), 2022 reprint: for dominant `lam` the induced representation has a unique
simple stable subspace, of highest weight `lam`, and every weight `mu` of it lies between
`w₀ lam` and `lam`. -/
theorem splitBorelInducedSocleAndWeights : SplitBorelInducedSocleAndWeightsStatement.{u} := by
  intro k _ G _ p D _ lam
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Mono p.negativeBorelHom.hom.hom := p.isRepresentedBy_negativeBorelHom.1
  let := (bialgebra (corepresentation G)).toCoalgebra
  let V := inducedSpace p.negativeBorelHom (p.borelCharacter lam)
  let b := inducedBasis p.negativeBorelHom D (p.borelCharacter lam)
  have hV : ∀ (ψ : Module.Dual k (algebra G)) (v : algebra G),
      v ∈ V → rightAct ψ v ∈ V := by
    intro ψ v hv
    unfold V inducedSpace at hv ⊢
    exact AffineCoordinates.rightAct_mem_leftCovariantSubspace p.negativeBorelHom
      (characterCoordinate p.negativeBorel (p.borelCharacter lam)) ψ hv
  have hc : V ≤ AffineCoordinates.leftCovariantSubspace p.negativeBorelHom
      (p.borelCharacterCoordinate lam) := by
    unfold V inducedSpace SplitPinning.borelCharacterCoordinate
    exact le_rfl
  constructor
  · intro hdom
    obtain ⟨f, hf⟩ := p.isRealizedWeight_of_isDominantWeight' lam hdom
    have hSV : affineCovariantSocle G f ≤ V :=
      affineCovariantSocle_le_leftCovariantSubspace G p.negativeBorelHom
        (p.borelCharacterCoordinate lam) hf.1
    unfold inducedRepresentation
    exact covariant_hasUniqueSimpleSubspace p V b hV hc hf hSV
  · intro mu hmu
    unfold inducedRepresentation at hmu
    exact covariant_weight_bounds p V b hV hc mu hmu

end Langlands.GroupScheme
