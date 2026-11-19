import Langlands.GroupScheme.Dynamic.AdjointDeterminantFunctorialityProof
import Langlands.GroupScheme.MatrixRepresentation.IntertwinerTransport
import Langlands.GroupScheme.Rational.HighestWeightBaseChange
import Langlands.GroupScheme.Reductive.SplitLeviIsotypicWeights

/-! # Ground isotypic representations on the actual anisotropic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData

open MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G}

local notation "ks" => SeparableClosure k
local notation "bc" => algebraBaseMap k (SeparableClosure k)
local notation "BC" => GroupScheme.baseChange bc

set_option maxHeartbeats 800000 in
/-- The split isotypic subspace on the actual kernel has ground coordinates. -/
private theorem exists_groundIsotypicRepresentation
    (p : d.AnisotropicKernelIndex) {n : ℕ} (ρ : MatrixRepresentation G (Fin n))
    (lam : characterLattice d.pinning.toSplitPinning.torus) :
    ∃ (m : ℕ) (τ : MatrixRepresentation p.kernel (Fin m)),
      ∀ ν : characterLattice p.index.pinning.toSplitPinning.torus,
        Nonempty (p.index.pinning.toSplitPinning.representationWeightSpace (τ.baseChange bc) ν
          ≃ₗ[ks] (p.index.pinning.toSplitPinning.representationWeightSpace
            ((ρ.baseChange bc).restrict ((BC).map (p.derived ≫ p.inclusion))) ν ⊓
          d.splitTorusDatum.isotypicSubspace (ρ.baseChange bc) lam :
            Submodule ks (Fin n → ks))) := by
  let s := d.splitTorusDatum
  let L := p.leviComparison
  let ι := p.derived ≫ p.inclusion
  let : IsAffineHom s.splitTorus.toGrp.X.hom := s.isSplitTorus.isAffineHom
  let : IsAffineHom ((BC).obj s.splitTorus.toGrp).X.hom := s.isAffineHom_baseChange
  let : IsAffineHom ((BC).obj p.kernel).X.hom := by
    change IsAffineHom (Limits.pullback.snd p.kernel.X.hom bc)
    infer_instance
  let : IsAffine ((BC).obj p.kernel).X.left := isAffine_of_isAffineHom ((BC).obj p.kernel).X.hom
  let ρS := ρ.restrict s.splitInclusion
  let χ := s.restriction lam
  let V := ρS.latticeCharacterSpace χ
  let W := s.isotypicSubspace (ρ.baseChange bc) lam
  let e := characterLattice.baseChangeEquiv bc s.splitTorus s.isSplitTorus
  have hχ : characterLattice.baseChange bc s.splitTorus χ = s.splitCharacter lam := by
    change e (e.symm (s.splitCharacter lam)) = s.splitCharacter lam
    exact e.apply_symm_apply _
  have hW : W = ρS.extendedLatticeCharacterSpace (K := ks) χ := by
    rw [← latticeCharacterSpace_baseChange_eq_extended s.isSplitTorus ρS χ, hχ]
    unfold W GaloisPinningData.SplitTorusDatum.isotypicSubspace latticeCharacterSpace ρS
    rw [baseChange_restrict]
    rfl
  obtain ⟨m, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hVst : (ρ.restrict ι).IsStableSubspace V :=
    isStableSubspace_characterSpace_of_centralizes s.splitInclusion ι L.centralizes ρ _
  have hst := hVst.isStableCoordinates B C hcols hproj
  let τ := restrictCoordinates (ρ.restrict ι) B C hCB hst
  let B' := B.map (algebraMap k ks)
  let C' := C.map (algebraMap k ks)
  have hCB' : C' * B' = 1 := by
    dsimp only [B', C']
    rw [← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcols' : ∀ j, (fun i => B' i j) ∈ W := by
    intro j
    rw [hW]
    exact Submodule.subset_span ⟨_, hcols j, rfl⟩
  have hproj' : ∀ v, v ∈ W → (B' * C') *ᵥ v = v := by
    let P := (B' * C').mulVecLin - (LinearMap.id : (Fin n → ks) →ₗ[ks] (Fin n → ks))
    have hker : W ≤ LinearMap.ker P := by
      rw [hW]
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      apply LinearMap.mem_ker.mpr
      change (B' * C') *ᵥ (fun i => algebraMap k ks (v i)) -
        (fun i => algebraMap k ks (v i)) = 0
      apply sub_eq_zero.mpr
      dsimp only [B', C']
      rw [← Matrix.map_mul]
      funext i
      exact ((algebraMap k ks).map_mulVec (B * C) v i).symm.trans
        (congrArg (fun w : Fin n → k => algebraMap k ks (w i)) (hproj v hv))
    exact fun v hv => sub_eq_zero.mp (LinearMap.mem_ker.mp (hker hv))
  have hWst := L.isStableSubspace_isotypicSubspace (ρ.baseChange bc) lam
  have hst' := hWst.isStableCoordinates B' C' hcols' hproj'
  have hτ : τ.baseChange bc =
      restrictCoordinates ((ρ.baseChange bc).restrict ((BC).map ι)) B' C' hCB' hst' := by
    apply MatrixRepresentation.ext_affineMatrix
    intro A x
    let : Algebra k A := ((algebraMap ks A).comp (algebraMap k ks)).toAlgebra
    let : IsScalarTower k ks A := IsScalarTower.of_algebraMap_eq' rfl
    apply Units.ext
    have hB : B'.map (algebraMap ks A) = B.map (algebraMap k A) := by
      ext i j
      exact (IsScalarTower.algebraMap_apply k ks A (B i j)).symm
    have hC : C'.map (algebraMap ks A) = C.map (algebraMap k A) := by
      ext i j
      exact (IsScalarTower.algebraMap_apply k ks A (C i j)).symm
    rw [affineMatrix_baseChange_fintype, restrictCoordinates_affineMatrix,
      restrictCoordinates_affineMatrix, ← baseChange_restrict,
      affineMatrix_baseChange_fintype, hB, hC]
  refine ⟨m, τ, fun ν => ?_⟩
  rw [hτ]
  exact ⟨p.index.pinning.toSplitPinning.representationWeightSpaceRestrictCoordinatesEquiv
    _ W B' C' hCB' hcols' hproj' hst' ν⟩

/-- A positive combination of simple kernel roots lifts to the positive ambient monoid
with zero split restriction. -/
private theorem exists_positiveRootLift (p : d.AnisotropicKernelIndex)
    {ν : characterLattice p.index.pinning.toSplitPinning.torus}
    (hν : ν ∈ p.index.pinning.toSplitPinning.positiveRootMonoid) :
    ∃ β ∈ d.pinning.toSplitPinning.positiveRootMonoid,
      p.leviComparison.weightRestriction β = ν ∧
      d.splitTorusDatum.splitCharacter β = 0 := by
  let L := p.leviComparison
  let s := d.splitTorusDatum
  induction hν using AddSubmonoid.closure_induction with
  | mem _ hroot =>
    obtain ⟨a, rfl⟩ := hroot
    let z := L.vertexEquiv a
    refine ⟨d.pinning.rootDatum.root z.val.val,
      d.pinning.toSplitPinning.simpleRoot_mem_positiveRootMonoid z.val, ?_, ?_⟩
    · rw [L.weightRestriction_root_zero z]
      change p.index.pinning.rootDatum.root (L.vertexEquiv.symm (L.vertexEquiv a)).val = _
      rw [Equiv.symm_apply_apply]
      rfl
    · have hz := z.property
      change s.restriction (d.pinning.rootDatum.root z.val.val) = 0 at hz
      let e := characterLattice.baseChangeEquiv bc s.splitTorus s.isSplitTorus
      exact e.symm.injective (hz.trans e.symm.map_zero.symm)
  | zero =>
    exact ⟨0, zero_mem _, L.weightRestriction.map_zero,
      (characterPrecompInt ((CommGroupScheme.baseChange bc).map s.torusMap)).map_zero⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨x, hx, hDx, hSx⟩ := hx
    obtain ⟨y, hy, hDy, hSy⟩ := hy
    refine ⟨x + y, add_mem hx hy, by rw [map_add, hDx, hDy], ?_⟩
    change characterPrecompInt ((CommGroupScheme.baseChange bc).map s.torusMap) (x + y) = 0
    change characterPrecompInt ((CommGroupScheme.baseChange bc).map s.torusMap) x = 0 at hSx
    change characterPrecompInt ((CommGroupScheme.baseChange bc).map s.torusMap) y = 0 at hSy
    rw [map_add, hSx, hSy, zero_add]

/-- When the split and kernel torus restrictions jointly determine an absolute weight,
a maximal multiplicity-one weight of a ground representation restricts to such a weight of a
ground representation of the actual kernel. -/
def GroundKernelMaximalWeightTransfer (d : TitsIndexData G) : Prop :=
  (∀ {x y : characterLattice d.pinning.toSplitPinning.torus},
    d.anisotropicKernelIndex.comparison.weightRestriction x =
      d.anisotropicKernelIndex.comparison.weightRestriction y →
    d.splitTorusDatum.splitCharacter x = d.splitTorusDatum.splitCharacter y → x = y) →
  ∀ {n : ℕ} (ρ : MatrixRepresentation G (Fin n))
    (lam : characterLattice d.pinning.toSplitPinning.torus),
    Module.finrank ks
      (d.pinning.toSplitPinning.representationWeightSpace (ρ.baseChange bc) lam) = 1 →
    (∀ μ, d.pinning.toSplitPinning.representationWeightSpace (ρ.baseChange bc) μ ≠ ⊥ →
      μ - lam ∈ d.pinning.toSplitPinning.positiveRootMonoid → μ = lam) →
    ∃ (m : ℕ) (τ : MatrixRepresentation d.anisotropicKernelIndex.kernel (Fin (m + 1))),
      let p := d.anisotropicKernelIndex
      let q := p.index.pinning.toSplitPinning
      let ν : characterLattice q.torus := p.comparison.weightRestriction lam
      Module.finrank ks (q.representationWeightSpace (τ.baseChange bc) ν) = 1 ∧
      ∀ μ, q.representationWeightSpace (τ.baseChange bc) μ ≠ ⊥ →
        μ - ν ∈ q.positiveRootMonoid → μ = ν

set_option maxHeartbeats 800000 in
theorem groundKernelMaximalWeightTransfer : d.GroundKernelMaximalWeightTransfer := by
  intro hinj n ρ lam hmult hmax
  let p := d.anisotropicKernelIndex
  let L := p.leviComparison
  let s := d.splitTorusDatum
  let q := p.index.pinning.toSplitPinning
  let ρK := ρ.baseChange bc
  let τK := ρK.restrict ((BC).map (p.derived ≫ p.inclusion))
  let ν : characterLattice q.torus := L.weightRestriction lam
  let W := s.isotypicSubspace ρK lam
  obtain ⟨m, τ, hτ⟩ := exists_groundIsotypicRepresentation p ρ lam
  have heq : q.representationWeightSpace τK ν ⊓ W =
      d.pinning.toSplitPinning.representationWeightSpace ρK lam := by
    apply le_antisymm
    · refine (L.representationWeightSpace_inf_isotypicSubspace_le ρK ν lam).trans ?_
      refine iSup_le fun μ => iSup_le fun hμ => ?_
      have hμlam : μ = lam := hinj hμ.1 hμ.2
      rw [hμlam]
    · exact le_inf (L.representationWeightSpace_le_restrict ρK lam)
        (s.representationWeightSpace_le_isotypicSubspace ρK lam)
  have hmult' : Module.finrank ks (q.representationWeightSpace (τ.baseChange bc) ν) = 1 := by
    rw [(hτ ν).some.finrank_eq]
    change Module.finrank ks (q.representationWeightSpace τK ν ⊓ W :
      Submodule ks (Fin n → ks)) = 1
    rw [heq]
    exact hmult
  have hmax' (μ : characterLattice q.torus)
      (hμ : q.representationWeightSpace (τ.baseChange bc) μ ≠ ⊥)
      (hpos : μ - ν ∈ q.positiveRootMonoid) : μ = ν := by
    obtain ⟨β, hβ, hD, hS⟩ := exists_positiveRootLift p hpos
    have hne : q.representationWeightSpace τK μ ⊓ W ≠ ⊥ := by
      intro hbot
      apply hμ
      apply Submodule.finrank_eq_zero.mp
      change Module.finrank ks (q.representationWeightSpace (τ.baseChange bc) μ) = 0
      rw [(hτ μ).some.finrank_eq]
      change Module.finrank ks (q.representationWeightSpace τK μ ⊓ W :
        Submodule ks (Fin n → ks)) = 0
      rw [hbot, finrank_bot]
    by_contra hnot
    apply hne
    refine eq_bot_iff.mpr ((L.representationWeightSpace_inf_isotypicSubspace_le ρK μ lam).trans ?_)
    refine iSup_le fun (x : characterLattice d.pinning.toSplitPinning.torus) =>
      iSup_le fun hx => ?_
    by_contra hx0
    have hxlam : x = lam + β := by
      apply hinj
      · change L.weightRestriction x = L.weightRestriction (lam + β)
        rw [map_add, hx.1, hD]
        change μ = ν + (μ - ν)
        abel
      · change s.splitCharacter x =
          characterPrecompInt ((CommGroupScheme.baseChange bc).map s.torusMap) (lam + β)
        change characterPrecompInt ((CommGroupScheme.baseChange bc).map s.torusMap) β = 0 at hS
        rw [map_add, hS, add_zero]
        exact hx.2
    have hxpos : x - lam ∈ d.pinning.toSplitPinning.positiveRootMonoid := by
      rw [hxlam, add_sub_cancel_left]
      exact hβ
    have hx' := hmax x (fun he => hx0 he.le) hxpos
    apply hnot
    rw [hx'] at hx
    exact hx.1.symm
  cases m with
  | zero =>
    have hmle := Submodule.finrank_le (q.representationWeightSpace (τ.baseChange bc) ν)
    simp only [hmult', Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hmle
    omega
  | succ m => exact ⟨m, τ, hmult', hmax'⟩

end Langlands.GroupScheme.TitsIndexData
