import Langlands.Geometry.Building.SplitRealTorusSpace
import Langlands.GroupScheme.Rational.RelativeRank
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Finiteness and dimensions of the real spaces of a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

namespace RealTorusSpace

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Real scalar extension of transport on actual cocharacters. -/
def cocharacterRealCongr (e : T ≅ T') : V T ≃ₗ[ℝ] V T' :=
  LinearEquiv.baseChange ℤ ℝ _ _ (cocharacterLattice.congr e).toIntLinearEquiv

/-- Real scalar extension of transport on actual characters. -/
def characterRealCongr (e : T ≅ T') : Vstar T ≃ₗ[ℝ] Vstar T' :=
  LinearEquiv.baseChange ℤ ℝ _ _ (characterLattice.congr e).toIntLinearEquiv

@[simp] theorem cocharacterRealCongr_tmul (e : T ≅ T') (r : ℝ)
    (ν : cocharacterLattice T) :
    cocharacterRealCongr e (r ⊗ₜ[ℤ] ν) = r ⊗ₜ[ℤ] (ν ≫ e.hom) := rfl

@[simp] theorem characterRealCongr_tmul (e : T ≅ T') (r : ℝ)
    (χ : characterLattice T) :
    characterRealCongr e (r ⊗ₜ[ℤ] χ) = r ⊗ₜ[ℤ] (e.inv ≫ χ) := rfl

/-- Actual isomorphisms preserve the real lattice pairing. -/
theorem pair_congr (e : T ≅ T') (x : Vstar T) (v : V T) :
    pair T' (characterRealCongr e x) (cocharacterRealCongr e v) = pair T x v := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    induction v using TensorProduct.inductionOn with
    | tmul s ν =>
      simpa only [characterRealCongr_tmul, cocharacterRealCongr_tmul, pair_tmul_tmul,
        characterLattice.congr_apply, cocharacterLattice.congr_apply] using
        congrArg (fun z : ℤ => r * s * (z : ℝ)) (latticePairing_congr e χ ν)
    | add v w hv hw => simp only [map_add, hv, hw]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end RealTorusSpace

open RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The real cocharacter space of every actual finite-rank split torus is finite. -/
theorem IsSplitTorus.finite_realCocharacterSpace (hT : IsSplitTorus T.toGrp) :
    Module.Finite ℝ (V T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact Module.Finite.equiv
    ((cocharacterRealCongr eC).trans (splitCocharacterCoordinates k I)).symm

/-- The real character space of every actual finite-rank split torus is finite. -/
theorem IsSplitTorus.finite_realCharacterSpace (hT : IsSplitTorus T.toGrp) :
    Module.Finite ℝ (Vstar T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact Module.Finite.equiv
    ((characterRealCongr eC).trans (splitCharacterCoordinates k I)).symm

/-- The full real cocharacter dimension equals the full rational character rank. -/
theorem IsSplitTorus.finrank_realCocharacterSpace (hT : IsSplitTorus T.toGrp) :
    Module.finrank ℝ (V T) = splitTorusRank T := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  rw [((cocharacterRealCongr eC).trans (splitCocharacterCoordinates k I)).finrank_eq,
    splitTorusRank,
    ((LinearEquiv.baseChange ℤ ℚ _ _ (characterLattice.congr eC).toIntLinearEquiv).trans
      (Langlands.LinearAlgebra.RationalSpan.tensorEquivPi
        (splitTorus.characterLatticeEquiv k I))).finrank_eq]
  simp

/-- The full real character dimension equals the full rational character rank. -/
theorem IsSplitTorus.finrank_realCharacterSpace (hT : IsSplitTorus T.toGrp) :
    Module.finrank ℝ (Vstar T) = splitTorusRank T := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  rw [((characterRealCongr eC).trans (splitCharacterCoordinates k I)).finrank_eq,
    splitTorusRank,
    ((LinearEquiv.baseChange ℤ ℚ _ _ (characterLattice.congr eC).toIntLinearEquiv).trans
      (Langlands.LinearAlgebra.RationalSpan.tensorEquivPi
        (splitTorus.characterLatticeEquiv k I))).finrank_eq]
  simp

end Langlands.GroupScheme
