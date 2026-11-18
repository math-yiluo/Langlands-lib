import Langlands.GroupScheme.SimplyConnected.AbsoluteCenterCharacterRestriction
import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField
import Mathlib.Data.ZMod.Basic

/-! # Full centre character stabilizers of the leaves of D4 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G)

private def representationStabilizer {Γ V : Type u} [Group Γ] [AddCommGroup V]
    (ρ : Representation ℤ Γ V) (χ : V) : Subgroup Γ :=
  letI : MulAction Γ V := {
    smul := fun σ v => ρ σ v
    one_smul := fun v => LinearMap.congr_fun (map_one ρ) v
    mul_smul := fun σ τ v => LinearMap.congr_fun (map_mul ρ σ τ) v }
  MulAction.stabilizer Γ χ

/-- The ordinary absolute Galois stabilizer of an actual geometric centre character. -/
def centerCharacterStabilizer
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
      d.toralCenter.group)) : Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  representationStabilizer
    (characterLattice.galoisRepresentation K (SeparableClosure K) d.toralCenter.group) χ

/-- The sum of two specified leaf-coroot pairings, reduced modulo two. -/
private def leafPairParity (e : d.Vertex ≃ Fin 4) (j : Fin 4) :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj d.pinning.torus) →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap.comp
    (d.pinning.rootDatum.toLinearMap.flip (d.pinning.rootDatum.coroot (e.symm 0).val) +
      d.pinning.rootDatum.toLinearMap.flip (d.pinning.rootDatum.coroot (e.symm j).val))

private theorem leafPairParity_apply (e : d.Vertex ≃ Fin 4) (j : Fin 4)
    (χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj d.pinning.torus)) :
    d.leafPairParity e j χ =
      (↑(d.pinning.rootDatum.toLinearMap χ (d.pinning.rootDatum.coroot (e.symm 0).val) +
        d.pinning.rootDatum.toLinearMap χ (d.pinning.rootDatum.coroot (e.symm j).val)) : ZMod 2) :=
  rfl

/-- Both leaf-pair parities kill the full integral root span. -/
private theorem rootSpan_le_ker_leafPairParity (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    {j : Fin 4} (hj : j = 2 ∨ j = 3) :
    d.pinning.rootDatum.rootSpan ℤ ≤ LinearMap.ker (d.leafPairParity e j) := by
  change Submodule.span ℤ (Set.range d.pinning.rootDatum.root) ≤ _
  rw [← d.pinning.base.span_int_root_support]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, rfl⟩
  let v : d.Vertex := ⟨a, ha⟩
  change d.leafPairParity e j (d.pinning.rootDatum.root v.val) = 0
  rw [d.leafPairParity_apply, d.pinning.rootDatum.root_coroot_eq_pairing,
    d.pinning.rootDatum.root_coroot_eq_pairing]
  change (↑(d.cartan v (e.symm 0) + d.cartan v (e.symm j)) : ZMod 2) = 0
  rw [hD, hD, e.apply_symm_apply, e.apply_symm_apply]
  generalize e v = i
  rcases hj with rfl | rfl <;> fin_cases i <;> decide

private def leafPairParityValue (j i : Fin 4) : ZMod 2 :=
  Int.cast ((if (0 : Fin 4) = i then 1 else 0) + (if j = i then 1 else 0) : ℤ)

private theorem leafPairParity_fundamental (hsc : IsSimplyConnected G)
    (e : d.Vertex ≃ Fin 4) (j : Fin 4) (i : Fin 4) :
    d.leafPairParity e j (d.absoluteFundamentalCharacter hsc (e.symm i)) =
      leafPairParityValue j i := by
  classical
  rw [d.leafPairParity_apply]
  unfold absoluteFundamentalCharacter
  rw [Langlands.RootDatum.fundamentalWeightBasis_pairing,
    Langlands.RootDatum.fundamentalWeightBasis_pairing]
  simp only [leafPairParityValue, Equiv.apply_eq_iff_eq]

private theorem d4Leaf_eq_of_pairParities (i j : Fin 4) (hi : i ≠ 1) (hj : j ≠ 1)
    (p2 : leafPairParityValue 2 i = leafPairParityValue 2 j)
    (p3 : leafPairParityValue 3 i = leafPairParityValue 3 j) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [leafPairParityValue]

/-- On the three leaves of a D4 numbering, the actual centre characters distinguish
all the vertices. -/
theorem centerFundamentalCharacter_D4_leaf_eq_iff
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a b : d.Vertex) (ha : e a ≠ 1) (hb : e b ≠ 1) :
    d.centerFundamentalCharacter hsc a = d.centerFundamentalCharacter hsc b ↔ a = b := by
  classical
  constructor
  · intro heq
    have hzero : d.centerCharacterRestriction
        (d.absoluteFundamentalCharacter hsc a - d.absoluteFundamentalCharacter hsc b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr heq
    have hmem := (d.centerCharacterRestriction_eq_zero_iff _).mp hzero
    have hparity (j : Fin 4) (hj : j = 2 ∨ j = 3) :
        d.leafPairParity e j (d.absoluteFundamentalCharacter hsc a) =
          d.leafPairParity e j (d.absoluteFundamentalCharacter hsc b) := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact (d.rootSpan_le_ker_leafPairParity e hD hj) hmem
    obtain ⟨i, rfl⟩ := e.symm.surjective a
    obtain ⟨j, rfl⟩ := e.symm.surjective b
    simp only [e.apply_symm_apply] at ha hb
    apply congrArg e.symm
    apply d4Leaf_eq_of_pairParities i j ha hb
    · simpa only [d.leafPairParity_fundamental hsc] using hparity 2 (Or.inl rfl)
    · simpa only [d.leafPairParity_fundamental hsc] using hparity 3 (Or.inr rfl)
  · rintro rfl
    rfl

/-- Ordinary Galois fixation of a D4 leaf character is equivalent to full star
fixation of the leaf. -/
theorem centerCharacterStabilizer_D4_leaf
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a : d.Vertex) (ha : e a ≠ 1) :
    d.centerCharacterStabilizer (d.centerFundamentalCharacter hsc a) = d.starVertexStabilizer a := by
  ext σ
  change characterLattice.galoisRepresentation K (SeparableClosure K) d.toralCenter.group σ
    (d.centerFundamentalCharacter hsc a) = d.centerFundamentalCharacter hsc a ↔ d.star σ a = a
  rw [d.centerFundamentalCharacter_galois]
  have hstar : e (d.star σ a) ≠ 1 := by
    intro h
    have hc := d.star_fixes_center_of_D (by decide) e hD σ (e.symm 1) (by simp)
    have heq : d.star σ a = d.star σ (e.symm 1) :=
      e.injective (h.trans (by simp [hc]))
    have hleaf := (d.starPermutation σ).injective heq
    exact ha (by simpa only [Equiv.apply_symm_apply] using congrArg e hleaf)
  exact d.centerFundamentalCharacter_D4_leaf_eq_iff hsc e hD (d.star σ a) a hstar ha

/-- The ordinary fixed field of the character stabilizer is the actual leaf field. -/
theorem fixedField_centerCharacterStabilizer_D4_leaf
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a : d.Vertex) (ha : e a ≠ 1) :
    IntermediateField.fixedField (d.centerCharacterStabilizer (d.centerFundamentalCharacter hsc a)) =
      d.starVertexField a :=
  congrArg IntermediateField.fixedField (d.centerCharacterStabilizer_D4_leaf hsc e hD a ha)

end Langlands.GroupScheme.TitsIndexData
