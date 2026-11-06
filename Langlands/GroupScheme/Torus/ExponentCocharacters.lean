import Langlands.GroupScheme.Torus.ExponentCharacters

/-! # Fixed-exponent actual cocharacters over arbitrary bases -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

variable (S : Scheme.{u}) (I : Type u) [Fintype I]

/-- The actual cocharacter with the specified integer coordinate vector,
over an arbitrary base scheme. -/
def exponentCocharacter (n : I → ℤ) : cocharacterLattice (commGroupScheme S I) :=
  ∑ j, n j • single S I j

/-- Its composite with each coordinate projection is the corresponding
integer power map, without a connectedness or reducedness premise on the base. -/
@[simp] theorem exponentCocharacter_comp_proj (n : I → ℤ) (j : I) :
    exponentCocharacter S I n ≫ proj S I j = Gm.powerHom S (n j) := by
  classical
  simp only [exponentCocharacter, Preadditive.sum_comp,
    Preadditive.zsmul_comp, single_comp_proj]
  rw [Finset.sum_eq_single j]
  · simp
  · intro a _ haj
    simp [haj]
  · simp

/-- The actual cocharacter evaluates coordinatewise by the specified powers
on every test scheme. -/
theorem pointsEquiv_exponentCocharacter (n : I → ℤ)
    {U : Over S} (x : U ⟶ (Gm S).X) :
    pointsEquiv I U
        (x ≫ (CommGroupScheme.groupHom (exponentCocharacter S I n)).hom.hom) =
      fun j => Gm.pointsEquiv S U x ^ n j := by
  funext j
  rw [← comp_proj, ← comp_groupHom_comp, exponentCocharacter_comp_proj,
    Gm.powerHom_apply, Gm.comp_zsmul_id, map_zpow]

/-- Composition with a fixed-exponent actual character is the power map
given by the integer dot product, even over a nonreduced base. -/
theorem exponentCocharacter_comp_exponentCharacter (m n : I → ℤ) :
    exponentCocharacter S I n ≫ exponentCharacter S I m =
      Gm.powerHom S (∑ j, m j * n j) := by
  simp only [exponentCharacter, Preadditive.comp_sum,
    Preadditive.comp_zsmul, exponentCocharacter_comp_proj,
    Gm.powerHom_apply, smul_smul, ← Finset.sum_smul]

variable {S' : Scheme.{u}}

/-- Every coordinate cocharacter commutes with arbitrary scheme base
change through the canonical split-torus identification. -/
theorem single_baseChange (b : S' ⟶ S) (j : I) :
    cocharacterLattice.baseChange b _ (single S I j) ≫
        (commBaseChangeIso b I).hom =
      single S' I j := by
  classical
  have hproj (a : I) :
      (cocharacterLattice.baseChange b _ (single S I j) ≫
          (commBaseChangeIso b I).hom) ≫ proj S' I a =
        single S' I j ≫ proj S' I a := by
    rw [Category.assoc, commBaseChangeIso_hom_proj]
    change (Gm.commBaseChangeIso b).inv ≫
      (CommGroupScheme.baseChange b).map (single S I j) ≫
      (CommGroupScheme.baseChange b).map (proj S I a) ≫
      (Gm.commBaseChangeIso b).hom = _
    rw [← Functor.map_comp_assoc, single_comp_proj, single_comp_proj]
    split_ifs <;> simp
  calc
    _ = (cocharacterLattice.baseChange b _ (single S I j) ≫
        (commBaseChangeIso b I).hom) ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = single S' I j ≫ 𝟙 _ := by
      rw [← sum_proj_comp_single S' I]
      simp only [Preadditive.comp_sum, ← Category.assoc, hproj]
    _ = _ := Category.comp_id _

/-- Fixed-exponent actual cocharacters commute with arbitrary base change. -/
theorem exponentCocharacter_baseChange (b : S' ⟶ S) (n : I → ℤ) :
    cocharacterLattice.baseChange b _ (exponentCocharacter S I n) ≫
        (commBaseChangeIso b I).hom =
      exponentCocharacter S' I n := by
  simp only [exponentCocharacter, map_sum, map_zsmul,
    Preadditive.sum_comp, Preadditive.zsmul_comp, single_baseChange]

/-- The group-map version retains the actual dynamic cocharacter base
change used in the centralizer construction. -/
theorem groupHom_exponentCocharacter_baseChange (b : S' ⟶ S) (n : I → ℤ) :
    Dynamic.baseChangeCocharacter b
        (CommGroupScheme.groupHom (exponentCocharacter S I n)) ≫
        (baseChangeIso b I).hom =
      CommGroupScheme.groupHom (exponentCocharacter S' I n) :=
  congrArg CommGroupScheme.groupHom (exponentCocharacter_baseChange S I b n)

variable (k : Type u) [Field k]

/-- Over a field the fixed-exponent actual cocharacter is the inverse of
the existing integral coordinate equivalence. -/
theorem exponentCocharacter_eq_cocharacterLatticeEquiv_symm (n : I → ℤ) :
    exponentCocharacter (Spec (CommRingCat.of k)) I n =
      (cocharacterLatticeEquiv k I).symm n :=
  (cocharacterLatticeEquiv_symm_eq k I n).symm

/-- The actual character/cocharacter pairing is the integer dot product. -/
theorem latticePairing_exponentCharacter_exponentCocharacter (m n : I → ℤ) :
    latticePairing (commGroupScheme (Spec (CommRingCat.of k)) I)
        (exponentCharacter (Spec (CommRingCat.of k)) I m)
        (exponentCocharacter (Spec (CommRingCat.of k)) I n) =
      ∑ j, m j * n j := by
  rw [exponentCharacter_eq_characterLatticeEquiv_symm,
    exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
  exact latticePairing_symm_symm k I m n

end Langlands.GroupScheme.splitTorus
