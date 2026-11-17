import Langlands.GroupScheme.Reductive.SpecialLinearRoots
import Langlands.GroupScheme.Torus.InducedProducts
import Langlands.GroupScheme.CentralIsogeny.NonzeroWeights
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Actual roots of the standard rank-one cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Products

variable {S : Scheme.{u}} (H : GroupScheme S) (C : CommGroupScheme S)

/-- The first projection from a product with a commutative group has central full kernel. -/
theorem isCentral_kernel_fst_comm :
    IsCentral (kernelι (fst H C.toGrp)) := by
  apply (isCentral_kernelι_iff (fst H C.toGrp)).mpr
  intro U x hx V a y
  change (a ≫ x) * y = y * (a ≫ x)
  apply (productPointsEquiv H C.toGrp V).injective
  rw [map_mul, map_mul]
  apply Prod.ext
  · change ((a ≫ x) ≫ fst H.X C.X) * (y ≫ fst H.X C.X) =
      (y ≫ fst H.X C.X) * ((a ≫ x) ≫ fst H.X C.X)
    have hax : (a ≫ x) ≫ fst H.X C.X = 1 := by
      rw [Category.assoc]
      change a ≫ (x ≫ (fst H C.toGrp).hom.hom) = 1
      rw [hx, MonObj.comp_one]
    rw [hax, one_mul, mul_one]
  · change ((a ≫ x) ≫ snd H.X C.X) * (y ≫ snd H.X C.X) =
      (y ≫ snd H.X C.X) * ((a ≫ x) ≫ snd H.X C.X)
    exact mul_comm _ _

end Products

section ProductRoots

variable {k : Type u} [Field k]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (C : CommGroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom (H ⊗ C.toGrp).X.hom]
  [LocallyOfFiniteType (H ⊗ C.toGrp).X.hom]

/-- A commutative product factor contributes no new nonzero adjoint roots. -/
theorem exists_root_of_mem_roots_tensor_comm
    (i : T.toGrp ⟶ H) (hT : IsSplitTorus T.toGrp) (hC : IsSplitTorus C.toGrp)
    {χ : characterLattice (CommGroupScheme.prod T C)}
    (hχ : χ ∈ roots (i ⊗ₘ 𝟙 C.toGrp)) :
    ∃ α ∈ roots i, CommGroupScheme.prodFst T C ≫ α = χ := by
  have hp : χ ∈ roots ((i ⊗ₘ 𝟙 C.toGrp) ≫ fst H C.toGrp) :=
    roots_subset_comp_of_central_kernel (T := CommGroupScheme.prod T C)
      (fst H C.toGrp) (isCentral_kernel_fst_comm H C)
      (i ⊗ₘ 𝟙 C.toGrp) (hT.tensor hC) hχ
  have heq :
      (i ⊗ₘ 𝟙 C.toGrp) ≫ fst H C.toGrp =
        CommGroupScheme.groupHom (CommGroupScheme.prodFst T C) ≫ i :=
    tensorHom_fst _ _
  rw [heq] at hp
  exact ((mem_roots_comp_iff hT (hT.tensor hC)
    (CommGroupScheme.prodFst T C) i χ).mp hp).2

/-- Choose an actual root of the first factor pulling back to a given product root. -/
def rootOfTensorComm
    (i : T.toGrp ⟶ H) (hT : IsSplitTorus T.toGrp) (hC : IsSplitTorus C.toGrp)
    (χ : {χ : characterLattice (CommGroupScheme.prod T C) //
      χ ∈ roots (i ⊗ₘ 𝟙 C.toGrp)}) :
    {α : characterLattice T // α ∈ roots i ∧ CommGroupScheme.prodFst T C ≫ α = χ.val} :=
  ⟨(exists_root_of_mem_roots_tensor_comm C i hT hC χ.property).choose,
    (exists_root_of_mem_roots_tensor_comm C i hT hC χ.property).choose_spec⟩

end ProductRoots

section SpecialLinear

variable {k : Type u} [Field k]

local notation "D" =>
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))
local notation "SL" => SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)
local notation "d" => SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k)

/-- The explicit matrix calculation of the roots of `SL₂` gives equality or opposition. -/
theorem SpecialLinear.FinSucc.eq_or_eq_neg_of_mem_roots_one
    {α β : characterLattice D} (hα : α ∈ roots d) (hβ : β ∈ roots d) :
    α = β ∨ α = -β := by
  obtain ⟨p, q, hpq, hαc⟩ := SpecialLinear.FinSucc.exists_coord_of_mem_roots hα
  obtain ⟨r, s, hrs, hβc⟩ := SpecialLinear.FinSucc.exists_coord_of_mem_roots hβ
  have hc :
      GeneralLinear.characterCoordEquiv (Fin 1) k α =
        GeneralLinear.characterCoordEquiv (Fin 1) k β ∨
      GeneralLinear.characterCoordEquiv (Fin 1) k α =
        -(GeneralLinear.characterCoordEquiv (Fin 1) k β) := by
    rw [hαc, hβc]
    fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;>
      first
      | exact (hpq rfl).elim
      | exact (hrs rfl).elim
      | exact Or.inl rfl
      | exact Or.inr (by abel)
  rcases hc with hc | hc
  · exact Or.inl ((GeneralLinear.characterCoordEquiv (Fin 1) k).injective hc)
  · apply Or.inr
    apply (GeneralLinear.characterCoordEquiv (Fin 1) k).injective
    simpa only [map_neg] using hc

variable (C : CommGroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom
    (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp).X.hom]
  [LocallyOfFiniteType
    (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp).X.hom]

/-- Every actual root of `SL₂ × C` is pulled back from an actual root of `SL₂`. -/
theorem exists_root_of_mem_roots_sl2_tensor
    (hC : IsSplitTorus C.toGrp)
    {χ : characterLattice (CommGroupScheme.prod D C)}
    (hχ : χ ∈ roots (d ⊗ₘ 𝟙 C.toGrp)) :
    ∃ α ∈ roots d, CommGroupScheme.prodFst D C ≫ α = χ := by
  exact exists_root_of_mem_roots_tensor_comm C d (isSplitTorus_splitTorus _) hC hχ

/-- Actual roots of `SL₂ × C` are equal or opposite. -/
theorem eq_or_eq_neg_of_mem_roots_sl2_tensor
    (hC : IsSplitTorus C.toGrp)
    {α β : characterLattice (CommGroupScheme.prod D C)}
    (hα : α ∈ roots (d ⊗ₘ 𝟙 C.toGrp))
    (hβ : β ∈ roots (d ⊗ₘ 𝟙 C.toGrp)) :
    α = β ∨ α = -β := by
  obtain ⟨a, ha, rfl⟩ := exists_root_of_mem_roots_sl2_tensor C hC hα
  obtain ⟨b, hb, rfl⟩ := exists_root_of_mem_roots_sl2_tensor C hC hβ
  rcases SpecialLinear.FinSucc.eq_or_eq_neg_of_mem_roots_one ha hb with hab | hab
  · exact Or.inl (congrArg (fun χ => CommGroupScheme.prodFst D C ≫ χ) hab)
  · apply Or.inr
    rw [hab, Preadditive.comp_neg]

end SpecialLinear

end Langlands.GroupScheme
