import Langlands.GroupScheme.Reductive.RankOneCentralCoverRoots
import Langlands.GroupScheme.CentralIsogeny.NonzeroWeightEquivalence
import Langlands.GroupScheme.CentralIsogeny.RootComparison

/-! # Root-space lines from a supplied standard rank-one cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option maxHeartbeats 800000

namespace SpecialLinear.FinSucc

variable {k : Type u} [Field k]

local notation "D" =>
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))
local notation "SL" => SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)
local notation "d" => diagonalTorus 1 (CommRingCat.of k)

/-- In rank one an off-diagonal weight determines its ordered matrix entry. -/
theorem eq_pair_of_weightCoord_sub_eq_one {p q x y : Fin 2} (hpq : p ≠ q)
    (h : weightCoord 1 x - weightCoord 1 y = weightCoord 1 p - weightCoord 1 q) :
    x = p ∧ y = q := by
  have h0 := congrFun h 0
  fin_cases p <;> fin_cases q <;> fin_cases x <;> fin_cases y <;>
    first
    | exact (hpq rfl).elim
    | exact ⟨rfl, rfl⟩
    | norm_num [weightCoord] at h0

/-- Evaluation at a fixed matrix entry on the actual root weight space of SL₂. -/
def rootEntry (χ : characterLattice D) (p q : Fin 2) :
    weightSpace d χ →ₗ[k] k where
  toFun X := lieMatrix (X : Additive (lieKernel SL k)) p q
  map_add' X Y := by
    simp only [Submodule.coe_add, map_add, Matrix.add_apply]
  map_smul' c X := by
    simp only [Submodule.coe_smul, map_smul, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- A root vector of SL₂ is determined by its one possible nonzero matrix entry. -/
theorem rootEntry_injective {χ : characterLattice D} {p q : Fin 2} (hpq : p ≠ q)
    (hχ : GeneralLinear.characterCoordEquiv (Fin 1) k χ =
      weightCoord 1 p - weightCoord 1 q) :
    Function.Injective (rootEntry χ p q) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  apply Subtype.ext
  apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
  rw [Submodule.coe_zero, map_zero]
  ext x y
  rw [Matrix.zero_apply]
  by_contra hxy
  have hw := (mem_weightSpace_diagonalTorus_iff_support X.val χ).mp X.property x y hxy
  have hpair := eq_pair_of_weightCoord_sub_eq_one hpq (hw.symm.trans hχ)
  obtain ⟨rfl, rfl⟩ := hpair
  exact hxy hX

/-- Every actual root space of the diagonal torus of SL₂ has dimension one. -/
theorem finrank_weightSpace_eq_one {χ : characterLattice D} (hχ : χ ∈ roots d) :
    Module.finrank k (weightSpace d χ) = 1 := by
  obtain ⟨p, q, hpq, hc⟩ := exists_coord_of_mem_roots hχ
  have hle := LinearMap.finrank_le_finrank_of_injective (rootEntry_injective hpq hc)
  rw [Module.finrank_self] at hle
  let : Nontrivial (weightSpace d χ) := Submodule.nontrivial_iff_ne_bot.mpr hχ.2
  have hpos : 0 < Module.finrank k (weightSpace d χ) := Module.finrank_pos
  omega

/-- Choose the actual root-space line of SL₂ from its explicit matrix coordinates. -/
def rootLine (χ : characterLattice D) (hχ : χ ∈ roots d) :
    k ≃ₗ[k] weightSpace d χ :=
  Classical.choice (Module.nonempty_linearEquiv_of_finrank_eq_one
    (finrank_weightSpace_eq_one hχ))

end SpecialLinear.FinSucc

namespace RankOneCentralCover

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

local notation "D" =>
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))
local notation "SL" => SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)
local notation "d" => SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k)

section CentralKernel

variable {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual nonzero weight injects into an SL₂ root line through a central-kernel map. -/
theorem finrank_eq_one_of_centralKernelMap
    (p : H ⟶ SL) (hp : IsCentral (kernelι p)) (j : S.toGrp ⟶ H)
    (hS : IsSplitTorus S.toGrp) (t : S ⟶ D)
    (hinj : Function.Injective (fun α : characterLattice D => t ≫ α))
    (ht : j ≫ p = CommGroupScheme.groupHom t ≫ d)
    (α : characterLattice D) (hα : α ∈ roots d)
    (hχ : t ≫ α ∈ roots j) :
    Module.finrank k (weightSpace j (t ≫ α)) = 1 := by
  have hle : Module.finrank k (weightSpace j (t ≫ α)) ≤
      Module.finrank k (weightSpace (j ≫ p) (t ≫ α)) :=
    LinearMap.finrank_le_finrank_of_injective
      (Lie.weightSpaceMap_injective_of_central_kernel (k := k) p hp j hS hχ.1)
  rw [ht, (Lie.weightSpaceCompEquiv hS (isSplitTorus_splitTorus _) t d hinj α).finrank_eq,
    SpecialLinear.FinSucc.finrank_weightSpace_eq_one hα] at hle
  let : Nontrivial (weightSpace j (t ≫ α)) := Submodule.nontrivial_iff_ne_bot.mpr hχ.2
  have hpos : 0 < Module.finrank k (weightSpace j (t ≫ α)) := Module.finrank_pos
  omega

/-- Choose a source root line from a supplied central-kernel comparison with SL₂. -/
def rootLineOfCentralKernelMap
    (p : H ⟶ SL) (hp : IsCentral (kernelι p)) (j : S.toGrp ⟶ H)
    (hS : IsSplitTorus S.toGrp) (t : S ⟶ D)
    (hinj : Function.Injective (fun α : characterLattice D => t ≫ α))
    (ht : j ≫ p = CommGroupScheme.groupHom t ≫ d)
    (α : characterLattice D) (hα : α ∈ roots d)
    (hχ : t ≫ α ∈ roots j) :
    k ≃ₗ[k] weightSpace j (t ≫ α) :=
  haveI : Module.Free k (weightSpace j (t ≫ α)) := Module.Free.of_divisionRing k _
  Classical.choice (Module.nonempty_linearEquiv_of_finrank_eq_one
    (finrank_eq_one_of_centralKernelMap p hp j hS t hinj ht α hα hχ))

end CentralKernel

variable (C : CommGroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom
    (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp).X.hom]
  [LocallyOfFiniteType
    (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp).X.hom]

omit [IsAffineHom (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp).X.hom]
  [LocallyOfFiniteType (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp).X.hom] in
/-- Character pullback along a product projection is injective. -/
theorem prodFst_character_injective : Function.Injective
    (fun α : characterLattice D => CommGroupScheme.prodFst D C ≫ α) := by
  intro α β hab
  have h := congrArg (fun f => CommGroupScheme.prodInl D C ≫ f) hab
  simpa only [← Category.assoc, CommGroupScheme.prodInl_fst, Category.id_comp] using h

/-- A nonzero root space of SL₂ times a commutative split torus is still a line. -/
theorem nonempty_productRootLine (hC : IsSplitTorus C.toGrp)
    {χ : characterLattice (CommGroupScheme.prod D C)}
    (hχ : χ ∈ roots (d ⊗ₘ 𝟙 C.toGrp)) :
    Nonempty (k ≃ₗ[k] weightSpace (d ⊗ₘ 𝟙 C.toGrp) χ) := by
  obtain ⟨α, hα, rfl⟩ := exists_root_of_mem_roots_sl2_tensor C hC hχ
  exact ⟨rootLineOfCentralKernelMap (S := CommGroupScheme.prod D C)
    (fst SL C.toGrp) (isCentral_kernel_fst_comm SL C) (d ⊗ₘ 𝟙 C.toGrp)
    ((isSplitTorus_splitTorus _).tensor hC) (CommGroupScheme.prodFst D C)
    (prodFst_character_injective C) (tensorHom_fst _ _) α hα hχ⟩

/-- Choose the root-space line of the standard product from explicit SL₂ matrix data. -/
def productRootLine (hC : IsSplitTorus C.toGrp)
    (χ : characterLattice (CommGroupScheme.prod D C))
    (hχ : χ ∈ roots (d ⊗ₘ 𝟙 C.toGrp)) :
    k ≃ₗ[k] weightSpace (d ⊗ₘ 𝟙 C.toGrp) χ :=
  Classical.choice (nonempty_productRootLine C hC hχ)

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A supplied compatible standard central cover gives the actual target root-space line. -/
def rootLineOfCover (hC : IsSplitTorus C.toGrp) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (q : SL ⊗ C.toGrp ⟶ G) (hq : IsCentralIsogeny q)
    (t : CommGroupScheme.prod D C ⟶ T)
    (hinj : Function.Injective (fun α : characterLattice T => t ≫ α))
    (ht : (d ⊗ₘ 𝟙 C.toGrp) ≫ q = CommGroupScheme.groupHom t ≫ i)
    (χ : characterLattice T) (hχ : χ ∈ roots i) :
    k ≃ₗ[k] weightSpace i χ := by
  have hpull : t ≫ χ ≠ 0 := by
    intro hz
    apply hχ.1
    apply hinj
    simpa only [Limits.comp_zero] using hz
  have hroot : t ≫ χ ∈ roots ((d ⊗ₘ 𝟙 C.toGrp) ≫ q) := by
    rw [ht, mem_roots_comp_iff hT ((isSplitTorus_splitTorus _).tensor hC) t i]
    exact ⟨hpull, χ, hχ, rfl⟩
  have hsource : t ≫ χ ∈ roots (d ⊗ₘ 𝟙 C.toGrp) := by
    rwa [roots_comp_eq_of_centralIsogeny (T := CommGroupScheme.prod D C) q hq (d ⊗ₘ 𝟙 C.toGrp)
      ((isSplitTorus_splitTorus _).tensor hC)] at hroot
  let e := Lie.nonzeroWeightSpaceEquivOfCentralIsogeny (T := CommGroupScheme.prod D C) q hq (d ⊗ₘ 𝟙 C.toGrp)
    ((isSplitTorus_splitTorus _).tensor hC) hpull
  have heq : weightSpace ((d ⊗ₘ 𝟙 C.toGrp) ≫ q) (t ≫ χ) = weightSpace i χ := by
    rw [ht]
    exact weightSpace_comp_eq_of_character_injective
      ((isSplitTorus_splitTorus _).tensor hC) hT t i hinj χ
  exact (productRootLine C hC (t ≫ χ) hsource).trans
    (e.trans (LinearEquiv.ofEq _ _ heq))

/-- Use the finite-flat-surjective torus map of a standard central cover directly. -/
def rootLineOfCover_isogeny (hC : IsSplitTorus C.toGrp) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (q : SL ⊗ C.toGrp ⟶ G) (hq : IsCentralIsogeny q)
    (t : CommGroupScheme.prod D C ⟶ T)
    (htiso : IsIsogeny (CommGroupScheme.groupHom t))
    (ht : (d ⊗ₘ 𝟙 C.toGrp) ≫ q = CommGroupScheme.groupHom t ≫ i)
    (χ : characterLattice T) (hχ : χ ∈ roots i) :
    k ≃ₗ[k] weightSpace i χ := by
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  exact rootLineOfCover C hC hT i q hq t
    (RealTorusSpace.characterRestrict_injective_of_epi t) ht χ hχ

end RankOneCentralCover

end Langlands.GroupScheme
