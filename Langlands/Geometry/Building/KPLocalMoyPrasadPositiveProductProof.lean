import Langlands.Geometry.Building.KPLocalMoyPrasadGlobalExchange
import Langlands.Geometry.Building.KPLocalMoyPrasadBlockExchange
import Langlands.Geometry.Building.KPLocalMoyPrasadPositiveProductStatement

/-! # The positive-depth sign product over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise TensorProduct NNReal
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom G.X.hom]
    (P : BuildingData F G) (hZ : IsTorus P.centralizer.Z)

/-- The auxiliary subtype-indexed span is the published root-filtration span. -/
theorem depthRootSpan_eq_rootFiltrationSpan (x : P.Apartment) (r : NNReal)
    (Ψ : Set (characterLattice P.S)) :
    P.depthRootSpan x r Ψ = P.rootFiltrationSpan x Ψ r := by
  exact iSup_subtype (f := fun a : Ψ => P.filtration x a.1 r)

/-- The original centralizer-depth image normalizes every selected depth span. -/
theorem image_le_normalizer_depthRootSpan (x : P.Apartment) (r s : NNReal)
    (Ψ : Set (characterLattice P.S)) :
    P.centralizerTorusImage hZ r ≤ Subgroup.normalizer
      (P.depthRootSpan x s Ψ : Set (rationalPoints G)) :=
  (le_iInf fun a : Ψ => P.image_le_normalizer_filtration hZ x r a s).trans
    (Subgroup.iInf_normalizer_le_normalizer_iSup _)

/-- Full local exchange supplies global covering of the original sharp
constant-depth subgroup. -/
theorem sharpFiltration_subset_signs_mul_image
    (hZcomm : P.LocalTorusCommutatorFriendly hZ)
    (x : P.Apartment) (r : NNReal) (hr : 0 < r)
    (mu : cocharacterLattice P.S) (hmu : IsGenericCocharacter P.i mu) :
    (P.apartment.sharpFiltration x (fun _ => (r : ℝ)) : Set (rationalPoints G)) ⊆
      (P.depthRootSpan x r (positiveRelativeRoots P.i (-mu)) : Set (rationalPoints G)) *
        P.depthRootSpan x r (positiveRelativeRoots P.i mu) * P.centralizerTorusImage hZ r := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hneg : ∀ c ∈ relativeRoots P.i, -c ∈ relativeRoots P.i := fun c hc =>
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT
      (rootRankOneFactorization (UnramifiedClosure F) G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus) x hc
  have hex (c : characterLattice P.S) (hc : c ∈ relativeRoots P.i) :
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-c) *
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) c ⊆
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) c *
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-c) * P.centralizerTorusImage hZ r := by
    have he := P.filtrationBlock_mul_opposite_subset hZ hZcomm x (hneg c hc) r hr
    simp only [neg_neg] at he
    refine he.trans (le_of_eq ?_)
    have hcZ := Subgroup.set_mul_normalizer_comm (P.centralizerTorusImage hZ r : Set (rationalPoints G))
      (P.filtrationBlockSubgroup (exists_order_eq_one F) x r (hneg c hc))
      (P.image_le_normalizer_filtrationBlockSubgroup hZ x r r (hneg c hc))
    change (P.centralizerTorusImage hZ r : Set (rationalPoints G)) *
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-c) =
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-c) * P.centralizerTorusImage hZ r at hcZ
    rw [mul_assoc, hcZ, ← mul_assoc]
  have h := P.sharpFiltration_subset_depthExchangeSet r hT
    (hT.finite_relativeRoots P.i) (P.isAffineRootSystemWithRankZero_extendedAffineRoots (exists_order_eq_one F))
    P.derivativeRoots_extendedAffineRoots hneg hex mu hmu
  have hpos : realPositiveRoots P.i ((1 : ℝ) ⊗ₜ[ℤ] mu) = positiveRelativeRoots P.i mu := by
    ext c
    simp only [realPositiveRoots, positiveRelativeRoots, Set.mem_ofPred_eq, eval_tmul,
      one_mul, Int.cast_pos]
  have hnegpos : realPositiveRoots P.i (-((1 : ℝ) ⊗ₜ[ℤ] mu)) =
      positiveRelativeRoots P.i (-mu) := by
    ext c
    simp only [realPositiveRoots, positiveRelativeRoots, Set.mem_ofPred_eq, map_neg,
      eval_tmul, one_mul, neg_pos]
    constructor
    · rintro ⟨hc, h⟩
      exact ⟨hc, by exact_mod_cast h⟩
    · rintro ⟨hc, h⟩
      exact ⟨hc, by exact_mod_cast h⟩
  simpa only [depthExchangeSet, hpos, hnegpos] using h

/-- The full original positive-depth subgroup is the product of the two
original sign spans and its actual centralizer-depth image. -/
theorem moyPrasad_eq_negative_image_positive
    (hZcomm : P.LocalTorusCommutatorFriendly hZ)
    (x : P.Apartment) (r : NNReal) (hr : 0 < r)
    (mu : cocharacterLattice P.S) (hmu : IsGenericCocharacter P.i mu) :
    (P.moyPrasad hZ x r : Set (rationalPoints G)) =
      (P.depthRootSpan x r (positiveRelativeRoots P.i (-mu)) : Set (rationalPoints G)) *
        (P.centralizerTorusImage hZ r : Set (rationalPoints G)) *
          P.depthRootSpan x r (positiveRelativeRoots P.i mu) := by
  let N := P.depthRootSpan x r (positiveRelativeRoots P.i (-mu))
  let Q := P.depthRootSpan x r (positiveRelativeRoots P.i mu)
  let Z := P.centralizerTorusImage hZ r
  have hnormal : P.centralizerTorusImage hZ r ≤ Subgroup.normalizer
      (P.apartment.sharpFiltration x (fun _ => (r : ℝ)) : Set (rationalPoints G)) := by
    rw [P.apartment.sharpFiltration_eq_iSup]
    exact (le_iInf fun a : relativeRoots P.i =>
      P.image_le_normalizer_filtration hZ x r a r).trans
        (Subgroup.iInf_normalizer_le_normalizer_iSup _)
  have hprod : (P.moyPrasad hZ x r : Set (rationalPoints G)) =
      (Z : Set (rationalPoints G)) *
        P.apartment.sharpFiltration x (fun _ => (r : ℝ)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormal
  have hZN : (Z : Set (rationalPoints G)) * N =
      (N : Set (rationalPoints G)) * Z :=
    Subgroup.set_mul_normalizer_comm _ _
      (P.image_le_normalizer_depthRootSpan hZ x r r _)
  have hZQ : (Z : Set (rationalPoints G)) * Q =
      (Q : Set (rationalPoints G)) * Z :=
    Subgroup.set_mul_normalizer_comm _ _
      (P.image_le_normalizer_depthRootSpan hZ x r r _)
  have hcollect : (Z : Set (rationalPoints G)) * ((N : Set (rationalPoints G)) * Q * Z) =
      (N : Set (rationalPoints G)) * Z * Q := by
    calc (Z : Set (rationalPoints G)) * ((N : Set (rationalPoints G)) * Q * Z)
        = ((Z : Set (rationalPoints G)) * N) * Q * Z := by
          simp only [mul_assoc]
      _ = ((N : Set (rationalPoints G)) * Z) * Q * Z := by rw [hZN]
      _ = (N : Set (rationalPoints G)) * ((Z : Set (rationalPoints G)) * Q) * Z := by
          rw [mul_assoc (N : Set (rationalPoints G))]
      _ = (N : Set (rationalPoints G)) * ((Q : Set (rationalPoints G)) * Z) * Z := by
          rw [hZQ]
      _ = ((N : Set (rationalPoints G)) * Q) * ((Z : Set (rationalPoints G)) * Z) := by
          simp only [mul_assoc]
      _ = ((N : Set (rationalPoints G)) * Q) * Z := by rw [coe_mul_coe]
      _ = (N : Set (rationalPoints G)) * Z * Q := by
          rw [mul_assoc, ← hZQ, ← mul_assoc]
  apply Set.Subset.antisymm
  · rw [hprod]
    exact (Set.mul_subset_mul_left
      (P.sharpFiltration_subset_signs_mul_image hZ hZcomm x r hr mu hmu)).trans
        (le_of_eq hcollect)
  · have hle (nu : cocharacterLattice P.S) :
        P.depthRootSpan x r (positiveRelativeRoots P.i nu) ≤ P.moyPrasad hZ x r :=
      iSup_le fun a => P.filtration_le_moyPrasad hZ x ⟨a, a.2.1⟩ r
    rintro g ⟨_, ⟨n, hn, z, hz, rfl⟩, q, hq, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hle (-mu) hn)
      (P.centralizerTorusImage_le_moyPrasad hZ x r hz)) (hle mu hq)


end Langlands.Geometry.Building.MaximalUnramified.BuildingData

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The exact K-level positive-depth product proposition, at arbitrary universe. -/
theorem localMoyPrasadPositiveProduct : LocalMoyPrasadPositiveProductStatement.{u} := by
  intro F _ _ _ _ H _ B hZ hcomm x r hr mu hmu
  simpa only [BuildingData.depthRootSpan_eq_rootFiltrationSpan] using
    B.moyPrasad_eq_negative_image_positive hZ hcomm x r hr mu hmu

end Langlands.Geometry.Building.MaximalUnramified
