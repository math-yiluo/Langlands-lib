import Langlands.Geometry.Building.UnramifiedTraceCosetDescent
import Langlands.Geometry.Building.RootGroupLinearization
import Langlands.Geometry.Building.UnramifiedFixedPointRootDescent
import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.Geometry.Building.RootJumpLiftNonMultipliable
import Langlands.Geometry.Building.RootBuildingGaloisFieldExtension
import Langlands.GroupScheme.ComponentGaloisContinuityProof
import Langlands.GroupScheme.GaloisPointDescent
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction
import Langlands.Geometry.Building.RootGroupLinearizationProof
import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.GroupScheme.Rational.RankOneParabolicCovering
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveProof

/-! # Forward descent of the absence of a zero-value jump

For `K = F^ur`, a split torus `S` of `G` and a root `α`, a family `ψ` of root functions of
`(G_K, S_K)` satisfying an ultrametric inequality (H1), `Aut(K/F)`-invariance (H2) and
invariance under the valuation-one points of `S_K` (H3) on `U_{α_K}(K)`: if `0` is not a jump
of `α_K` for `ψ`, then `0` is not a jump of `α` for `fieldRestrict ψ`. The proof removes the
`U_{2α_K}(K)`-component of a factorization by Galois descent of a cocycle with values in the
positive-value part of `U_{2α_K}(K)`. `unramifiedZeroJump_forwardDescent` has the exact type of
the hypothesis `hfwd` of `unramifiedZeroJumpFieldComparison_of_galoisDescent`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- `U_{2a}(k) ≤ U_a(k)`, with the convention `U_{2a}(k) = {1}` when `2a` is not a root. -/
theorem doubleRootGroupPoints_le_rootGroupPoints {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S) :
    doubleRootGroupPoints i a ≤ rootGroupPoints i a := by
  unfold doubleRootGroupPoints
  split_ifs
  · exact RelativeRoot.subgroup_nsmul_le i a (show 0 < (2 : ℕ) by norm_num) _
  · exact bot_le

/-- A rational point of a scalar extension of a group of finite type is fixed by the fixing
subgroup of some finite intermediate field. (A one-point copy of
`TwistedGeneratorReduction.exists_finite_fixing_rationalPoints`, restated here so that this
module does not import `UnramifiedTwistedChamberThroughFixedPointReduction`.) -/
theorem exists_finite_fixing_rationalPoint (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (g : rationalPoints (baseChanged k K G)) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, rationalConjugate k K G σ g = g := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨E, hE, hfix⟩ := IdentityComponent.exists_finite_fixing_algHoms k K
    (fun _ : PUnit.{u + 1} => GaloisPoint.coordinates k G K (baseChangeCoeffEquiv k K G g))
  refine ⟨E, hE, fun σ hσ => ?_⟩
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate]
  apply (GaloisPoint.coordinates k G K).injective
  ext a
  rw [GaloisPoint.coordinates_conjugate]
  exact DFunLike.congr_fun (hfix σ hσ PUnit.unit) a

namespace MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [Smooth G.X.hom]

local notation "K" => inertiaFixedField F
local notation "b" => algebraBaseMap F (inertiaFixedField F)
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)
local notation "a_K" a => characterLattice.baseChange b S a

local instance forwardDescent_isAffineHom_baseChange : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Forward descent of the absence of a zero-value jump, given semilinear coordinates.**
Let `K = F^ur`, `α` a root of `(G, S)` for a split torus `S`, and `ψ` a family of root
functions of `(G_K, S_K)` satisfying on `U_{α_K}(K)` the ultrametric inequality (H1), invariance
under `Aut(K/F)` (H2) and invariance under conjugation by the points of `S_K` at which every
rational character has valuation one (H3). Given the semilinear coordinates of
`RootGroupLinearization iS α (valuation F)`, if `0` is not a jump of `α_K` for `ψ`, then `0` is
not a jump of `α` for `fieldRestrict ψ`. -/
theorem not_isRootFiltrationJump_fieldRestrict_of_linearization
    (iS : S.toGrp ⟶ G) [Mono iS.hom.hom.left] (hS : IsSplitTorus S.toGrp)
    {α : characterLattice S} (hα : α ∈ relativeRoots iS)
    (hlin : RootGroupLinearization iS α (valuation F))
    (ψ : RootFunctionFamily S_K G_K)
    (H1 : ∀ g ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K α),
      ∀ h ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K α),
        min (ψ (a_K α) g) (ψ (a_K α) h) ≤ ψ (a_K α) (g * h⁻¹))
    (H2 : ∀ σ : K ≃ₐ[F] K, ∀ g ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K α),
      ψ (a_K α) (rationalConjugate F K G σ g) = ψ (a_K α) g)
    (H3 : ∀ t ∈ characterValuationKernel (valuation F) (S_K).toGrp,
      ∀ g ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K α),
        ψ (a_K α) (rationalPoints.map (j_K iS) t * g * (rationalPoints.map (j_K iS) t)⁻¹) =
          ψ (a_K α) g)
    (hK : ¬ IsRootFiltrationJump (j_K iS) ψ (a_K α) 0) :
    ¬ IsRootFiltrationJump iS (RootFunctionFamily.fieldRestrict (k := F) ψ) α 0 := by
  classical
  have hα0 : α ≠ 0 := hα.1
  obtain ⟨n, m, d, q, e, -, -, hq_zero, he_mul, he_inj, hU_conj, hq_conj, he_conj, htorus⟩ :=
    hlin
  have hU₂U : doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α) ≤
      rootGroupPoints (S := S_K) (j_K iS) (a_K α) :=
    doubleRootGroupPoints_le_rootGroupPoints _ _
  have hU₂conj : ∀ σ : K ≃ₐ[F] K, ∀ x ∈ doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α),
      rationalConjugate F K G σ x ∈ doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α) := by
    intro σ x hx
    have hxU := hU₂U hx
    have hσU := hU_conj σ x hxU
    refine (hq_zero _ hσU).mp ?_
    rw [hq_conj σ x hxU, (hq_zero x hxU).mpr hx]
    funext i
    simp
  intro hJ
  apply hJ
  intro g hg
  have hgU : g ∈ rootGroupPoints iS α := hg.1
  rw [rootFiltration_fieldRestrict iS hS ψ α hα0 0] at hg
  obtain ⟨u, ⟨huU, hu⟩, z, hz, huz⟩ := Set.mem_mul.mp ((not_not.mp hK) hg)
  -- Positivity on `U_{α_K}(K)` from the ultrametric inequality.
  have hψ1 : (0 : WithTop ℝ) < ψ (a_K α) 1 := by
    have h := H1 u huU u huU
    rw [min_self, mul_inv_cancel] at h
    exact lt_of_lt_of_le hu h
  have hpos_inv : ∀ y ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K α),
      (0 : WithTop ℝ) < ψ (a_K α) y → (0 : WithTop ℝ) < ψ (a_K α) y⁻¹ := by
    intro y hy hpos
    have h := H1 1 (Subgroup.one_mem _) y hy
    rw [one_mul] at h
    exact lt_of_lt_of_le (lt_min hψ1 hpos) h
  have hpos_mul : ∀ x ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K α),
      ∀ y ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K α),
      (0 : WithTop ℝ) < ψ (a_K α) x → (0 : WithTop ℝ) < ψ (a_K α) y →
        (0 : WithTop ℝ) < ψ (a_K α) (x * y) := by
    intro x hx y hy hxpos hypos
    have h := H1 x hx y⁻¹ (Subgroup.inv_mem _ hy)
    rw [inv_inv] at h
    exact lt_of_lt_of_le (lt_min hxpos (hpos_inv y hy hypos)) h
  by_cases h2 : 2 • α ∈ relativeRoots iS
  · -- `2α` is a root: remove the `U_{2α_K}(K)`-component by a Galois-fixed point.
    have h2K : 2 • (a_K α) ∈ relativeRoots (T := S_K) (j_K iS) := by
      rw [← map_nsmul]
      exact (mem_roots_baseChange_iff G S hS iS (2 • α)).mpr h2
    have hU₂eq : doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α) =
        rootGroupPoints (S := S_K) (j_K iS) (a_K (2 • α)) := by
      unfold doubleRootGroupPoints
      rw [ite_eq_left h2K, map_nsmul]
    have hU₂F : doubleRootGroupPoints iS α = rootGroupPoints iS (2 • α) := by
      unfold doubleRootGroupPoints
      rw [ite_eq_left h2]
    -- The stable subgroup `B` of positive-value points of `U_{2α_K}(K)`.
    let B : Subgroup (rationalPoints G_K) :=
      { carrier := {y | y ∈ doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α) ∧
          (0 : WithTop ℝ) < ψ (a_K α) y}
        one_mem' := ⟨Subgroup.one_mem _, hψ1⟩
        mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1,
          hpos_mul x (hU₂U hx.1) y (hU₂U hy.1) hx.2 hy.2⟩
        inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, hpos_inv x (hU₂U hx.1) hx.2⟩ }
    have hmemB : ∀ y, y ∈ B ↔ y ∈ doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α) ∧
        (0 : WithTop ℝ) < ψ (a_K α) y := fun _ => Iff.rfl
    have hB : ∀ σ, ∀ x ∈ B, rationalConjugateAction F K G σ x ∈ B := by
      intro σ x hx
      rw [hmemB] at hx ⊢
      rw [rationalConjugateAction_apply]
      exact ⟨hU₂conj σ x hx.1, by rw [H2 σ x (hU₂U hx.1)]; exact hx.2⟩
    have hsq : ∀ c : Kˣ, valuation F (c : K) = 1 →
        ∀ x ∈ B, ∃ y ∈ B, e y = (c : K) ^ 2 • e x := by
      intro c hc x hx
      rw [hmemB] at hx
      obtain ⟨t, ht, -, hconjU, hconj₂⟩ := htorus c hc
      have hxU := hU₂U hx.1
      obtain ⟨hyU, hyq⟩ := hconjU x hxU
      refine ⟨rationalPoints.map (j_K iS) t * x * (rationalPoints.map (j_K iS) t)⁻¹, ?_,
        hconj₂ x hx.1⟩
      rw [hmemB]
      refine ⟨(hq_zero _ hyU).mp ?_, by rw [H3 t ht x hxU]; exact hx.2⟩
      rw [hyq, (hq_zero x hxU).mpr hx.1, smul_zero]
    obtain ⟨E₀, hE₀, hfix₀⟩ := exists_finite_fixing_rationalPoint F K (G := G) z⁻¹
    have hzU₂ : z ∈ doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α) := hz
    have hw₀B : ∀ σ, (z⁻¹)⁻¹ * rationalConjugateAction F K G σ z⁻¹ ∈ B := by
      intro σ
      rw [inv_inv, rationalConjugateAction_apply, map_inv, hmemB]
      have hσz := hU₂conj σ z hzU₂
      refine ⟨Subgroup.mul_mem _ hzU₂ (Subgroup.inv_mem _ hσz), ?_⟩
      have hz_eq : z = u⁻¹ * rationalExtend F K G g := by
        rw [← huz, inv_mul_cancel_left]
      have hσz_eq : rationalConjugate F K G σ z =
          (rationalConjugate F K G σ u)⁻¹ * rationalExtend F K G g := by
        rw [hz_eq, map_mul, map_inv, rationalConjugate_rationalExtend]
      have hkey : z * (rationalConjugate F K G σ z)⁻¹ = u⁻¹ * rationalConjugate F K G σ u := by
        rw [hσz_eq, hz_eq]
        group
      rw [hkey]
      have hσu := hU_conj σ u huU
      exact hpos_mul _ (Subgroup.inv_mem _ huU) _ hσu (hpos_inv u huU hu)
        (by rw [H2 σ u huU]; exact hu)
    obtain ⟨b₁, hb₁, hb₁fix⟩ := exists_fixed_mul_of_unitSquare_scaling
      (rationalConjugateAction F K G) B hB e
      (fun x hx y hy => he_mul x ((hmemB x).mp hx).1 y ((hmemB y).mp hy).1)
      (fun x hx => he_inj x ((hmemB x).mp hx).1)
      (fun σ x hx => he_conj σ x ((hmemB x).mp hx).1) hsq E₀ z⁻¹
      hfix₀ hw₀B
    have hb₁' := (hmemB b₁).mp hb₁
    have hwU₂ : z⁻¹ * b₁ ∈ rootGroupPoints (S := S_K) (j_K iS) (a_K (2 • α)) := by
      rw [← hU₂eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzU₂) hb₁'.1
    obtain ⟨z₀, hz₀, hz₀ext⟩ := exists_mem_rootGroupPoints_of_galoisFixed F iS hS (2 • α) h2.1
      (fun σ => hb₁fix σ) hwU₂
    have hz₀₂ : z₀ ∈ doubleRootGroupPoints iS α := by
      rw [hU₂F]
      exact hz₀
    refine Set.mem_mul.mpr ⟨g * z₀, ⟨Subgroup.mul_mem _ hgU
      (doubleRootGroupPoints_le_rootGroupPoints iS α hz₀₂), ?_⟩, z₀⁻¹,
      Subgroup.inv_mem _ hz₀₂, mul_inv_cancel_right g z₀⟩
    rw [RootFunctionFamily.fieldRestrict_apply, map_mul, hz₀ext, ← huz]
    have hprod : u * z * (z⁻¹ * b₁) = u * b₁ := by group
    rw [hprod]
    exact hpos_mul u huU b₁ (hU₂U hb₁'.1) hu hb₁'.2
  · -- `2α` is not a root: `U_{2α_K}(K) = 1`, so `g_K = u`.
    have h2K : 2 • (a_K α) ∉ relativeRoots (T := S_K) (j_K iS) := by
      rw [← map_nsmul]
      exact fun h => h2 ((mem_roots_baseChange_iff G S hS iS (2 • α)).mp h)
    have hz1 : z = 1 := by
      have hz' : z ∈ doubleRootGroupPoints (S := S_K) (j_K iS) (a_K α) := hz
      unfold doubleRootGroupPoints at hz'
      rw [ite_eq_right h2K] at hz'
      exact (Subgroup.mem_bot.mp hz')
    rw [hz1, mul_one] at huz
    refine Set.mem_mul.mpr ⟨g, ⟨hgU, ?_⟩, 1, ?_, mul_one g⟩
    · rw [RootFunctionFamily.fieldRestrict_apply, ← huz]
      exact hu
    · exact Subgroup.one_mem _

end MaximalUnramified

namespace MaximalUnramified

set_option maxHeartbeats 1600000 in
/-- **Forward descent of the absence of a zero-value jump.** Let `F` be a non-archimedean local
field, `K = F^ur`, `G` a connected reductive `F`-group with a maximal split torus `S`, `α` a
root of `(G, S)`, and `ψ` a family of root functions of `(G_K, S_K)` satisfying on
`U_{α_K}(K)` the ultrametric inequality (H1), invariance under `Aut(K/F)` (H2) and invariance
under conjugation by the points of `S_K` at which every rational character has valuation one
(H3). If `0` is not a jump of `α_K` for `ψ`, then `0` is not a jump of `α` for
`fieldRestrict ψ`. -/
theorem unramifiedZeroJump_forwardDescent :
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
      (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
      (hiS : IsMaximalSplitTorus iS),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : Smooth G.X.hom := hG.smooth
      haveI := mono_of_isMaximalSplitTorus hiS
      ∀ α ∈ relativeRoots iS,
      ∀ ψ : RootFunctionFamily
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G),
        (∀ g ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ∀ h ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          min (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g)
              (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) h) ≤
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) (g * h⁻¹)) →
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          ∀ g ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalConjugate F (inertiaFixedField F) G σ g) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        (∀ t ∈ characterValuationKernel (MaximalUnramified.valuation F)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S).toGrp,
          ∀ g ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) t *
                g * (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) t)⁻¹) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        ¬ IsRootFiltrationJump ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ψ
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) 0 →
          ¬ IsRootFiltrationJump iS (RootFunctionFamily.fieldRestrict (k := F) (K := inertiaFixedField F) ψ) α 0 := by
  intro F _ _ _ _ G hG S iS hiS
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro α hα ψ H1 H2 H3 hK
  have hS : IsSplitTorus S.toGrp := hiS.isSplitSubtorus.1
  have hEbase : RelativeRoot.HasOppositeFactorPairs iS := fun a ha g hg _ =>
    RelativeRoot.exists_oppositeFactorPair_of_componentReductivity
      RelativeRoot.kernelCentralizerComponentReductive F G hG S iS hiS a ha.1 g hg
  exact not_isRootFiltrationJump_fieldRestrict_of_linearization iS hS hα
    (rootGroupLinearization iS hS hEbase hα (valuation F)) ψ H1 H2 H3 hK

end MaximalUnramified

end Langlands.Geometry.Building
