import Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityStatement
import Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslation
import Langlands.Geometry.Building.ValuationDerivativeAffineRoots
import Langlands.Geometry.Building.ValuationBuildingTopologyCompatible
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-!
# The translation part of AS 5 from simple-root transitivity

This module proves `ValuationBuildingQuasiSplitAdjointTranslationStatement` from
`QuasiSplitAdjointSimpleRootTransitivityStatement`. Let `v` be a translation of the
apartment that preserves `Ψ`. For each `a ∈ Δ`, the values at a point `x` of the affine
roots with gradient `a` are the jumps of `U_a/U_{2a}` at `x`. Since `Ψ` is preserved,
`r` and `r + a(v)` are both jumps for some `r`. Transitivity and axiom V 6 give `z_a ∈ Z(F)`
with `a(ν(z_a)) = a(v)` and `b(ν(z_a)) = 0` for the other `b ∈ Δ`. The product `z` of the
`z_a` satisfies `b(ν(z)) = b(v)` for every `b ∈ Δ`, hence for every root, so `v` is the
class of `ν(z)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- `Z(F)` normalizes each root group `U_a(F)`. -/
theorem centralizer_conj_mem_rootGroup (z : rationalPoints B.centralizer.Z)
    {a : characterLattice B.S} {u : rationalPoints G} (hu : u ∈ B.rootGroup a) :
    rationalPoints.map B.centralizer.j z * u * (rationalPoints.map B.centralizer.j z)⁻¹ ∈
      B.rootGroup a := by
  have h := conj_mem_rootGroupPoints (B.centralizer.toNormalizer z) hu
  rwa [weylAction_centralizerToNormalizer, LinearEquiv.coe_one, id] at h

/-- `Z(F)` normalizes `U_{2a}(F)`. -/
theorem centralizer_conj_mem_doubleRootGroup (z : rationalPoints B.centralizer.Z)
    {a : characterLattice B.S} {u : rationalPoints G} (hu : u ∈ B.doubleRootGroup a) :
    rationalPoints.map B.centralizer.j z * u * (rationalPoints.map B.centralizer.j z)⁻¹ ∈
      B.doubleRootGroup a := by
  unfold ValuationBuildingData.doubleRootGroup doubleRootGroupPoints at hu ⊢
  split_ifs at hu ⊢ with h2
  · exact B.centralizer_conj_mem_rootGroup z hu
  · rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, mul_one, mul_inv_cancel]

theorem centralizer_inv_conj_mem_rootGroup (z : rationalPoints B.centralizer.Z)
    {a : characterLattice B.S} {u : rationalPoints G} (hu : u ∈ B.rootGroup a) :
    (rationalPoints.map B.centralizer.j z)⁻¹ * u * rationalPoints.map B.centralizer.j z ∈
      B.rootGroup a := by
  have h := B.centralizer_conj_mem_rootGroup z⁻¹ hu
  rwa [map_inv, inv_inv] at h

theorem centralizer_inv_conj_mem_doubleRootGroup (z : rationalPoints B.centralizer.Z)
    {a : characterLattice B.S} {u : rationalPoints G} (hu : u ∈ B.doubleRootGroup a) :
    (rationalPoints.map B.centralizer.j z)⁻¹ * u * rationalPoints.map B.centralizer.j z ∈
      B.doubleRootGroup a := by
  have h := B.centralizer_conj_mem_doubleRootGroup z⁻¹ hu
  rwa [map_inv, inv_inv] at h

/-- Axiom V 6 at a point of the apartment: `x_a(z⁻¹ u z) = x_a(u) + a(ν(z))`. -/
theorem val_centralizer_conj (x : B.Apartment) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) (z : rationalPoints B.centralizer.Z) {u : rationalPoints G}
    (hu : u ∈ B.rootGroup a) :
    x.val a ((rationalPoints.map B.centralizer.j z)⁻¹ * u * rationalPoints.map B.centralizer.j z) =
      x.val a u + ((eval B.S a (B.translation z).toAdd : ℝ) : WithTop ℝ) :=
  B.isOmegaCompatible x.val x.mem a ha z u hu

/-- `r` is a jump of `U_a(F)/U_{2a}(F)` at `x`: some `u ∈ U_{a,x,r}` does not lie in
`U_{a,x,r+} U_{2a}(F)`. -/
def IsRootJump (x : B.Apartment) (a : characterLattice B.S) (r : ℝ) : Prop :=
  ∃ u ∈ B.rootGroup a, (r : WithTop ℝ) ≤ x.val a u ∧
    ∀ p ∈ B.rootGroup a, (r : WithTop ℝ) < x.val a p → ∀ w ∈ B.doubleRootGroup a, p * w ≠ u

/-- The value at `x` of an affine root with gradient `a` is a jump of `U_a/U_{2a}` at `x`
(KP Definition 6.3.4). -/
theorem isRootJump_of_mem_affineRoots (x : B.Apartment) (α : relativeRoots B.i)
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) (hlin : ψ.linear = rootForm B.i α) :
    B.IsRootJump x α (ψ x) := by
  obtain ⟨β, hβ, hnot⟩ := hψ
  have hβα : β = α :=
    Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split
      B.isMaximalSplitTorus.isSplitSubtorus.1 B.i (hβ.symm.trans hlin)
  subst hβα
  rw [Set.not_subset] at hnot
  obtain ⟨u, hu, hnu⟩ := hnot
  rw [SetLike.mem_coe, KPApartmentData.mem_affineRootGroup_iff hlin x] at hu
  refine ⟨u, hu.1, hu.2, fun p hp hlt w hw hpw => hnu ?_⟩
  rw [← hpw]
  exact Set.mul_mem_mul ((KPApartmentData.mem_affineRootGroupPlus_iff hlin x).2 ⟨hp, hlt⟩) hw

theorem not_mem_doubleRootGroup_of_isRootJump_witness (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) {r : ℝ} {u : rationalPoints G}
    (hu : ∀ p ∈ B.rootGroup a, (r : WithTop ℝ) < x.val a p →
      ∀ w ∈ B.doubleRootGroup a, p * w ≠ u) : u ∉ B.doubleRootGroup a := by
  intro hmem
  have h1 : x.val a 1 = ⊤ :=
    (x.isValuation.eq_top_iff a ha 1 (B.rootGroup a).one_mem).2 rfl
  exact hu 1 (B.rootGroup a).one_mem (by rw [h1]; exact WithTop.coe_lt_top r) u hmem
    (one_mul u)

/-- If `Z(F)` has the transitivity of `QuasiSplitAdjointSimpleRootTransitivityStatement` at
`a`, then for any two jumps `r, s` of `U_a/U_{2a}` at `x` some `z ∈ Z(F)` has
`a(ν(z)) = r - s` and `b(ν(z)) = 0` for the other `b ∈ Δ`. -/
theorem exists_eval_translation_of_isRootJump (x : B.Apartment) {Δ : Finset (characterLattice B.S)}
    (hΔ : ∀ b ∈ Δ, b ∈ relativeRoots B.i) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i)
    (htr : ∀ u ∈ B.rootGroup a, ∀ u' ∈ B.rootGroup a,
      u ∉ B.doubleRootGroup a → u' ∉ B.doubleRootGroup a →
      ∃ z : rationalPoints B.centralizer.Z,
        (∀ b ∈ Δ, b ≠ a → ∀ g ∈ B.rootGroup b,
          Commute (rationalPoints.map B.centralizer.j z) g) ∧
        ∃ w ∈ B.doubleRootGroup a,
          rationalPoints.map B.centralizer.j z * u * (rationalPoints.map B.centralizer.j z)⁻¹ =
            u' * w)
    {r s : ℝ} (hr : B.IsRootJump x a r) (hs : B.IsRootJump x a s) :
    ∃ z : rationalPoints B.centralizer.Z,
      (∀ b ∈ Δ, b ≠ a → eval B.S b (B.translation z).toAdd = 0) ∧
        eval B.S a (B.translation z).toAdd = r - s := by
  obtain ⟨u, hu, hur, hu'⟩ := hr
  obtain ⟨u', hu'm, hu's, hu''⟩ := hs
  obtain ⟨z, hcomm, w, hw, hconj⟩ :=
    htr u hu u' hu'm (B.not_mem_doubleRootGroup_of_isRootJump_witness x ha hu')
      (B.not_mem_doubleRootGroup_of_isRootJump_witness x ha hu'')
  refine ⟨z, fun b hb hba => ?_, ?_⟩
  · obtain ⟨y, hy, hytop⟩ := x.isValuation.exists_ne_top (hΔ b hb)
    have h := B.val_centralizer_conj x (hΔ b hb) z hy
    have hc : (rationalPoints.map B.centralizer.j z)⁻¹ * y *
        rationalPoints.map B.centralizer.j z = y := by
      rw [mul_assoc, ← (hcomm b hb hba y hy).eq, inv_mul_cancel_left]
    rw [hc] at h
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hytop
    rw [← ht, ← WithTop.coe_add, WithTop.coe_inj] at h
    linarith
  · set g := rationalPoints.map B.centralizer.j z with hg
    set c := eval B.S a (B.translation z).toAdd with hc
    have hgu : g * u * g⁻¹ ∈ B.rootGroup a := B.centralizer_conj_mem_rootGroup z hu
    have hu'w : u' * w ∈ B.rootGroup a := hconj ▸ hgu
    have h1 := B.val_centralizer_conj x ha z hu'w
    have hback : g⁻¹ * (u' * w) * g = u := by rw [← hconj]; group
    rw [hback] at h1
    have h2 := B.val_centralizer_conj x ha z hu'm
    have hle : r - c ≤ s := by
      by_contra hlt
      push Not at hlt
      apply hu'' (u' * w) hu'w ?_ w⁻¹ ((B.doubleRootGroup a).inv_mem hw) (by group)
      rw [h1] at hur
      induction hv : x.val a (u' * w) using WithTop.recTopCoe with
      | top => exact WithTop.coe_lt_top s
      | coe t =>
        rw [hv, ← WithTop.coe_add, WithTop.coe_le_coe] at hur
        exact WithTop.coe_lt_coe.2 (by linarith)
    have hge : s ≤ r - c := by
      by_contra hlt
      push Not at hlt
      apply hu' (g⁻¹ * u' * g) (B.centralizer_inv_conj_mem_rootGroup z hu'm) ?_
        (g⁻¹ * w * g) (B.centralizer_inv_conj_mem_doubleRootGroup z hw)
      · calc g⁻¹ * u' * g * (g⁻¹ * w * g) = g⁻¹ * (u' * w) * g := by group
          _ = u := hback
      · rw [h2]
        induction hv : x.val a u' using WithTop.recTopCoe with
        | top => rw [WithTop.top_add]; exact WithTop.coe_lt_top r
        | coe t =>
          rw [hv, WithTop.coe_le_coe] at hu's
          rw [← WithTop.coe_add, WithTop.coe_lt_coe]
          linarith
    linarith

end ValuationBuildingData

open ValuationBuildingData in
/-- **The translation part of AS 5 from simple-root transitivity.**
`QuasiSplitAdjointSimpleRootTransitivityStatement` implies
`ValuationBuildingQuasiSplitAdjointTranslationStatement`. -/
theorem valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity
    (h : QuasiSplitAdjointSimpleRootTransitivityStatement.{u}) :
    ValuationBuildingQuasiSplitAdjointTranslationStatement.{u} := by
  classical
  intro F _ _ _ _ G _ B hqs had v hv
  obtain ⟨Δ, hΔ, hgen, htr⟩ := h F G hqs had B.S B.i B.isMaximalSplitTorus B.centralizer.Z
    B.centralizer.j B.centralizer.isRepresentedBy
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  let x : B.Apartment := Classical.arbitrary _
  have hroot : ∀ a ∈ Δ, ∃ z : rationalPoints B.centralizer.Z,
      (∀ b ∈ Δ, b ≠ a → eval B.S b (B.translation z).toAdd = 0) ∧
        eval B.S a (B.translation z).toAdd = eval B.S a w := by
    intro a haΔ
    have ha := hΔ a haΔ
    let α : relativeRoots B.i := ⟨a, ha⟩
    have hder := derivativeRoots_affineRoots_of_isTopologyCompatible B.isTopologyCompatible
    obtain ⟨ψ, hψ, hlin⟩ : rootForm B.i α ∈ AffineRootSystem.derivativeRoots B.affineRoots := by
      rw [hder]
      exact ⟨α, rfl⟩
    set e : B.Apartment →ᵃ[ℝ] B.Apartment :=
      (AffineEquiv.constVAdd ℝ B.Apartment
        (Submodule.Quotient.mk w : TranslationSpace B.i) : B.Apartment →ᵃ[ℝ] B.Apartment)
      with he
    have hψ' : ψ.comp e ∈ B.affineRoots := (hv ψ).2 hψ
    have hlin' : (ψ.comp e).linear = rootForm B.i α := by
      rw [← hlin]
      exact LinearMap.ext fun y => rfl
    have hval : (ψ.comp e) x = ψ x + eval B.S a w := by
      have hl : ψ.linear = rootForm B.i α := hlin
      change ψ ((Submodule.Quotient.mk w : TranslationSpace B.i) +ᵥ x) = _
      rw [AffineMap.map_vadd, hl, rootForm_mk, vadd_eq_add, add_comm]
    obtain ⟨z, hz0, hz⟩ := B.exists_eval_translation_of_isRootJump x hΔ ha (htr a haΔ)
      (B.isRootJump_of_mem_affineRoots x α hψ' hlin')
      (B.isRootJump_of_mem_affineRoots x α hψ hlin)
    refine ⟨z, hz0, ?_⟩
    rw [hz, hval]
    ring
  have hall : ∀ s : Finset (characterLattice B.S), s ⊆ Δ → ∃ z : rationalPoints B.centralizer.Z,
      (∀ b ∈ s, eval B.S b (B.translation z).toAdd = eval B.S b w) ∧
        ∀ b ∈ Δ, b ∉ s → eval B.S b (B.translation z).toAdd = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, fun b hb => absurd hb (Finset.notMem_empty b), fun b _ _ => ?_⟩
      rw [map_one, toAdd_one, map_zero]
    | insert a s has ih =>
      intro hs
      obtain ⟨z, hzs, hz0⟩ := ih ((Finset.subset_insert a s).trans hs)
      have haΔ := hs (Finset.mem_insert_self a s)
      obtain ⟨za, hza0, hza⟩ := hroot a haΔ
      refine ⟨z * za, fun b hb => ?_, fun b hb hbs => ?_⟩
      · rw [map_mul, toAdd_mul, map_add]
        rcases Finset.mem_insert.1 hb with rfl | hbs
        · rw [hz0 b haΔ has, hza, zero_add]
        · have hba : b ≠ a := fun h => has (h ▸ hbs)
          rw [hzs b hbs, hza0 b (hs hb) hba, add_zero]
      · have hba : b ≠ a := fun h => hbs (h ▸ Finset.mem_insert_self a s)
        have hbs' : b ∉ s := fun h => hbs (Finset.mem_insert_of_mem h)
        rw [map_mul, toAdd_mul, map_add, hz0 b hb hbs', hza0 b hb hba, add_zero]
  obtain ⟨z, hz, -⟩ := hall Δ subset_rfl
  have key : ∀ b ∈ AddSubgroup.closure (Δ : Set (characterLattice B.S)),
      eval B.S b (B.translation z).toAdd = eval B.S b w := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem c hc => exact hz c hc
    | zero => rw [eval_zero_char, eval_zero_char]
    | add c d _ _ hc hd => rw [eval_add_char, eval_add_char, hc, hd]
    | neg c _ hc => rw [eval_neg_char, eval_neg_char, hc]
  refine ⟨z, ?_⟩
  rw [Submodule.Quotient.eq, mem_rootAnnihilator]
  intro b hb
  rw [map_sub, sub_eq_zero]
  exact key b (hgen b hb)

end Langlands.Geometry.Building
