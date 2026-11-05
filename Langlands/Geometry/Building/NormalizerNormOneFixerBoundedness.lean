import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeWeylSpanFiniteness
import Langlands.LinearAlgebra.RationalRealSpan
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-!
# Boundedness of the norm-one stabilizer of a point in `N(F)`

For building data `B` and a point `x` of the apartment, the subgroup
`N(F)^1_x = {n ∈ N(F) | n ∈ G(F)^1, n · x = x}` of `G(F)` lies in finitely many
translates `n_w · j(Z(F)^1)`, one for each class `w` of the finite relative Weyl
group `N(F)/Z(F)` (KP Corollary 7.3.14, second half of the proof). Hence it is
bounded as soon as `j(Z(F)^1)` is bounded. Boundedness of `Z(F)^1` is an explicit
premise here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.LinearAlgebra.RationalSpan Langlands.BruhatTits

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- On a split torus, a real cocharacter killed by a set of characters whose
rationalizations span `ℚ ⊗ X*(T)` is zero. -/
theorem eq_zero_of_eval_eq_zero_of_span (hT : IsSplitTorus T.toGrp)
    {R : Set (characterLattice T)} (hR : Submodule.span ℚ (toRat '' R) = ⊤)
    {v : V T} (hv : ∀ χ ∈ R, eval T χ v = 0) : v = 0 := by
  have := isPerfPair_of_isSplitTorus hT
  let φ : (ℚ ⊗[ℤ] characterLattice T) →ₗ[ℚ] ℝ :=
    (((pair T).flip v).restrictScalars ℚ).comp (toReal (characterLattice T))
  have hφ : ∀ χ, φ (toRat χ) = eval T χ v := by
    intro χ
    simp only [φ, LinearMap.comp_apply, toReal_toRat, LinearMap.restrictScalars_apply,
      LinearMap.flip_apply, eval_eq_pair]
  have hker : Submodule.span ℚ (toRat '' R) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ ⟨χ, hχ, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hφ, hv χ hχ]
  rw [hR] at hker
  have hall : ∀ χ, eval T χ v = 0 := fun χ => by
    rw [← hφ]
    exact LinearMap.mem_ker.mp (hker Submodule.mem_top)
  apply (LinearMap.IsPerfPair.bijective_right (pair T)).injective
  rw [map_zero]
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply, LinearMap.flip_apply]
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    rw [show r ⊗ₜ[ℤ] χ = r • ((1 : ℝ) ⊗ₜ[ℤ] χ) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, LinearMap.smul_apply, ← eval_eq_pair, hall χ, smul_zero]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

end Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

local instance normalizerNormOneFixerBoundednessInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The norm-one stabilizer `N(F)^1_x = {n ∈ N(F) | n ∈ G(F)^1, n · x = x}` of a point
of the apartment, as a subgroup of `G(F)`. -/
def normOneNormalizerStabilizer (x : B.Apartment) : Subgroup (rationalPoints G) :=
  rationalCommonNormKernel G ⊓
    (MulAction.stabilizer (normalizerPoints B.i) x).map (normalizerPoints B.i).subtype

theorem mem_normOneNormalizerStabilizer {x : B.Apartment} {g : rationalPoints G} :
    g ∈ B.normOneNormalizerStabilizer x ↔
      g ∈ rationalCommonNormKernel G ∧
        ∃ n : normalizerPoints B.i, (n : rationalPoints G) = g ∧ n • x = x := by
  simp only [normOneNormalizerStabilizer, Subgroup.mem_inf, Subgroup.mem_map,
    MulAction.mem_stabilizer_iff, Subgroup.coe_subtype]
  exact Iff.rfl.and ⟨fun ⟨n, hn, h⟩ => ⟨n, h, hn⟩, fun ⟨n, h, hn⟩ => ⟨n, hn, h⟩⟩

/-- Restricting a rational character of `G` to `S` is restricting it to `Z` and then to `S`. -/
theorem torusCharacterRestrict_eq_characterRestriction (χ : rationalCharacters G) :
    torusCharacterRestrict B.i χ =
      Cartan.characterRestriction B.centralizer.s (characterRestrict B.centralizer.j χ) := by
  have h : characterRestrict B.i χ =
      characterRestrict B.centralizer.s (characterRestrict B.centralizer.j χ) := by
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, B.centralizer.comp_eq]
  simp only [torusCharacterRestrict, Cartan.characterRestriction, AddMonoidHom.comp_apply, h]

/-- `χ(ν(z)) = -ω(χ(j z))` for a rational character `χ` of `G` restricted to `S`. -/
theorem eval_torusCharacterRestrict_translation (z : rationalPoints B.centralizer.Z)
    (χ : rationalCharacters G) :
    eval B.S (torusCharacterRestrict B.i χ) (B.translation z).toAdd =
      -((rationalCharacterValuation G (rationalPoints.map B.centralizer.j z)).toAdd χ : ℝ) := by
  rw [torusCharacterRestrict_eq_characterRestriction, eval_centralizerTranslation,
    rationalCharacterValuation_apply, rationalCharacterValuation_apply,
    rationalCharacterEval_characterRestrict]

/-- If `z ∈ Z(F)` has `j z ∈ G(F)^1` and fixes a point of the apartment, then
`z ∈ Z(F)^1`: its translation `ν(z)` is killed by the relative roots (it fixes `x`) and
by the restricted characters of `G` (`j z ∈ G(F)^1`), which together span. -/
theorem mem_rationalCommonNormKernel_of_smul_eq (z : rationalPoints B.centralizer.Z)
    (hz : rationalPoints.map B.centralizer.j z ∈ rationalCommonNormKernel G)
    {x : B.Apartment} (hx : B.centralizer.toNormalizer z • x = x) :
    z ∈ rationalCommonNormKernel B.centralizer.Z := by
  rw [← centralizerTranslation_ker, MonoidHom.mem_ker]
  set v : V B.S := (B.translation z).toAdd with hv
  rw [B.isOmegaCompatible.smul_eq_vadd z x] at hx
  have hmk : (Submodule.Quotient.mk v : TranslationSpace B.i) = 0 := by
    rw [← vadd_right_cancel_iff x, zero_vadd]
    exact hx
  rw [Submodule.Quotient.mk_eq_zero, mem_rootAnnihilator] at hmk
  have hspan := relativeRootsRestrictedCharactersSpan F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus
  have hv0 : v = 0 := by
    refine eq_zero_of_eval_eq_zero_of_span B.isMaximalSplitTorus.isSplitSubtorus.1 hspan ?_
    rintro χ (hχ | ⟨ψ, rfl⟩)
    · exact hmk χ hχ
    · rw [hv, eval_torusCharacterRestrict_translation,
        (mem_rationalCommonNormKernel_iff_valuation G _).mp hz ψ, Int.cast_zero, neg_zero]
  change B.translation z = 1
  rw [← toAdd_eq_zero, ← hv, hv0]

/-- `N(F)^1_x` lies in finitely many translates of `j(Z(F)^1)`, one for each class of
`N(F)/Z(F)`. -/
theorem normOneNormalizerStabilizer_subset_iUnion (x : B.Apartment) :
    ∃ r : relativeWeylGroup B.i → rationalPoints G,
      (B.normOneNormalizerStabilizer x : Set (rationalPoints G)) ⊆
        ⋃ w, r w • (rationalPoints.map B.centralizer.j ''
          (rationalCommonNormKernel B.centralizer.Z : Set (rationalPoints B.centralizer.Z))) := by
  classical
  let P : relativeWeylGroup B.i → normalizerPoints B.i → Prop := fun w n =>
    (QuotientGroup.mk n : relativeWeylGroup B.i) = w ∧
      (n : rationalPoints G) ∈ rationalCommonNormKernel G ∧ n • x = x
  refine ⟨fun w => if h : ∃ n, P w n then (h.choose : rationalPoints G) else 1, ?_⟩
  intro g hg
  obtain ⟨hg1, n, rfl, hnx⟩ := (B.mem_normOneNormalizerStabilizer).mp hg
  set w : relativeWeylGroup B.i := QuotientGroup.mk n
  have h : ∃ m, P w m := ⟨n, rfl, hg1, hnx⟩
  obtain ⟨hmw, hm1, hmx⟩ := h.choose_spec
  set m := h.choose
  refine Set.mem_iUnion.mpr ⟨w, ?_⟩
  beta_reduce
  rw [dite_eq_left h]
  have hc : ((m⁻¹ * n : normalizerPoints B.i) : rationalPoints G) ∈ centralizerPoints B.i := by
    rw [← Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq.mp hmw
  rw [← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2] at hc
  obtain ⟨z, hjz⟩ : ∃ z : rationalPoints B.centralizer.Z, rationalPoints.map B.centralizer.j z =
      ((m⁻¹ * n : normalizerPoints B.i) : rationalPoints G) := by
    obtain ⟨z, hz⟩ := hc
    exact ⟨z, hz⟩
  have hz1 : z ∈ rationalCommonNormKernel B.centralizer.Z := by
    refine B.mem_rationalCommonNormKernel_of_smul_eq z ?_ (x := x) ?_
    · rw [hjz, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (inv_mem hm1) hg1
    · have hzn : B.centralizer.toNormalizer z = m⁻¹ * n := Subtype.ext hjz
      rw [hzn, mul_smul, hnx, inv_smul_eq_iff, hmx]
  refine ⟨rationalPoints.map B.centralizer.j z, ⟨z, hz1, rfl⟩, ?_⟩
  show (m : rationalPoints G) * rationalPoints.map B.centralizer.j z = n
  rw [hjz, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

/-- KP Corollary 7.3.14, second half: if `j(Z(F)^1)` is bounded, then so is the
norm-one stabilizer `N(F)^1_x` of every point `x` of the apartment. -/
theorem isAlgebraicallyBounded_normOneNormalizerStabilizer
    (hZ : IsAlgebraicallyBounded F G.X (rationalPoints.map B.centralizer.j ''
      (rationalCommonNormKernel B.centralizer.Z : Set (rationalPoints B.centralizer.Z))))
    (x : B.Apartment) :
    IsAlgebraicallyBounded F G.X (B.normOneNormalizerStabilizer x : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have := (B.isMaximalSplitTorus.isSplitSubtorus.1).finite_relativeWeylGroup_of_span B.i
    (relativeRootsRestrictedCharactersSpan F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus)
  obtain ⟨r, hr⟩ := B.normOneNormalizerStabilizer_subset_iUnion x
  exact (isAlgebraicallyBounded_iUnion fun w => hZ.smul_set (r w)).mono hr

/-- The same conclusion from boundedness of `Z(F)^1` inside `Z(F)`. -/
theorem isAlgebraicallyBounded_normOneNormalizerStabilizer_of_centralizer
    [IsAffine B.centralizer.Z.X.left]
    (hZ : IsAlgebraicallyBounded F B.centralizer.Z.X
      (rationalCommonNormKernel B.centralizer.Z : Set (rationalPoints B.centralizer.Z)))
    (x : B.Apartment) :
    IsAlgebraicallyBounded F G.X (B.normOneNormalizerStabilizer x : Set (rationalPoints G)) :=
  B.isAlgebraicallyBounded_normOneNormalizerStabilizer
    (hZ.image_rationalPointsMap B.centralizer.j) x

end Langlands.Geometry.Building.ValuationBuildingData
