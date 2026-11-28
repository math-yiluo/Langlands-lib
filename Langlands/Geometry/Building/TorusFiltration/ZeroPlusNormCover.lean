import Langlands.Geometry.Building.TorusFiltration.Construction
import Langlands.Geometry.Building.TorusFiltration.GeometricPrincipalUnits
import Langlands.GroupScheme.Torus.InducedEmbedding
import Langlands.GroupScheme.Torus.InducedProducts

/-! # Principal-unit parts of lifts through an induced norm -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme
open Langlands.LocalField Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open scoped BigOperators CategoryTheory.MonObj NNReal TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 180000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F Ω
local notation "Osep" => sepClosureIntegers F

section Factors

variable (E : IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [FiniteDimensional (inertiaFixedField F) E] [IsGalois (inertiaFixedField F) E]
  (I : Type u) [Fintype I] [DecidableEq I]

local notation "C" => (I → ConnectedImage.integers F E)
local notation "S" => WeilGm.commGroupScheme (CommRingCat.of K) (I → E)
local notation "W" => ConnectedImage.model F E I

private theorem normSource_sections_decompose (x : (W).integralSections) :
    ∃ (m : ℕ) (u t : (W).integralSections) (r : ℝ≥0),
      IsUnit (m : Osep) ∧ t ^ m = 1 ∧ x = u * t ∧ 0 < r ∧ r < 1 ∧
        (W).integralPointMap u ∈ localGeometricCharacterCongruence F (S) r := by
  let c := (WeilGm.sectionUnitsEquiv (CommRingCat.of O) C).trans
    (MulEquiv.piUnits (M := fun _ : I => ConnectedImage.integers F E))
  let w := c x
  choose b t m hw ht hm hb using fun i : I => exists_principal_and_torsion F E (w i)
  let n := ∏ i, m i
  let u := c.symm b
  let z := c.symm t
  have hz : z ^ n = 1 := by
    apply c.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply]
    funext i
    obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    change t i ^ n = 1
    rw [show n = m i * a from ha, pow_mul, ht i, one_pow]
  have hn : IsUnit (n : Osep) := by
    simp only [n, Nat.cast_prod]
    exact IsUnit.prod_univ_iff.mpr hm
  have hdecomp : x = u * z := by
    apply c.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact funext hw
  let f (i : I) : WithTop ℝ := ν (((b i : ConnectedImage.integers F E) : E) - 1 : Ω)
  let δ := (Finset.univ : Finset I).inf f
  have hδ : 0 < δ :=
    (Finset.lt_inf_iff (by simp : (0 : WithTop ℝ) < ⊤)).mpr fun i _ => hb i
  obtain ⟨a, ha, haδ⟩ : ∃ a : ℝ, 0 < a ∧ (a : WithTop ℝ) ≤ δ := by
    rcases eq_or_ne δ ⊤ with he | he
    · exact ⟨1, one_pos, he ▸ le_top⟩
    · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp he
      exact ⟨v, WithTop.coe_lt_coe.mp (hv ▸ hδ), hv ▸ le_rfl⟩
  let r : ℝ≥0 := min ⟨a, ha.le⟩ (1 / 2)
  have hr : 0 < r := lt_min ha (by norm_num)
  have hr₁ : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨n, u, z, r, hn, hz, hdecomp, hr, hr₁, ?_⟩
  apply (InducedTorusShallow.mem_geometricCharacterCongruence_iff F (fun _ : I => E) r hr _).mpr
  intro i
  rw [show (W).integralPointMap u =
      (WeilGm.integralModel O K C (I → E) (ConnectedImage.piTensorEquiv F E I)).integralPointMap u from rfl,
    WeilGm.rationalUnitsEquiv_integralPointMap, ConnectedImage.piTensorEquiv_tmul,
    map_one, one_mul]
  have hu : (WeilGm.sectionUnitsEquiv (CommRingCat.of O) C u : C) i = b i := by
    exact congrArg (fun w : ∀ _ : I, (ConnectedImage.integers F E)ˣ =>
      (w i : ConnectedImage.integers F E)) (c.apply_symm_apply b)
  rw [hu]
  exact (show ((r : ℝ) : WithTop ℝ) ≤ (a : WithTop ℝ) by
    exact_mod_cast (min_le_left (⟨a, ha.le⟩ : ℝ≥0) (1 / 2))).trans
      (haδ.trans (Finset.inf_le (Finset.mem_univ i)))

end Factors

/-- The bounded norm source of the connected Néron point group can be chosen
induced. Every integral lift decomposes into a positive-depth point and a
torsion point of order a unit in the separable valuation ring. -/
theorem exists_induced_normCover_decomposed
    (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left] (hT : IsTorus T.toGrp) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of K)))
      (_hS : IsInducedTorus S) (n : S ⟶ T) (W : IntegralModel O K S.toGrp),
      W.IsSmooth ∧
      W.integralPoints.map (rationalPoints.map (CommGroupScheme.groupHom n)) =
        (connectedNeronModel F T hT).integralPoints ∧
      ∀ x : W.integralSections, ∃ (m : ℕ) (u t : W.integralSections) (r : ℝ≥0),
        IsUnit (m : Osep) ∧ t ^ m = 1 ∧ x = u * t ∧ 0 < r ∧ r < 1 ∧
          W.integralPointMap u ∈ localGeometricCharacterCongruence F S r := by
  classical
  let L := localTorusSplittingData F T hT
  obtain ⟨I, hI, ⟨σ⟩⟩ := L.splits
  let : Fintype I := Fintype.ofFinite I
  let : Algebra K (I → L.L) := Pi.algebra _ _
  let : Module K (I → L.L) := Algebra.toModule
  let : Module.Finite K (I → L.L) := Module.Finite.pi
  let : Module.Projective K (I → L.L) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace K _)
  let S := WeilGm.commGroupScheme (CommRingCat.of K) (I → L.L)
  let B := ∀ i, GaloisLatticeRealization.topFamily K L.L I i
  let eB : B ≃ₐ[K] (I → L.L) :=
    AlgEquiv.piCongrRight fun _ : I => IntermediateField.topEquiv (F := K) (E := L.L)
  let : Module.Finite K B := Module.Finite.pi
  let : Module.Projective K B := Module.Projective.of_basis (Module.Basis.ofVectorSpace K B)
  let e : GaloisLatticeRealization.permTorus K L.L I ≅ S :=
    WeilGm.commCongrIso (A := CommRingCat.of K) eB
  let eGrp : S.toGrp ≅ (GaloisLatticeRealization.permTorus K L.L I).toGrp :=
    { hom := CommGroupScheme.groupHom e.inv
      inv := CommGroupScheme.groupHom e.hom
      hom_inv_id := congrArg Additive.toMul e.inv_hom_id
      inv_hom_id := congrArg Additive.toMul e.hom_inv_id }
  have hS : IsInducedTorus S := IsInducedTorus.of_iso eGrp (InducedEmbedding.permTorus_isInduced I)
  let T_L := baseChanged K L.L T.toGrp
  let : IsAffineHom T_L.X.hom := L.splits.isAffineHom
  let : IsAffine T_L.X.left := isAffine_of_isAffineHom T_L.X.hom
  let : Smooth T_L.X.hom := L.splits.smooth
  let : Module.Projective O (I → ConnectedImage.integers F L.L) := Module.Projective.of_free
  let W := ConnectedImage.model F L.L I
  let n : S ⟶ T := Additive.ofMul (ConnectedImage.normMap F L.L I T σ)
  refine ⟨S, hS, n, W, WeilGm.integralModel_isSmooth _ _ _ _ _, ?_, ?_⟩
  · rw [connectedNeronModel_integralPoints, localTorusFiltration_zero F L.L T hT L.splits]
    exact ConnectedImage.map_model_integralPoints F L.L I T σ
  · exact normSource_sections_decompose F L.L I

end Langlands.Geometry.Building
