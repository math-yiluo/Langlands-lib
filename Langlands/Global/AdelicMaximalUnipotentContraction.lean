import Langlands.Global.StandardUnipotentEigenCoordinates
import Langlands.Global.AdelicSiegelConjugationBound
import Langlands.Global.AdelicRationalHeightReduction
import Langlands.Global.InfiniteAdelicGroupManifold

/-! # Archimedean contraction in a maximal standard unipotent radical -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory IsDedekindDomain NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
  AdelicGroupPoints InfiniteAdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (rT : T₀ ⟶ T)
  (j : U ⟶ G) {d : ℕ} (hU : SmoothOfRelativeDimension d U.X.hom)

local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "I∞" => 𝓘(ℝ, smoothModel F d)
local notation "A∞" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "Aₐ" => CommAlgCat.of F (Adeles F)
local notation "c∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

section Coordinates

variable {n : ℕ} {t : Fin n → AffineCoordinateRing F U.X}
  (ht : Function.Bijective
    (MvPolynomial.aeval t : MvPolynomial (Fin n) F →ₐ[F] AffineCoordinateRing F U.X))

/-- A polynomial generating system gives global coordinates on the actual infinite points. -/
def archimedeanPolynomialCoordinates : U∞ ≃ₜ (Fin n → E∞) :=
  (((U.affinePointsAlgebraHomeomorph A∞).trans
    ((AlgPoint.congr (AlgEquiv.ofBijective _ ht).symm).trans
      (AlgPoint.polynomialPointHomeomorph (Fin n)))).trans
    (Homeomorph.piCongrRight (fun _ => infiniteAdeleHomeomorph F)))

omit [NumberField F] in
@[simp]
theorem archimedeanPolynomialCoordinates_apply (v : U∞) (a : Fin n) :
    archimedeanPolynomialCoordinates ht v a = c∞ (U.affinePointEvaluation A∞ v (t a)) := by
  change c∞ ((U.affinePointsAlgebraHomeomorph A∞ v) ((MvPolynomial.aeval t) (.X a))) = _
  rw [MvPolynomial.aeval_X, U.affinePointsAlgebraHomeomorph_apply]

/-- The inverse coordinate map is smooth, by polynomial evaluation. -/
theorem contMDiff_archimedeanPolynomialCoordinates_symm :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F U hU
    ContMDiff 𝓘(ℝ, Fin n → E∞) I∞ ∞ (archimedeanPolynomialCoordinates ht).symm := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F U hU
  let S : AffineCoordinateRing F U.X ≃ₐ[F] MvPolynomial (Fin n) F :=
    (AlgEquiv.ofBijective _ ht).symm
  let Q := archimedeanPolynomialCoordinates ht
  have hQinv (v : Fin n → E∞) (a : AffineCoordinateRing F U.X) :
      U.affinePointEvaluation A∞ (Q.symm v) a =
        MvPolynomial.aeval (fun k => c∞.symm (v k)) (S a) := by
    rw [← U.affinePointsAlgebraHomeomorph_apply A∞]
    simp only [Q, archimedeanPolynomialCoordinates, Homeomorph.symm_trans_apply]
    rw [Homeomorph.apply_symm_apply]
    rfl
  apply (contMDiff_iff_coordinateSmooth F U 𝓘(ℝ, Fin n → E∞) hU _).mpr
  intro a
  change ContMDiff 𝓘(ℝ, Fin n → E∞) 𝓘(ℝ, E∞) ∞
    (fun v : Fin n → E∞ => c∞ (U.affinePointEvaluation A∞ (Q.symm v) a))
  simp only [hQinv]
  generalize S a = b
  induction b using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.aeval_C]
      exact contMDiff_const
  | add b e hb he =>
      simp only [map_add]
      exact hb.add he
  | mul_X b k hb =>
      simp only [map_mul, MvPolynomial.aeval_X, RingEquiv.apply_symm_apply]
      have hk : ContMDiff 𝓘(ℝ, Fin n → E∞) 𝓘(ℝ, E∞) ∞ (fun v : Fin n → E∞ => v k) :=
        contMDiff_pi_space.mp contMDiff_id k
      exact (hb.contDiff.mul hk.contDiff).contMDiff

end Coordinates

private theorem exists_add_of_not_mem_closure_diff {X : Type*} [AddCommMonoid X]
    {Δ : Set X} {α χ : X} (hχ : χ ∈ AddSubmonoid.closure Δ)
    (hnot : χ ∉ AddSubmonoid.closure (Δ \ {α})) :
    ∃ β ∈ AddSubmonoid.closure Δ, χ = α + β := by
  suffices ∀ χ ∈ AddSubmonoid.closure Δ,
      χ ∈ AddSubmonoid.closure (Δ \ {α}) ∨
        ∃ β ∈ AddSubmonoid.closure Δ, χ = α + β by
    exact (this χ hχ).resolve_left hnot
  intro x hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      by_cases h : x = α
      · exact Or.inr ⟨0, AddSubmonoid.zero_mem _, by rw [h, add_zero]⟩
      · exact Or.inl (AddSubmonoid.subset_closure ⟨hx, h⟩)
  | zero => exact Or.inl (AddSubmonoid.zero_mem _)
  | add x y hx hy ihx ihy =>
      rcases ihx with hx' | ⟨β, hβ, rfl⟩
      · rcases ihy with hy' | ⟨β, hβ, rfl⟩
        · exact Or.inl (AddSubmonoid.add_mem _ hx' hy')
        · exact Or.inr ⟨x + β, AddSubmonoid.add_mem _ hx hβ, by ac_rfl⟩
      · exact Or.inr ⟨β + y, AddSubmonoid.add_mem _ hβ hy, add_assoc _ _ _⟩

/-- The archimedean decay factor of a relative character, expressed using its full idele norm. -/
def relativeCharacterDecay (χ : characterLattice T) (a : intrinsicSubgroup F T₀) : ℝ :=
  ((normCharacter F T₀ (rT ≫ χ) a : ℝ≥0) : ℝ) ^ (-1 / (Module.finrank ℚ F : ℝ))

theorem relativeCharacterDecay_pos (χ : characterLattice T) (a : intrinsicSubgroup F T₀) :
    0 < relativeCharacterDecay rT χ a := by
  have hp := (normCharacter F T₀ (rT ≫ χ) a).ne_zero.bot_lt
  exact Real.rpow_pos_of_pos (by exact_mod_cast hp) _

private theorem relativeCharacterDecay_eq_inv {χ : characterLattice T} {a : intrinsicSubgroup F T₀}
    {s : ℝ≥0ˣ} (hs : PositiveRealIdeles.full F s = Lie.characterValue (rT ≫ χ) a.val) :
    relativeCharacterDecay rT χ a = ((s : ℝ≥0) : ℝ)⁻¹ := by
  have hD : (Module.finrank ℚ F : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := F)).ne'
  rw [relativeCharacterDecay, normCharacter_apply, ← hs, PositiveRealIdeles.absoluteValue_full,
    Units.val_pow_eq_pow_val, NNReal.coe_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (NNReal.coe_nonneg _), mul_comm, div_mul_cancel₀ _ hD, Real.rpow_neg_one]

omit [LocallyOfFiniteType G.X.hom] in
private theorem exists_relativeCharacterDecay_le (b : ℝ≥0ˣ) {α χ : characterLattice T}
    (hχ : χ ∈ positiveRelativeRoots i ν)
    (hnot : χ ∉ AddSubmonoid.closure (simpleRelativeRoots i ν \ {α})) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ weakSimpleRootChamber F T₀ T rT G i ν b,
      relativeCharacterDecay rT χ a ≤ C * relativeCharacterDecay rT α a := by
  obtain ⟨β, hβ, rfl⟩ := exists_add_of_not_mem_closure_diff
    (positiveRelativeRoots_subset_closure_simpleRelativeRoots i ν hχ) hnot
  obtain ⟨L, hL, hLow⟩ := exists_le_normCharacter_of_mem_closure i ν rT b hβ
  let e : ℝ := -1 / (Module.finrank ℚ F : ℝ)
  have he : e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hLp : 0 < (L : ℝ) := by exact_mod_cast hL
  refine ⟨(L : ℝ) ^ e, Real.rpow_nonneg hLp.le e, fun a ha => ?_⟩
  rw [relativeCharacterDecay, normCharacter_comp_add_val rT, NNReal.coe_mul, Real.mul_rpow
    (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (relativeCharacterDecay_pos rT α a).le
  exact Real.rpow_le_rpow_of_nonpos hLp (by exact_mod_cast hLow a ha) he

/-- For the maximal standard radical omitting `α`, on any weak simple-root chamber the
archimedean coordinates of conjugates of a compact set shrink by the inverse scalar of `α`. -/
def AdelicMaximalUnipotentContractionStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  ∀ α ∈ simpleRelativeRoots i ν,
  IsClosedImmersion j.hom.hom.left →
  SubgroupFunctor.range j = standardUnipotent i ν (simpleRelativeRoots i ν \ {α}) →
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F U hU
  ∃ (n : ℕ) (Q : U∞ ≃ₜ (Fin n → E∞)),
    Q 1 = 0 ∧ ContMDiff 𝓘(ℝ, Fin n → E∞) I∞ ∞ Q.symm ∧
    ∀ (Ω : Set (AdelicGroupPoints F U)), IsCompact Ω → ∀ b : ℝ≥0ˣ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ω, ∀ a ∈ weakSimpleRootChamber F T₀ T rT G i ν b,
        ∃ y : AdelicGroupPoints F U,
          (positiveMap F G T i T₀ rT a)⁻¹ * map F U G j x * positiveMap F G T i T₀ rT a =
            map F U G j y ∧
          ‖Q (infinite F U y)‖ ≤ C * relativeCharacterDecay rT α a

theorem adelicMaximalUnipotentContraction :
    AdelicMaximalUnipotentContractionStatement i ν rT j hU := by
  intro hG hi hν α hα hjClosed hj
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F U hU
  let J := simpleRelativeRoots i ν \ {α}
  have hJ : J ⊆ simpleRelativeRoots i ν := Set.sdiff_subset
  obtain ⟨n, t, w, hw, hweights⟩ := standardUnipotentEigenCoordinates i j
    hG hi ν hν J hJ hjClosed hj
  let Q := archimedeanPolynomialCoordinates hw.1
  refine ⟨n, Q, ?_, contMDiff_archimedeanPolynomialCoordinates_symm hU hw.1, ?_⟩
  · funext a
    simp only [Q, archimedeanPolynomialCoordinates_apply, hw.2.1, map_zero, Pi.zero_apply]
  intro Ω hΩ b
  have hbounds (k : Fin n) := exists_relativeCharacterDecay_le i ν rT b
    (hweights k).1 (hweights k).2
  choose D hD hbound using hbounds
  obtain ⟨B, hB⟩ := (hΩ.image (Q.continuous.comp (infinite F U).continuous).norm).bddAbove
  let L := max 0 B
  let M := ∑ k, D k
  have hL : 0 ≤ L := le_max_left _ _
  have hM : 0 ≤ M := Finset.sum_nonneg (fun k _ => hD k)
  refine ⟨M * L, mul_nonneg hM hL, fun x hx a ha => ?_⟩
  let s : GroupScheme.affinePoints T.toGrp Aₐ := a.val ≫ (CommGroupScheme.groupHom rT).hom.hom
  have hs : positiveMap F G T i T₀ rT a = GroupScheme.affinePointsTarget T.toGrp i Aₐ s := by
    change a.1 ≫ (CommGroupScheme.groupHom rT ≫ i).hom.hom =
      (a.1 ≫ (CommGroupScheme.groupHom rT).hom.hom) ≫ i.hom.hom
    rw [Category.assoc]
    rfl
  obtain ⟨⟨zeta, hzeta⟩, hcomp⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  have hstable : (AutomorphicAction.conjugation i).IsStable (SubgroupFunctor.range j) := by
    rw [hj, (hcomp zeta hzeta).2.2]
    exact Dynamic.unipotent_isStable_conjugation i _
  have hconjMem := hstable _ s⁻¹ (map F U G j x) ⟨x, rfl⟩
  rw [AutomorphicAction.conjugation_act] at hconjMem
  change ∃ y : AdelicGroupPoints F U, map F U G j y =
    GroupScheme.affinePointsTarget T.toGrp i Aₐ s⁻¹ * map F U G j x *
      (GroupScheme.affinePointsTarget T.toGrp i Aₐ s⁻¹)⁻¹ at hconjMem
  obtain ⟨y, hy⟩ := hconjMem
  rw [map_inv, inv_inv, ← hs] at hy
  refine ⟨y, hy.symm, (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg hM hL) (relativeCharacterDecay_pos rT α a).le)).mpr ?_⟩
  intro k
  have hxy : map F U G j x = positiveMap F G T i T₀ rT a *
      map F U G j y * (positiveMap F G T i T₀ rT a)⁻¹ := by rw [hy]; group
  rw [hs] at hxy
  obtain ⟨r, hr⟩ := (mem_intrinsicSubgroup_iff F T₀ a.val).mp a.property (rT ≫ w k)
  have hr' : PositiveRealIdeles.full F r = Lie.characterValue (w k) s :=
    hr.trans (Lie.characterValue_comp rT (w k) a.val)
  have heval := hw.2.2 Aₐ s y x hxy k
  rw [← hr'] at heval
  have hyEval : U.affinePointEvaluation Aₐ y (t k) =
      ((PositiveRealIdeles.full F r⁻¹ : Ideles F) : Adeles F) *
        U.affinePointEvaluation Aₐ x (t k) := by
    rw [heval, map_inv, ← mul_assoc, Units.inv_mul, one_mul]
  have hproj (z : AdelicGroupPoints F U) :
      Q (infinite F U z) k = c∞ (U.affinePointEvaluation Aₐ z (t k)).1 := by
    let f : Aₐ ⟶ A∞ :=
      CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    simp only [Q, archimedeanPolynomialCoordinates_apply]
    change c∞ (U.affinePointEvaluation A∞ (U.affinePointMap f z) (t k)) = _
    rw [U.affinePointEvaluation_map]
    rfl
  have hQy : Q (infinite F U y) k =
      c∞ (PositiveRealIdeles.full F r⁻¹).val.1 * Q (infinite F U x) k := by
    rw [hproj y, hyEval]
    change c∞ ((PositiveRealIdeles.full F r⁻¹).val.1 *
      (U.affinePointEvaluation Aₐ x (t k)).1) = _
    rw [map_mul, hproj x]
  have hsNorm : ‖c∞ (PositiveRealIdeles.full F r⁻¹).val.1‖ ≤ relativeCharacterDecay rT (w k) a := by
    rw [relativeCharacterDecay_eq_inv rT hr, ← NNReal.coe_inv, ← Units.val_inv_eq_inv_val]
    exact AdelicMatrixHeight.mixedSpace_norm_le F _ (NNReal.coe_nonneg _)
      (fun v => (PositiveRealIdeles.norm_full_infinite_value F v r⁻¹).le)
  have hxNorm : ‖Q (infinite F U x) k‖ ≤ L :=
    (norm_le_pi_norm _ k).trans ((hB ⟨x, hx, rfl⟩).trans (le_max_right _ _))
  have hDM : D k ≤ M := Finset.single_le_sum (f := D) (fun k _ => hD k) (Finset.mem_univ k)
  calc
    ‖Q (infinite F U y) k‖ ≤ ‖c∞ (PositiveRealIdeles.full F r⁻¹).val.1‖ *
        ‖Q (infinite F U x) k‖ := by rw [hQy]; exact norm_mul_le _ _
    _ ≤ (D k * relativeCharacterDecay rT α a) * L :=
      mul_le_mul (hsNorm.trans (hbound k a ha)) hxNorm (norm_nonneg _)
        (mul_nonneg (hD k) (relativeCharacterDecay_pos rT α a).le)
    _ ≤ (M * relativeCharacterDecay rT α a) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDM
        (relativeCharacterDecay_pos rT α a).le) hL
    _ = M * L * relativeCharacterDecay rT α a := by ring

end Langlands.Global
