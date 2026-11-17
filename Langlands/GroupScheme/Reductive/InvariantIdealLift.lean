import Langlands.GroupScheme.Reductive.StableCovariantFamily
import Langlands.GroupScheme.Reductive.InvariantLinearForm

/-! # Invariant lifts inside translation-stable ideals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.InvariantPowerLift

variable {k : Type u} [Field k]

/-- The subspace of elements whose image is a ground-field scalar. -/
def scalarPreimage {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) : Submodule k A :=
  (LinearMap.range (Algebra.linearMap k B)).comap φ.toLinearMap

theorem mem_scalarPreimage {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) (a : A) :
    a ∈ scalarPreimage φ ↔ ∃ c : k, φ a = algebraMap k B c := by
  exact exists_congr fun _ => eq_comm

variable {J H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Scalar images of a covariant family yield a dual-fixed coefficient vector
when rational translations preserve those images. -/
theorem IsRightCovariantFamily.dual_fixed_of_scalar_images
    [IsAlgClosed k] [Smooth H.X.hom]
    {i : H ⟶ J} {ρ : MatrixRepresentation H n}
    {f : n → ((algΓ (CommRingCat.of k)).obj J.X).unop}
    (hf : IsRightCovariantFamily i ρ f)
    {B : Type*} [CommRing B] [Nontrivial B] [Algebra k B]
    (φ : ((algΓ (CommRingCat.of k)).obj J.X).unop →ₐ[k] B)
    (c : n → k) (hc : ∀ j, φ (f j) = algebraMap k B (c j))
    (hφ : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (j : n),
      φ (rightTranslation i h (f j)) = φ (f j)) :
    ρ.dual.IsFixedVector c := by
  apply (MatrixRepresentation.isFixedVector_iff_rationalRepresentation ρ.dual c).2
  intro h
  rw [MatrixRepresentation.rationalRepresentation_apply,
    MatrixRepresentation.dual_rationalMatrix,
    GeneralLinear.matrixContragredient_coe]
  have he := hf J.X (𝟙 _) (CartesianMonoidalCategory.toUnit J.X ≫ h⁻¹)
  rw [MatrixRepresentation.pointMatrix_constant] at he
  change (fun j => rightTranslation i h⁻¹ (f j)) =
    ((ρ.rationalMatrix h⁻¹ : Matrix n n k).map (scalarMap J.X))ᵀ *ᵥ f at he
  funext j
  apply (FaithfulSMul.algebraMap_injective k B)
  have hj := congrArg φ (congrFun he j)
  rw [hφ, hc] at hj
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply] at hj
  change algebraMap k B (c j) =
    φ (∑ r, algebraMap k _ (ρ.rationalMatrix h⁻¹ r j) * f r) at hj
  rw [map_sum] at hj
  simp only [map_mul] at hj
  simp only [AlgHom.commutes, hc, ← map_mul, ← map_sum] at hj
  simpa only [map_inv, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    using hj.symm

section IdealLift

variable [IsAlgClosed k] [Smooth H.X.hom] [IsAffine J.X.left]

/-- A geometrically reductive subgroup lifts the scalar one to an invariant
element of a rationally stable ideal, provided scalar images are preserved. -/
theorem exists_invariant_mem_ideal_image_one
    (i : H ⟶ J) (hH : IsGeometricallyReductive H)
    (I : Ideal ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hI : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (s : ((algΓ (CommRingCat.of k)).obj J.X).unop),
      s ∈ I → rightTranslation i h s ∈ I)
    {B : Type*} [CommRing B] [Nontrivial B] [Algebra k B]
    (φ : ((algΓ (CommRingCat.of k)).obj J.X).unop →ₐ[k] B)
    (hφ : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (s : ((algΓ (CommRingCat.of k)).obj J.X).unop),
      s ∈ scalarPreimage φ → φ (rightTranslation i h s) = φ s)
    (s : ((algΓ (CommRingCat.of k)).obj J.X).unop) (hs : s ∈ I)
    (hsφ : φ s = 1) :
    ∃ t : ((algΓ (CommRingCat.of k)).obj J.X).unop,
      t ∈ I ∧ HomogeneousQuotientFromEmbedding.IsRightInvariant i t ∧ φ t = 1 := by
  let := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    k H.X.left H.X.hom
  let W := I.restrictScalars k ⊓ scalarPreimage φ
  have hW : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (a : ((algΓ (CommRingCat.of k)).obj J.X).unop),
      a ∈ W → rightTranslation i h a ∈ W := by
    intro h a ha
    refine ⟨hI h a ha.1, ?_⟩
    obtain ⟨c, hc⟩ := (mem_scalarPreimage φ a).1 ha.2
    exact (mem_scalarPreimage φ _).2 ⟨c, (hφ h a ha.2).trans hc⟩
  have hsW : s ∈ W :=
    ⟨hs, (mem_scalarPreimage φ s).2 ⟨1, hsφ.trans (map_one _).symm⟩⟩
  obtain ⟨d, ρ, f, v, hf, hfW, hv⟩ :=
    exists_covariantFamily_in_submodule i W hW s hsW
  choose c hc using fun j => (mem_scalarPreimage φ (f j)).1 (hfW j).2
  have hc0 : c ≠ 0 := by
    intro hz
    have hzφ : ∀ j, φ (f j) = 0 := by
      intro j
      simpa only [hz, Pi.zero_apply, map_zero] using hc j
    have hvφ := congrArg φ hv
    rw [familyLinearMap_apply, map_sum, hsφ] at hvφ
    simp only [map_smul, hzφ, smul_zero, Finset.sum_const_zero] at hvφ
    exact zero_ne_one hvφ
  have hfix : ρ.dual.IsFixedVector c :=
    hf.dual_fixed_of_scalar_images φ c hc (fun h j => hφ h (f j) (hfW j).2)
  obtain ⟨e, F, he, hF, hFinv, hFc⟩ :=
    MatrixRepresentation.exists_normalized_transpose_invariant hH ρ c hc0 hfix
  refine ⟨MvPolynomial.aeval f F, aeval_mem_ideal I f (fun j => (hfW j).1) he hF,
    ?_, ?_⟩
  · exact isRightInvariant_eval₂ i ρ f hf F hFinv
  · simpa only [mul_one, one_pow] using
      map_aeval_eq_pow φ f hF c hFc 1 (by simpa only [mul_one] using hc)

/-- Two comaximal rationally translation-stable ideals, one proper, are
separated by an actual all-test invariant global section. -/
theorem exists_invariant_separating_ideals
    (i : H ⟶ J) (hH : IsGeometricallyReductive H)
    (I K : Ideal ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hI : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (s : ((algΓ (CommRingCat.of k)).obj J.X).unop),
      s ∈ I → rightTranslation i h s ∈ I)
    (hK : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (s : ((algΓ (CommRingCat.of k)).obj J.X).unop),
      s ∈ K → rightTranslation i h s ∈ K)
    (hKproper : K ≠ ⊤) (hIK : I ⊔ K = ⊤) :
    ∃ t : ((algΓ (CommRingCat.of k)).obj J.X).unop,
      t ∈ I ∧ HomogeneousQuotientFromEmbedding.IsRightInvariant i t ∧ t - 1 ∈ K := by
  let A := ((algΓ (CommRingCat.of k)).obj J.X).unop
  let := Ideal.Quotient.nontrivial_iff.mpr hKproper
  let φ : A →ₐ[k] A ⧸ K := Ideal.Quotient.mkₐ k K
  have hφ : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (a : A),
      a ∈ scalarPreimage φ → φ (rightTranslation i h a) = φ a := by
    intro h a ha
    obtain ⟨c, hc⟩ := (mem_scalarPreimage φ a).1 ha
    have hdiff : a - algebraMap k A c ∈ K := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change φ (a - algebraMap k A c) = 0
      rw [map_sub, AlgHom.commutes, hc, sub_self]
    have ht : φ (rightTranslation i h (a - algebraMap k A c)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hK h _ hdiff)
    rw [map_sub, AlgHom.commutes, map_sub, AlgHom.commutes] at ht
    exact (sub_eq_zero.mp ht).trans hc.symm
  obtain ⟨s, hs, a, ha, hsa⟩ := Submodule.mem_sup.mp
    (show (1 : A) ∈ I ⊔ K by rw [hIK]; trivial)
  have hsφ : φ s = 1 := by
    have he := congrArg φ hsa
    rw [map_add, map_one, show φ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      add_zero] at he
    exact he
  obtain ⟨t, htI, htinv, htφ⟩ :=
    exists_invariant_mem_ideal_image_one i hH I hI φ hφ s hs hsφ
  refine ⟨t, htI, htinv, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change φ (t - 1) = 0
  rw [map_sub, map_one, htφ, sub_self]

end IdealLift

end Langlands.GroupScheme.InvariantPowerLift
