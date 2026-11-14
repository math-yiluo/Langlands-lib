import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.Geometry.Building.RealTorusInvariantForm
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Rational.RootFiniteness
import Mathlib.LinearAlgebra.RootSystem.Basic
import Langlands.GroupScheme.Rational.IndivisibleRealRootReduced

/-! # Real relative coroots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped BigOperators

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

namespace RelativeRootReflectionData

variable (D : RelativeRootReflectionData i)

/-- The invariant-form formula determines the real coroot in the full space. -/
theorem realCoroot_unique (hT : IsSplitTorus T.toGrp)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (v : V T) :
    (∀ x : Vstar T, pair T x v *
      B ((1 : ℝ) ⊗ₜ[ℤ] α.1) ((1 : ℝ) ⊗ₜ[ℤ] α.1) =
        2 * B x ((1 : ℝ) ⊗ₜ[ℤ] α.1)) ↔ v = D.realCoroot α := by
  constructor
  · intro hv
    apply (isPerfPair_of_isSplitTorus hT).bijective_right.injective
    apply LinearMap.ext
    intro x
    change pair T x v = pair T x (D.realCoroot α)
    apply mul_right_cancel₀ (hB.2.1 _ (D.one_tmul_ne_zero i α)).ne'
    exact (hv x).trans (D.coroot_mul_form i B hB α x).symm
  · rintro rfl x
    exact D.coroot_mul_form i B hB α x

/-- Integral coroots are independent of the integral reflection data. -/
theorem coroot_eq_of_invariantForm (hT : IsSplitTorus T.toGrp)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (D' : RelativeRootReflectionData i) : D'.coroot = D.coroot := by
  funext α
  have hreal : D'.realCoroot α = D.realCoroot α :=
    (D.realCoroot_unique hT B hB α _).mp (D'.coroot_mul_form i B hB α)
  apply hT.isPerfPair_latticePairing.bijective_right.injective
  apply LinearMap.ext
  intro χ
  have hp := congrArg (pair T ((1 : ℝ) ⊗ₜ[ℤ] χ)) hreal
  simp only [pair_tmul_realCoroot, one_mul] at hp
  exact_mod_cast hp

end RelativeRootReflectionData

/-- Averaging a coordinate form gives an invariant positive form on any finite
real representation of a finite group. -/
private theorem exists_invariant_realForm {W E : Type*} [Group W] [Finite W]
    [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    (ρ : W →* (E ≃ₗ[ℝ] E)) :
    ∃ C : LinearMap.BilinForm ℝ E,
      (∀ v w, C v w = C w v) ∧ (∀ v, v ≠ 0 → 0 < C v v) ∧
        ∀ (w : W) v v', C (ρ w v) (ρ w v') = C v v' := by
  classical
  let := Fintype.ofFinite W
  let b := Module.finBasis ℝ E
  let C₀ : LinearMap.BilinForm ℝ E :=
    (dotProductBilin ℝ ℝ).compl₁₂ b.equivFun.toLinearMap b.equivFun.toLinearMap
  have hC₀ (v w : E) : C₀ v w = ∑ j, b.equivFun v j * b.equivFun w j := rfl
  have hnonneg (v : E) : 0 ≤ C₀ v v := by
    rw [hC₀]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hpos (v : E) (hv : v ≠ 0) : 0 < C₀ v v := by
    have hc : b.equivFun v ≠ 0 := fun h => hv (b.equivFun.injective (by simpa using h))
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    rw [hC₀]
    exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _)
      ⟨j, Finset.mem_univ _, mul_self_pos.mpr hj⟩
  let C : LinearMap.BilinForm ℝ E :=
    ∑ w : W, C₀.compl₁₂ (ρ w).toLinearMap (ρ w).toLinearMap
  have hC (v w : E) : C v w = ∑ z : W, C₀ (ρ z v) (ρ z w) := by
    simp [C, LinearMap.sum_apply]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro v w
    simp only [hC, hC₀, mul_comm]
  · intro v hv
    rw [hC]
    refine Finset.sum_pos' (fun _ _ => hnonneg _) ⟨1, Finset.mem_univ _, ?_⟩
    simpa using hpos v hv
  · intro z v w
    simp only [hC]
    simp_rw [← LinearEquiv.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulRight z) _ _ (fun _ => rfl)

omit [IsAffineHom G.X.hom] in
/-- Invariant scalar products exist on both full real torus spaces. -/
theorem exists_relativeWeyl_realInnerProducts (hT : IsSplitTorus T.toGrp)
    [Finite (relativeWeylGroup i)] :
    (∃ B : LinearMap.BilinForm ℝ (Vstar T), IsWeylInvariantInnerProduct i B) ∧
    ∃ C : LinearMap.BilinForm ℝ (V T), IsWeylInvariantCocharacterInnerProduct i C := by
  classical
  let := Fintype.ofFinite (relativeWeylGroup i)
  let := hT.finite_realCocharacterSpace
  refine ⟨⟨relativeWeylInvariantForm i hT, ?_, ?_, ?_⟩,
    exists_invariant_realForm (relativeWeylRealAction i)⟩
  · exact relativeWeylInvariantForm_symm i hT
  · exact fun _ hv => relativeWeylInvariantForm_pos i hT hv
  · exact relativeWeylInvariantForm_invariant i hT

namespace RelativeRootReflectionData

variable (D : RelativeRootReflectionData i)

/-- The actual pairing restricted to the root and coroot spans. -/
def realSpanPairing : relativeRootSpanReal i →ₗ[ℝ] D.realCorootSpan →ₗ[ℝ] ℝ :=
  (pair T).compl₁₂ (relativeRootSpanReal i).subtype D.realCorootSpan.subtype

/-- Coroots annihilate every restricted group character, including their span. -/
theorem realCorootSpan_le_annihilator
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    D.realCorootSpan ≤ cocharacterAnnihilator (rationalCharacterRestrictReal i).range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨α, rfl⟩
  change D.realCoroot α ∈ cocharacterAnnihilator _
  rw [mem_cocharacterAnnihilator]
  rintro _ ⟨x, rfl⟩
  exact D.restrictedCharacter_coroot i B hB x α

/-- Positivity separates the real root span by the supplied coroots. -/
theorem root_eq_zero_of_pair_coroot_eq_zero
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (x : relativeRootSpanReal i) (hx : ∀ α, pair T x (D.realCoroot α) = 0) : x = 0 := by
  apply Subtype.ext
  change (x : Vstar T) = 0
  by_contra hne
  have hspan : relativeRootSpanReal i ≤ (B x).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    exact (D.coroot_eq_zero_iff i B hB ⟨α, hα⟩ x).mp (hx ⟨α, hα⟩)
  have hz : B x x = 0 := hspan x.property
  exact (hB.2.1 x hne).ne' hz

omit [Mono i.hom.hom.left] in
/-- The character/root complement separates vectors that annihilate both summands. -/
theorem cocharacter_eq_zero_of_pair_summands (hT : IsSplitTorus T.toGrp)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (v : V T) (hr : ∀ x : relativeRootSpanReal i, pair T x v = 0)
    (hz : v ∈ cocharacterAnnihilator (rationalCharacterRestrictReal i).range) : v = 0 := by
  apply (isPerfPair_of_isSplitTorus hT).bijective_right.injective
  apply LinearMap.ext
  intro x
  obtain ⟨r, z, h, _⟩ := Submodule.existsUnique_add_of_isCompl hc x
  simp only [map_zero, LinearMap.zero_apply]
  change pair T x v = 0
  rw [← h, map_add, LinearMap.add_apply, hr]
  simpa using (mem_cocharacterAnnihilator _ _).mp hz z z.property

/-- The real pairing is perfect on the root and coroot spans. -/
theorem realSpanPairing_isPerfPair (hT : IsSplitTorus T.toGrp)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    D.realSpanPairing.IsPerfPair := by
  let := hT.finite_realCharacterSpace
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply D.root_eq_zero_of_pair_coroot_eq_zero B hB x
    intro α
    exact congrArg (fun f => f ⟨D.realCoroot α, Submodule.subset_span ⟨α, rfl⟩⟩) hx
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply Subtype.ext
    exact cocharacter_eq_zero_of_pair_summands hT hc v
      (fun x => congrArg (fun f => f x) hv)
      (D.realCorootSpan_le_annihilator B hB v.property)

/-- The real coroot span is exactly the annihilator of restricted group characters. -/
theorem realCorootSpan_eq_annihilator (hT : IsSplitTorus T.toGrp)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    D.realCorootSpan = cocharacterAnnihilator (rationalCharacterRestrictReal i).range := by
  apply le_antisymm (D.realCorootSpan_le_annihilator B hB)
  intro v hv
  obtain ⟨n, hn⟩ := (D.realSpanPairing_isPerfPair hT hc B hB).bijective_right.surjective
    (((pair T).flip v).comp (relativeRootSpanReal i).subtype)
  have he : v - (n : V T) = 0 :=
    cocharacter_eq_zero_of_pair_summands hT hc _
      (fun x => by
        have hh := congrArg (fun f => f x) hn
        change pair T x n = pair T x v at hh
        simp only [map_sub, hh, sub_self])
      ((cocharacterAnnihilator _).sub_mem hv
        (D.realCorootSpan_le_annihilator B hB n.property))
  exact (sub_eq_zero.mp he).symm ▸ n.property

/-- Central directions and the real coroot span are complementary. -/
theorem central_isCompl_realCorootSpan (hT : IsSplitTorus T.toGrp)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    IsCompl (relativeCentralDirections i) D.realCorootSpan := by
  have hcent : relativeCentralDirections i = cocharacterAnnihilator (relativeRootSpanReal i) :=
    rootAnnihilator_eq_cocharacterAnnihilator _
  rw [hcent]
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv hn
    have hz : (⟨v, hn⟩ : D.realCorootSpan) = 0 := by
      apply (D.realSpanPairing_isPerfPair hT hc B hB).bijective_right.injective
      apply LinearMap.ext
      intro x
      simpa [realSpanPairing] using
        (mem_cocharacterAnnihilator _ _).mp hv x x.property
    exact congrArg Subtype.val hz
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    obtain ⟨n, hn⟩ := (D.realSpanPairing_isPerfPair hT hc B hB).bijective_right.surjective
      (((pair T).flip v).comp (relativeRootSpanReal i).subtype)
    apply Submodule.mem_sup.mpr
    refine ⟨v - n, ?_, n, n.property, sub_add_cancel _ _⟩
    rw [mem_cocharacterAnnihilator]
    intro x hx
    have hh := congrArg (fun f => f ⟨x, hx⟩) hn
    change pair T x n = pair T x v at hh
    simp only [map_sub, hh, sub_self]

end RelativeRootReflectionData

namespace RelativeRootSystem

/-- An actual root in its real span. -/
def realRootVector (α : relativeRoots i) : relativeRootSpanReal i :=
  ⟨(1 : ℝ) ⊗ₜ[ℤ] α.1, Submodule.subset_span ⟨α.1, α.2, rfl⟩⟩

/-- Real scalar extension is injective on the character lattice of a split torus. -/
theorem character_realTensor_injective (hT : IsSplitTorus T.toGrp) :
    Function.Injective (fun χ : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] χ) := by
  intro χ ψ h
  apply hT.isPerfPair_latticePairing.bijective_left.injective
  apply LinearMap.ext
  intro ν
  have hp := congrArg (fun x => pair T x ((1 : ℝ) ⊗ₜ[ℤ] ν)) h
  simp only [pair_tmul_tmul, one_mul] at hp
  exact_mod_cast hp

/-- Different actual roots give different real root vectors. -/
def realRootEmbedding (hT : IsSplitTorus T.toGrp) :
    relativeRoots i ↪ relativeRootSpanReal i where
  toFun := realRootVector
  inj' := fun _ _ h => Subtype.ext (character_realTensor_injective hT (congrArg Subtype.val h))

omit [Mono i.hom.hom.left] in
/-- The actual real roots span the real root span. -/
theorem span_range_realRootVector :
    Submodule.span ℝ (Set.range (realRootVector (i := i))) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  change Submodule.span ℝ (Set.range fun α : relativeRoots i => (1 : ℝ) ⊗ₜ[ℤ] α.1) =
    Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' relativeRoots i)
  congr 1
  ext x
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨α.1, α.2, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨⟨α, hα⟩, rfl⟩

end RelativeRootSystem

namespace RelativeRootReflectionData

open RelativeRootSystem

variable (D : RelativeRootReflectionData i)

/-- Distinct relative roots have distinct real coroots. -/
theorem realCoroot_injective (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) : Function.Injective D.realCoroot := by
  intro α β h
  apply D.corootFunctional_injective hT hfinite
  apply congrArg (corootFunctional i)
  apply hT.isPerfPair_latticePairing.bijective_right.injective
  apply LinearMap.ext
  intro χ
  have hp := congrArg (pair T ((1 : ℝ) ⊗ₜ[ℤ] χ)) h
  simp only [pair_tmul_realCoroot, one_mul] at hp
  exact_mod_cast hp

/-- The real coroots in their actual span. -/
def realCorootEmbedding (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) : relativeRoots i ↪ D.realCorootSpan where
  toFun α := ⟨D.realCoroot α, Submodule.subset_span ⟨α, rfl⟩⟩
  inj' := fun _ _ h => D.realCoroot_injective hT hfinite (congrArg Subtype.val h)

/-- The actual root reflections preserve the real root family. -/
theorem mapsTo_realPreReflection (α : relativeRoots i) :
    Set.MapsTo (Module.preReflection (realRootVector α)
      (D.realSpanPairing.flip ⟨D.realCoroot α, Submodule.subset_span ⟨α, rfl⟩⟩))
      (Set.range (realRootVector (i := i))) (Set.range (realRootVector (i := i))) := by
  rintro _ ⟨β, rfl⟩
  refine ⟨⟨weylAction i (D.representative α) β.1,
    weylAction_mapsTo_relativeRoots i (D.representative α) β.2⟩, ?_⟩
  apply Subtype.ext
  change (1 : ℝ) ⊗ₜ[ℤ] weylAction i (D.representative α) β.1 =
    (1 : ℝ) ⊗ₜ[ℤ] β.1 - pair T ((1 : ℝ) ⊗ₜ[ℤ] β.1) (D.realCoroot α) •
      ((1 : ℝ) ⊗ₜ[ℤ] α.1)
  exact (D.real_reflection i α ((1 : ℝ) ⊗ₜ[ℤ] β.1))

/-- On the full cocharacter space the actual representative is the coreflection. -/
theorem real_coreflection (hT : IsSplitTorus T.toGrp) (α : relativeRoots i) (v : V T) :
    relativeWeylRealAction i (QuotientGroup.mk (D.representative α)) v =
      v - pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) v • D.realCoroot α := by
  let w : relativeWeylGroup i := QuotientGroup.mk (D.representative α)
  have hr : pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) (relativeWeylRealAction i w v) =
      -pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) v := by
    have h := pair_relativeWeyl i w ((1 : ℝ) ⊗ₜ[ℤ] α.1) v
    rw [D.real_reflection_self i] at h
    simp only [map_neg, LinearMap.neg_apply] at h
    linarith
  apply (isPerfPair_of_isSplitTorus hT).bijective_right.injective
  apply LinearMap.ext
  intro x
  have h := pair_relativeWeyl i w x v
  rw [D.real_reflection i] at h
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
  change pair T x (relativeWeylRealAction i w v) =
    pair T x (v - pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) v • D.realCoroot α)
  simp only [map_sub, map_smul, smul_eq_mul]
  rw [hr] at h
  dsimp only [realCoroot]
  nlinarith

/-- The real full-root pairing, with roots and coroots in their actual spans. -/
def realRootPairing (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    RootPairing (relativeRoots i) ℝ (relativeRootSpanReal i) D.realCorootSpan :=
  letI := hfinite.fintype
  letI := D.realSpanPairing_isPerfPair hT hc B hB
  RootPairing.mk'' D.realSpanPairing (realRootEmbedding hT) (D.realCorootEmbedding hT hfinite)
    D.pair_root_realCoroot D.mapsTo_realPreReflection span_range_realRootVector

theorem realRootPairing_isRootSystem (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    (D.realRootPairing hT hfinite hc B hB).IsRootSystem := by
  let := hfinite.fintype
  let := D.realSpanPairing_isPerfPair hT hc B hB
  unfold realRootPairing
  apply RootPairing.isRootSystem_mk''
  intro α β
  refine ⟨latticePairing T α.1 (D.coroot β), ?_⟩
  change _ = pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) (D.realCoroot β)
  simp

theorem realRootPairing_isCrystallographic (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    (D.realRootPairing hT hfinite hc B hB).IsCrystallographic := by
  constructor
  intro α β
  refine ⟨latticePairing T α.1 (D.coroot β), ?_⟩
  change _ = pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) (D.realCoroot β)
  simp

theorem realRootPairing_reflection (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (x : relativeRootSpanReal i) :
    ((D.realRootPairing hT hfinite hc B hB).reflection α x : Vstar T) =
      relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α)) x :=
  (D.real_reflection i α x).symm

theorem realRootPairing_coreflection (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (v : D.realCorootSpan) :
    ((D.realRootPairing hT hfinite hc B hB).coreflection α v : V T) =
      relativeWeylRealAction i (QuotientGroup.mk (D.representative α)) v :=
  (D.real_coreflection hT α v).symm

end RelativeRootReflectionData

namespace RelativeRootSystem

/-- Every relative root is indivisible or twice an indivisible root. -/
theorem exists_indivisible_eq_or_twice (hR : HasRelativeRootSystem i)
    (α : relativeRoots i) :
    ∃ β : RelativeRoot.indivisibleRoots i, α.1 = β.1 ∨ α.1 = 2 • β.1 := by
  classical
  by_cases hα : α.1 ∈ RelativeRoot.indivisibleRoots i
  · exact ⟨⟨α.1, hα⟩, Or.inl rfl⟩
  · obtain ⟨b, hb, m, hm, hmb⟩ :
        ∃ b ∈ relativeRoots i, ∃ m : ℕ, 1 < m ∧ m • b = α.1 := by
      simpa only [RelativeRoot.indivisibleRoots, Set.mem_ofPred_eq, α.2, true_and,
        not_forall, not_not, exists_prop] using hα
    have hm2 : m = 2 := by
      rcases hR.eq_one_or_two_of_nsmul_mem hb (hmb ▸ α.2) with h | h
      · omega
      · exact h
    subst m
    have hb' : b ∈ RelativeRoot.indivisibleRoots i := by
      refine ⟨hb, ?_⟩
      intro c hc n hn hnc
      have hmul : (2 * n) • c ∈ relativeRoots i := by
        rw [mul_smul, hnc, hmb]
        exact α.2
      rcases hR.eq_one_or_two_of_nsmul_mem hc hmul with h | h <;> omega
    exact ⟨⟨b, hb'⟩, Or.inr hmb.symm⟩

/-- The indivisible roots, embedded in the real root span. -/
def indivisibleRealRootEmbedding (hT : IsSplitTorus T.toGrp) :
    RelativeRoot.indivisibleRoots i ↪ relativeRootSpanReal i :=
  (⟨fun α => (⟨α.1, α.2.1⟩ : relativeRoots i),
    fun _ _ h => Subtype.ext (congrArg (fun x : relativeRoots i => x.val) h)⟩ :
      RelativeRoot.indivisibleRoots i ↪ relativeRoots i).trans (realRootEmbedding hT)

/-- The indivisible roots still span the full real root span. -/
theorem span_range_indivisibleRealRootEmbedding (hT : IsSplitTorus T.toGrp)
    (hR : HasRelativeRootSystem i) :
    Submodule.span ℝ (Set.range (indivisibleRealRootEmbedding (i := i) hT)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  change Submodule.span ℝ (Set.range fun α : RelativeRoot.indivisibleRoots i =>
    (1 : ℝ) ⊗ₜ[ℤ] α.1) = relativeRootSpanReal i
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    exact Submodule.subset_span ⟨α.1, α.2.1, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨β, h | h⟩ := exists_indivisible_eq_or_twice hR ⟨α, hα⟩
    · change α = β.1 at h
      rw [h]
      exact Submodule.subset_span ⟨β, rfl⟩
    · change α = 2 • β.1 at h
      rw [h]
      change (1 : ℝ) ⊗ₜ[ℤ] (2 • β.1) ∈ _
      rw [two_smul, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨β, rfl⟩)
        (Submodule.subset_span ⟨β, rfl⟩)

omit [Mono i.hom.hom.left] in
/-- A real indivisible root cannot be twice another indivisible root. -/
theorem indivisibleRealRoot_ne_two_smul (hT : IsSplitTorus T.toGrp)
    (α β : RelativeRoot.indivisibleRoots i) :
    indivisibleRealRootEmbedding hT β ≠
      (2 : ℝ) • indivisibleRealRootEmbedding hT α := by
  intro h
  have hlat : β.1 = 2 • α.1 := character_realTensor_injective hT (by
    calc
      (1 : ℝ) ⊗ₜ[ℤ] β.1 = (2 : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] α.1) :=
        congrArg (fun x : relativeRootSpanReal i => x.val) h
      _ = (1 : ℝ) ⊗ₜ[ℤ] (2 • α.1) := by
        simp [two_smul, TensorProduct.tmul_add])
  exact β.2.2 α.1 α.2.1 2 (by norm_num) hlat.symm

/-- The actual Weyl action preserves indivisibility within the root set. -/
theorem weylAction_indivisible (n : normalizerPoints i)
    (α : RelativeRoot.indivisibleRoots i) :
    weylAction i n α.1 ∈ RelativeRoot.indivisibleRoots i := by
  refine ⟨weylAction_mapsTo_relativeRoots i n α.2.1, ?_⟩
  intro b hb m hm hmb
  apply α.2.2 (weylAction i n⁻¹ b)
    (weylAction_mapsTo_relativeRoots i n⁻¹ hb) m hm
  rw [← map_nsmul, hmb, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

end RelativeRootSystem

namespace RelativeRootReflectionData

open RelativeRootSystem

variable (D : RelativeRootReflectionData i)

/-- The coroots of the indivisible roots, in the full coroot span. -/
def indivisibleRealCorootEmbedding (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    RelativeRoot.indivisibleRoots i ↪ D.realCorootSpan :=
  (⟨fun α => (⟨α.1, α.2.1⟩ : relativeRoots i),
    fun _ _ h => Subtype.ext (congrArg (fun x : relativeRoots i => x.val) h)⟩ :
      RelativeRoot.indivisibleRoots i ↪ relativeRoots i).trans (D.realCorootEmbedding hT hfinite)

theorem mapsTo_indivisibleRealPreReflection (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (α : RelativeRoot.indivisibleRoots i) :
    Set.MapsTo (Module.preReflection (indivisibleRealRootEmbedding hT α)
      (D.realSpanPairing.flip (D.indivisibleRealCorootEmbedding hT hfinite α)))
      (Set.range (indivisibleRealRootEmbedding (i := i) hT))
      (Set.range (indivisibleRealRootEmbedding (i := i) hT)) := by
  rintro _ ⟨β, rfl⟩
  refine ⟨⟨weylAction i (D.representative ⟨α.1, α.2.1⟩) β.1,
    weylAction_indivisible _ β⟩, ?_⟩
  apply Subtype.ext
  exact D.real_reflection i ⟨α.1, α.2.1⟩ ((1 : ℝ) ⊗ₜ[ℤ] β.1)

/-- The real root pairing on the actual indivisible root indices. -/
def indivisibleRealRootPairing (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (hR : HasRelativeRootSystem i) :
    RootPairing (RelativeRoot.indivisibleRoots i) ℝ (relativeRootSpanReal i) D.realCorootSpan :=
  letI := (hfinite.subset (show RelativeRoot.indivisibleRoots i ⊆ relativeRoots i from fun _ h => h.1)).fintype
  letI := D.realSpanPairing_isPerfPair hT hc B hB
  RootPairing.mk'' D.realSpanPairing (indivisibleRealRootEmbedding hT)
    (D.indivisibleRealCorootEmbedding hT hfinite)
    (fun α => D.pair_root_realCoroot ⟨α.1, α.2.1⟩)
    (D.mapsTo_indivisibleRealPreReflection hT hfinite)
    (span_range_indivisibleRealRootEmbedding hT hR)

theorem indivisibleRealRootPairing_isRootSystem (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (hR : HasRelativeRootSystem i) :
    (D.indivisibleRealRootPairing hT hfinite hc B hB hR).IsRootSystem := by
  let := (hfinite.subset (show RelativeRoot.indivisibleRoots i ⊆ relativeRoots i from fun _ h => h.1)).fintype
  let := D.realSpanPairing_isPerfPair hT hc B hB
  unfold indivisibleRealRootPairing
  apply RootPairing.isRootSystem_mk''
  intro α β
  refine ⟨latticePairing T α.1 (D.coroot ⟨β.1, β.2.1⟩), ?_⟩
  change _ = pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) (D.realCoroot ⟨β.1, β.2.1⟩)
  simp

theorem indivisibleRealRootPairing_isCrystallographic (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hc : IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (hR : HasRelativeRootSystem i) :
    (D.indivisibleRealRootPairing hT hfinite hc B hB hR).IsCrystallographic := by
  constructor
  intro α β
  refine ⟨latticePairing T α.1 (D.coroot ⟨β.1, β.2.1⟩), ?_⟩
  change _ = pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) (D.realCoroot ⟨β.1, β.2.1⟩)
  simp

end RelativeRootReflectionData

/-- Renard V.3.7 on the actual full real torus spaces and their root and coroot spans. -/
theorem relativeRealCoroot : RelativeRealCorootStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro D
  have hT := hi.isSplitSubtorus.1
  have hR := relativeRootSystem k G hG T i hi
  let : Finite (relativeWeylGroup i) := hR.finite_relativeWeylGroup i
  have hfinite := hR.finite_relativeRoots i hT
  have hc := (relativeCharacterRootComplement k G hG T i hi).2
  obtain ⟨⟨B, hB⟩, hC⟩ := exists_relativeWeyl_realInnerProducts (i := i) hT
  refine ⟨⟨B, hB⟩, hC, D.coroot_eq_of_invariantForm hT B hB,
    D.realCoroot_unique hT, D.realCorootSpan_eq_annihilator hT hc B hB, ?_,
    hfinite.to_subtype, ?_, ?_⟩
  · rw [← D.realCorootSpan_eq_annihilator hT hc B hB]
    exact D.central_isCompl_realCorootSpan hT hc B hB
  · refine ⟨D.realRootPairing hT hfinite hc B hB,
      D.realRootPairing_isRootSystem hT hfinite hc B hB,
      D.realRootPairing_isCrystallographic hT hfinite hc B hB,
      fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
      D.realRootPairing_reflection hT hfinite hc B hB,
      D.realRootPairing_coreflection hT hfinite hc B hB⟩
  · refine ⟨D.indivisibleRealRootPairing hT hfinite hc B hB hR,
      D.indivisibleRealRootPairing_isRootSystem hT hfinite hc B hB hR,
      D.indivisibleRealRootPairing_isCrystallographic hT hfinite hc B hB hR,
      ?_, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
    let := (hfinite.subset (show RelativeRoot.indivisibleRoots i ⊆ relativeRoots i from
      fun _ h => h.1)).fintype
    let := D.indivisibleRealRootPairing_isCrystallographic hT hfinite hc B hB hR
    exact RootPairing.isReduced_of_no_double
      (D.indivisibleRealRootPairing hT hfinite hc B hB hR)
      (RelativeRootSystem.indivisibleRealRoot_ne_two_smul hT)

end Langlands.GroupScheme
