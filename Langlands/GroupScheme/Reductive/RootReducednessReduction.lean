import Langlands.GroupScheme.Reductive.RootReducednessStatement
import Langlands.GroupScheme.Reductive.RankOneRootReducednessStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Reduction of root reducedness to the case of proportional roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RootReducedness

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

section Lattice

/-- Nonzero integer multiples of a nonzero character of a split torus are nonzero. -/
theorem zsmul_ne_zero (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    {n : ℤ} (hn : n ≠ 0) : n • a ≠ 0 := by
  intro h
  apply hT.nsmul_ne_zero ha (Int.natAbs_ne_zero.mpr hn)
  rcases Int.natAbs_eq n with h' | h'
  · rw [← natCast_zsmul, ← h', h]
  · rw [← natCast_zsmul, ← neg_eq_zero, ← neg_zsmul, ← h', h]

/-- Two characters that are each linearly dependent with a fixed nonzero character are
linearly dependent with each other, provided the second one is nonzero. -/
theorem not_linearIndependent_of_not_linearIndependent (hT : IsSplitTorus T.toGrp)
    {a b c : characterLattice T} (ha : a ≠ 0) (hc : c ≠ 0)
    (hab : ¬ LinearIndependent ℤ ![a, b]) (hac : ¬ LinearIndependent ℤ ![a, c]) :
    ¬ LinearIndependent ℤ ![b, c] := by
  rw [LinearIndependent.pair_iff] at hab hac ⊢
  push Not at hab hac ⊢
  obtain ⟨s₁, t₁, h₁, hne₁⟩ := hab
  obtain ⟨s₂, t₂, h₂, hne₂⟩ := hac
  have ht₁ : t₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at h₁
    exact zsmul_ne_zero hT ha (fun hs => hne₁ hs rfl) h₁
  have hs₂ : s₂ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at h₂
    exact zsmul_ne_zero hT hc (hne₂ rfl) h₂
  refine ⟨s₂ * t₁, -(s₁ * t₂), ?_, fun h => absurd h (mul_ne_zero hs₂ ht₁)⟩
  have e₁ : t₁ • b = -(s₁ • a) := eq_neg_of_add_eq_zero_right h₁
  have e₂ : t₂ • c = -(s₂ • a) := eq_neg_of_add_eq_zero_right h₂
  rw [mul_smul, neg_smul, mul_smul, e₁, e₂, smul_neg, smul_neg, neg_neg, smul_smul, smul_smul,
    mul_comm s₂ s₁, neg_add_cancel]

/-- For a nonzero character `α` of a split torus and a finite set `s` of characters, some
cocharacter pairs to zero with `α`, and every character of `s` that pairs to zero with this
cocharacter is linearly dependent with `α` over `ℤ`. -/
theorem exists_cocharacter_pairing_eq_zero (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ≠ 0) {s : Set (characterLattice T)} (hs : s.Finite) :
    ∃ ζ : cocharacterLattice T, latticePairing T α ζ = 0 ∧
      ∀ γ ∈ s, latticePairing T γ ζ = 0 → ¬ LinearIndependent ℤ ![α, γ] := by
  classical
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos hα
  let f : characterLattice T → characterLattice T :=
    fun γ => (D : ℤ) • γ - latticePairing T γ ν • α
  obtain ⟨ξ, hξ⟩ := hT.exists_pairings_ne_zero (f '' s \ {0}) (hs.image f).sdiff
    (fun x hx => hx.2)
  refine ⟨(D : ℤ) • ξ - latticePairing T α ξ • ν, ?_, ?_⟩
  · simp only [map_sub, map_zsmul, hν, smul_eq_mul]
    ring
  · intro γ hγ hγζ
    have hfγ : f γ = 0 := by
      by_contra hne
      apply hξ (f γ) ⟨⟨γ, hγ, rfl⟩, hne⟩
      simp only [map_sub, map_zsmul, smul_eq_mul] at hγζ
      simp only [f, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
      linear_combination hγζ
    rw [LinearIndependent.pair_iff]
    intro h
    have h' := h (-(latticePairing T γ ν)) (D : ℤ) (by
      simp only [f] at hfγ
      rw [neg_smul, ← hfγ]
      abel)
    exact (Int.natCast_ne_zero.mpr hD.ne') h'.2

/-- A cocharacter in the kernel of a nonzero character `α` of a split torus that is generic
with respect to a finite set `s` of characters: it pairs to zero with `α`, and every
character of `s` pairing to zero with it is linearly dependent with `α` over `ℤ`. It is a
choice of the cocharacter given by `exists_cocharacter_pairing_eq_zero`. -/
def kernelCocharacter (hT : IsSplitTorus T.toGrp) {α : characterLattice T} (hα : α ≠ 0)
    {s : Set (characterLattice T)} (hs : s.Finite) : cocharacterLattice T :=
  Classical.choose (exists_cocharacter_pairing_eq_zero hT hα hs)

/-- The kernel cocharacter pairs to zero with `α`. -/
theorem latticePairing_kernelCocharacter (hT : IsSplitTorus T.toGrp) {α : characterLattice T}
    (hα : α ≠ 0) {s : Set (characterLattice T)} (hs : s.Finite) :
    latticePairing T α (kernelCocharacter hT hα hs) = 0 :=
  (Classical.choose_spec (exists_cocharacter_pairing_eq_zero hT hα hs)).1

/-- A character of `s` pairing to zero with the kernel cocharacter is linearly dependent with
`α` over `ℤ`. -/
theorem not_linearIndependent_of_latticePairing_kernelCocharacter (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ≠ 0) {s : Set (characterLattice T)} (hs : s.Finite)
    {γ : characterLattice T} (hγ : γ ∈ s)
    (hγζ : latticePairing T γ (kernelCocharacter hT hα hs) = 0) :
    ¬ LinearIndependent ℤ ![α, γ] :=
  (Classical.choose_spec (exists_cocharacter_pairing_eq_zero hT hα hs)).2 γ hγ hγζ

end Lattice

section Centralizer

variable {G L : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [IsAffineHom L.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T) {j : L ⟶ G}
  (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)

omit [IsAffineHom G.X.hom] [IsAffineHom L.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A cocharacter followed by a character is the power map given by their pairing. -/
theorem comp_eq_powerHom (γ : characterLattice T) :
    ζ ≫ γ = Gm.powerHom _ (latticePairing T γ ζ) := by
  rw [latticePairing_apply]
  exact eq_gmEndEquiv_zsmul k (ζ ≫ γ)

include hj

/-- Weight vectors of a character pairing to zero with `ζ` lie in the tangent image of a
representative of the dynamic centralizer of `ζ`. -/
theorem weightSpace_le_range_centralizer {α : characterLattice T}
    (hα : latticePairing T α ζ = 0) :
    weightSpace i α ≤ LinearMap.range (Lie.targetMapLinear j _) := by
  intro X hX
  apply (hj.mem_range_lieKernelHomLinear X).mpr
  apply (dynamicLie k G (CommGroupScheme.groupHom ζ ≫ i) X.toMul).1.mpr
  have h := weightSpace_le_comp ζ i α hX
  rw [comp_eq_powerHom, hα] at h
  exact h

/-- A root pairing to zero with `ζ` is a root of the torus in the centralizer
representative. -/
theorem mem_roots_torusFactor {α : characterLattice T} (hα : α ∈ roots i)
    (hαζ : latticePairing T α ζ = 0) :
    α ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) := by
  have : Mono j.hom.hom := hj.1
  refine ⟨hα.1, fun hbot => hα.2 ?_⟩
  rw [eq_bot_iff]
  intro X hX
  obtain ⟨Y, rfl⟩ := weightSpace_le_range_centralizer i ζ hj hαζ hX
  have hY : Y ∈ weightSpace (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α := by
    apply (lieKernelHomLinear_mem_weightSpace_iff j _ α Y).mp
    rw [Dynamic.torusFactor_comp]
    exact hX
  rw [hbot, Submodule.mem_bot] at hY
  rw [hY, map_zero]
  exact Submodule.zero_mem _

/-- Every root of the torus in the centralizer representative is a root of the torus in
`G` that pairs to zero with `ζ`. -/
theorem mem_roots_of_mem_roots_torusFactor {γ : characterLattice T}
    (hγ : γ ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj)) :
    γ ∈ roots i ∧ latticePairing T γ ζ = 0 := by
  have : Mono j.hom.hom := hj.1
  refine ⟨?_, ?_⟩
  · have h := roots_subset_comp j (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) hγ
    rwa [Dynamic.torusFactor_comp] at h
  · by_contra hne
    apply hγ.2
    rw [eq_bot_iff]
    intro Y hY
    rw [Submodule.mem_bot]
    apply Lie.targetMapLinear_injective j _
    rw [map_zero]
    have hX : Lie.targetMapLinear j _ Y ∈ weightSpace i γ := by
      have h := lieKernelHomLinear_mem_weightSpace j
        (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) γ hY
      rwa [Dynamic.torusFactor_comp] at h
    have h0 : Lie.targetMapLinear j _ Y ∈
        weightSpace (CommGroupScheme.groupHom ζ ≫ i) (Gm.powerHom _ 0) :=
      (dynamicLie k G _ (Lie.targetMapLinear j _ Y).toMul).1.mp
        ((hj.mem_range_lieKernelHomLinear _).mp ⟨Y, rfl⟩)
    have hn : Lie.targetMapLinear j _ Y ∈
        weightSpace (CommGroupScheme.groupHom ζ ≫ i) (Gm.powerHom _ (latticePairing T γ ζ)) := by
      have h := weightSpace_le_comp ζ i γ hX
      rwa [comp_eq_powerHom] at h
    have e0 := DynamicLie.weightCoeffs_apply_of_mem k G (CommGroupScheme.groupHom ζ ≫ i)
      _ 0 0 h0
    have en := DynamicLie.weightCoeffs_apply_of_mem k G (CommGroupScheme.groupHom ζ ≫ i)
      _ _ 0 hn
    simp only [↓reduceIte] at e0
    simp only [Ne.symm hne, ↓reduceIte] at en
    exact e0.symm.trans en

end Centralizer

end RootReducedness

open RootReducedness in
/-- **Reduction of root reducedness to proportional roots.** Root reducedness for all
connected reductive groups follows from its case in which all roots are pairwise linearly
dependent, together with connected reductivity of dynamic centralizers. -/
theorem rootReducedness_of_rankOne (hrank : RankOneRootReducednessStatement.{u})
    (hcent : DynamicCentralizerReductiveStatement.{u}) : RootReducednessStatement.{u} := by
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  intro α hα β hβ hαβ
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have hαζ := latticePairing_kernelCocharacter hT hα.1 (hT.finite_relativeRoots i)
  have hζ := fun γ (hγ : γ ∈ roots i) =>
    not_linearIndependent_of_latticePairing_kernelCocharacter hT hα.1
      (hT.finite_relativeRoots i) hγ
  generalize kernelCocharacter hT hα.1 (hT.finite_relativeRoots i) = ζ at hαζ hζ
  have hj := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hjc := Dynamic.Affine.isClosedSubgroup_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hL := hcent k G hG _ _ _ hjc hj
  have := hL.isAffineHom
  have hiL : IsMaximalTorus (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) :=
    IsMaximalTorus.of_comp hjc (by rwa [Dynamic.torusFactor_comp])
  have hβζ : latticePairing T β ζ = 0 := by
    rw [LinearIndependent.pair_iff] at hαβ
    push Not at hαβ
    obtain ⟨s, t, hst, hne⟩ := hαβ
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul, add_zero] at hst
      exact zsmul_ne_zero hT hα.1 (fun hs => hne hs rfl) hst
    have h := congrArg (fun x => latticePairing T x ζ) hst
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, hαζ,
      smul_eq_mul, mul_zero, zero_add, map_zero, LinearMap.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left ht
  refine hrank k _ hL T hT _ hiL ?_ α (mem_roots_torusFactor i ζ hj hα hαζ)
    β (mem_roots_torusFactor i ζ hj hβ hβζ)
  intro γ hγ δ hδ
  obtain ⟨hγ', hγζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hγ
  obtain ⟨hδ', hδζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hδ
  exact not_linearIndependent_of_not_linearIndependent hT hα.1 hδ'.1
    (hζ γ hγ' hγζ) (hζ δ hδ' hδζ)

end Langlands.GroupScheme
