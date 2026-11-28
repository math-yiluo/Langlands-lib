import Langlands.Global.GMFamilyFieldDescentTori
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel

/-! # Roots and characters of nested split components across a field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GMFamily.FieldDescentTori

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]


section Roots

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}

local instance fieldDescentGroupsAffine : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance fieldDescentGroupsFiniteType : LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (hA : IsSplitTorus A.toGrp) (hA₁ : IsSplitTorus A₁.toGrp)
  (j : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj A ⟶ A₁)
  (i : A.toGrp ⟶ G) (i₁ : A₁.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
  (hcomp : (GroupScheme.baseChange (algebraBaseMap k K)).map i = CommGroupScheme.groupHom j ≫ i₁)
include hA hA₁ hcomp

/-- Every coarse root lifts to a fine root. -/
theorem exists_fine_of_mem_roots {β : characterLattice A} (hβ : β ∈ roots i) :
    ∃ α ∈ roots i₁, j ≫ α = characterLattice.baseChange (algebraBaseMap k K) A β := by
  have h := (mem_roots_baseChange_iff (K := K) G A hA i β).mpr hβ
  rw [hcomp] at h
  obtain ⟨-, α, hα, he⟩ := (mem_roots_comp_iff hA₁ (hA.baseChange (algebraBaseMap k K)) j i₁ _).mp h
  exact ⟨α, hα, he⟩

/-- A fine root with nonzero restriction restricts to a coarse root. -/
theorem exists_coarse_of_mem_roots {α : characterLattice A₁} (hα : α ∈ roots i₁)
    (h0 : j ≫ α ≠ 0) : ∃ β ∈ roots i, j ≫ α = characterLattice.baseChange (algebraBaseMap k K) A β := by
  obtain ⟨β, hβ⟩ := (hA.characterLattice_baseChange_bijective (algebraBaseMap k K) A).surjective (j ≫ α)
  refine ⟨β, ?_, hβ.symm⟩
  apply (mem_roots_baseChange_iff (K := K) G A hA i β).mp
  rw [hcomp, hβ]
  exact (mem_roots_comp_iff hA₁ (hA.baseChange (algebraBaseMap k K)) j i₁ _).mpr ⟨h0, α, hα, rfl⟩

end Roots

section Characters

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
  {M : GroupScheme (Spec (CommRingCat.of k))} {M₁ : GroupScheme (Spec (CommRingCat.of K))}

/-- The restriction to the fine split component of the scalar extension of a rational
character. -/
abbrev fineCharacter (a₁ : A₁.toGrp ⟶ M₁) (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M)
    (χ : rationalCharacters M) : characterLattice A₁ :=
  characterRestrict a₁ (characterRestrict m (rationalCharacters.baseChange (algebraBaseMap k K) χ))

/-- **Parameter compatibility.** The fine restriction of a scalar-extended rational
character, pulled back to the scalar extension of the coarse split component, is the scalar
extension of the coarse restriction. -/
theorem comp_fineCharacter (a : A.toGrp ⟶ M) (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M)
    (j : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj A ⟶ A₁)
    (hj : CommGroupScheme.groupHom j ≫ a₁ ≫ m = (GroupScheme.baseChange (algebraBaseMap k K)).map a)
    (χ : rationalCharacters M) :
    j ≫ fineCharacter a₁ m χ =
      characterLattice.baseChange (algebraBaseMap k K) A (characterRestrict a χ) := by
  have h := characterLattice.baseChange_torusCharacterRestrict (algebraBaseMap k K) a χ
  change _ = characterLattice.baseChange _ A (torusCharacterRestrict a χ)
  rw [h, ← hj]
  rfl

end Characters

section Complement

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
  {M : GroupScheme (Spec (CommRingCat.of k))} {M₁ : GroupScheme (Spec (CommRingCat.of K))}

/-- The fine restriction of scalar-extended rational characters, as an additive map. -/
def fineCharacterHom (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M) :
    rationalCharacters M →+ characterLattice A₁ :=
  (characterRestrict a₁).comp ((characterRestrict m).comp
    (rationalCharacters.baseChange (algebraBaseMap k K)))

/-- The real functionals of the fine restrictions of rational characters. -/
def fineEval (a₁ : A₁.toGrp ⟶ M₁) (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M) :
    rationalCharacters M →ₗ[ℤ] Module.Dual ℝ (V A₁) :=
  ((evalHom A₁).comp (fineCharacterHom a₁ m)).toIntLinearMap

theorem fineEval_apply (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M) (χ : rationalCharacters M) :
    fineEval a₁ m χ = eval A₁ (fineCharacter a₁ m χ) := rfl

/-- The common kernel of the fine restrictions of the rational characters. -/
def fineKernel (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M) : Submodule ℝ (V A₁) :=
  ⨅ χ : rationalCharacters M, LinearMap.ker (eval A₁ (fineCharacter a₁ m χ))

theorem mem_fineKernel {a₁ : A₁.toGrp ⟶ M₁}
    {m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M} {v : V A₁} :
    v ∈ fineKernel a₁ m ↔ ∀ χ, eval A₁ (fineCharacter a₁ m χ) v = 0 := by
  simp [fineKernel, Submodule.mem_iInf, LinearMap.mem_ker]

variable (a : A.toGrp ⟶ M) (a₁ : A₁.toGrp ⟶ M₁)
  (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M)
  (j : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj A ⟶ A₁)
  (hj : CommGroupScheme.groupHom j ≫ a₁ ≫ m = (GroupScheme.baseChange (algebraBaseMap k K)).map a)
include hj

theorem eval_fineCharacter_inclusion (χ : rationalCharacters M) (x : V A) :
    eval A₁ (fineCharacter a₁ m χ) (fieldCocharacterInclusion j x) =
      eval A (characterRestrict a χ) x :=
  eval_fieldCocharacterInclusion_of_eq j (comp_fineCharacter a a₁ m j hj χ) x

omit hj in
/-- Restrictions of rational characters of finite index separate real cocharacters. -/
theorem eq_zero_of_forall_eval (hA : IsSplitTorus A.toGrp)
    (hfin : (characterRestrict a).range.FiniteIndex) {x : V A}
    (hx : ∀ χ : rationalCharacters M, eval A (characterRestrict a χ) x = 0) : x = 0 := by
  have hβ : ∀ β : characterLattice A, eval A β x = 0 := by
    intro β
    obtain ⟨χ, hχ⟩ := AddSubgroup.nsmul_index_mem (characterRestrict a).range β
    have h := hx χ
    rw [hχ, ← natCast_zsmul, eval_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
    have hn : ((characterRestrict a).range.index : ℝ) ≠ 0 := by
      exact_mod_cast AddSubgroup.FiniteIndex.index_ne_zero
    exact (mul_eq_zero.mp (by exact_mod_cast h)).resolve_left hn
  have hp := isPerfPair_of_isSplitTorus hA
  apply hp.bijective_right.injective
  rw [map_zero]
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.inductionOn with
  | tmul r β =>
    change pair A (r ⊗ₜ[ℤ] β) x = 0
    have : r ⊗ₜ[ℤ] β = r • ((1 : ℝ) ⊗ₜ[ℤ] β) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, LinearMap.smul_apply, ← eval_eq_pair, hβ, smul_zero]
  | add y z hy hz => simp only [map_add, hy, hz, LinearMap.zero_apply, add_zero]

omit hj in
/-- The inclusion of coarse real cocharacters is injective. -/
theorem fieldCocharacterInclusion_injective (hj' : CommGroupScheme.groupHom j ≫ a₁ ≫ m =
      (GroupScheme.baseChange (algebraBaseMap k K)).map a)
    (hA : IsSplitTorus A.toGrp) (hfin : (characterRestrict a).range.FiniteIndex) :
    Function.Injective (fieldCocharacterInclusion j) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply eq_zero_of_forall_eval a hA hfin
  intro χ
  rw [← eval_fineCharacter_inclusion a a₁ m j hj', hx, map_zero]

/-- **The coarse cocharacters and the common kernel of the coarse characters are
complementary.** -/
theorem isCompl_fineKernel (hA : IsSplitTorus A.toGrp) (hA₁ : IsSplitTorus A₁.toGrp)
    (hinj : Function.Injective (characterRestrict a))
    (hfin : (characterRestrict a).range.FiniteIndex) :
    IsCompl (LinearMap.range (fieldCocharacterInclusion j)) (fineKernel a₁ m) := by
  have : Module.Finite ℝ (V A) := hA.finite_realCocharacterSpace
  have : Module.Finite ℝ (V A₁) := hA₁.finite_realCocharacterSpace
  have hι : Function.Injective (fieldCocharacterInclusion j) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply eq_zero_of_forall_eval a hA hfin
    intro χ
    rw [← eval_fineCharacter_inclusion a a₁ m j hj, hx, map_zero]
  have hdis : Disjoint (LinearMap.range (fieldCocharacterInclusion j)) (fineKernel a₁ m) := by
    rw [Submodule.disjoint_def]
    rintro v ⟨x, rfl⟩ hK
    have hx : x = 0 := eq_zero_of_forall_eval a hA hfin fun χ => by
      rw [← eval_fineCharacter_inclusion a a₁ m j hj]
      exact mem_fineKernel.mp hK χ
    rw [hx, map_zero]
  refine ⟨hdis, ?_⟩
  rw [codisjoint_iff]
  let Lℝ := (fineEval a₁ m).liftBaseChange ℝ
  let W := LinearMap.range Lℝ
  have hKW : fineKernel a₁ m = W.dualCoannihilator := by
    ext v
    rw [mem_fineKernel, Submodule.mem_dualCoannihilator]
    constructor
    · intro h ℓ hℓ
      have hle : W ≤ LinearMap.ker (Module.Dual.eval ℝ (V A₁) v) := by
        change LinearMap.range Lℝ ≤ _
        rw [LinearMap.range_liftBaseChange]
        apply Submodule.span_le.mpr
        rintro _ ⟨χ, rfl⟩
        exact h χ
      exact hle hℓ
    · intro h χ
      exact h _ ⟨(1 : ℝ) ⊗ₜ[ℤ] χ, by simp [Lℝ, fineEval_apply]⟩
  let r : Module.Dual ℝ (V A₁) →ₗ[ℝ] Module.Dual ℝ (V A) := (fieldCocharacterInclusion j).dualMap
  have hΨ : r ∘ₗ Lℝ = (characterDualEquiv hA).toLinearMap ∘ₗ
      ((characterRestrict a).toIntLinearMap.baseChange ℝ) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s χ
    apply LinearMap.ext
    intro x
    simp only [Lℝ, r, LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, LinearMap.dualMap_apply,
      LinearMap.smul_apply, fineEval_apply, smul_eq_mul, LinearMap.baseChange_tmul,
      LinearEquiv.coe_coe, characterDualEquiv_apply]
    rw [eval_fineCharacter_inclusion a a₁ m j hj, eval_eq_pair]
    have : s ⊗ₜ[ℤ] (characterRestrict a).toIntLinearMap χ =
        s • ((1 : ℝ) ⊗ₜ[ℤ] (characterRestrict a χ)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hΨinj : Function.Injective (r ∘ₗ Lℝ) := by
    rw [hΨ]
    refine (characterDualEquiv hA).injective.comp ?_
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) _ hinj
  have hr : Function.Injective (r.domRestrict W) := by
    rintro ⟨_, ⟨t₁, rfl⟩⟩ ⟨_, ⟨t₂, rfl⟩⟩ h
    have h' : (r ∘ₗ Lℝ) t₁ = (r ∘ₗ Lℝ) t₂ := h
    have ht : t₁ = t₂ := hΨinj h'
    subst ht
    rfl
  have hW : Module.finrank ℝ W ≤ Module.finrank ℝ (V A) := by
    calc Module.finrank ℝ W ≤ Module.finrank ℝ (Module.Dual ℝ (V A)) :=
          LinearMap.finrank_le_finrank_of_injective hr
      _ = Module.finrank ℝ (V A) := Subspace.dual_finrank_eq
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  have hB : Module.finrank ℝ (LinearMap.range (fieldCocharacterInclusion j)) =
      Module.finrank ℝ (V A) := LinearMap.finrank_range_of_inj hι
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (fieldCocharacterInclusion j)) (fineKernel a₁ m)
  rw [hdis.eq_bot, finrank_bot, add_zero, hB, hKW] at hsup
  apply Submodule.eq_top_of_finrank_eq
  have hle := Submodule.finrank_le (LinearMap.range (fieldCocharacterInclusion j) ⊔
    fineKernel a₁ m)
  rw [hKW] at hle ⊢
  omega

end Complement

end Langlands.GMFamily.FieldDescentTori
