import Langlands.Global.GMFamilyFieldDescent
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Langlands.GroupScheme.Torus.WeightBaseChangeComparison
import Langlands.Geometry.Building.RealTorusDuality

/-! # Characters, cocharacters and weights of split tori for field descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GMFamily.FieldDescentTori

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

section Lattice

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The integral pairing of a split torus is perfect. -/
theorem latticePairing_isPerfPair (hT : IsSplitTorus T.toGrp) : (latticePairing T).IsPerfPair := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact latticePairing_isPerfPair_of_split eC

/-- Characters of a split torus are determined by their real functionals. -/
theorem eval_injective (hT : IsSplitTorus T.toGrp) : Function.Injective (eval T) := by
  intro χ χ' h
  apply (latticePairing_isPerfPair hT).bijective_left.injective
  ext ν
  have h' := congrArg (fun f : Module.Dual ℝ (V T) => f ((1 : ℝ) ⊗ₜ[ℤ] ν)) h
  simp only [eval_tmul, one_mul, Int.cast_inj] at h'
  exact h'

theorem eval_zero : eval T (0 : characterLattice T) = 0 := by
  rw [eval_eq_pair, TensorProduct.tmul_zero, map_zero]

theorem eval_add (χ χ' : characterLattice T) : eval T (χ + χ') = eval T χ + eval T χ' := by
  rw [eval_eq_pair, eval_eq_pair, eval_eq_pair, TensorProduct.tmul_add, map_add]

theorem eval_sub (χ χ' : characterLattice T) : eval T (χ - χ') = eval T χ - eval T χ' := by
  rw [eval_eq_pair, eval_eq_pair, eval_eq_pair, TensorProduct.tmul_sub, map_sub]

theorem eval_zsmul (n : ℤ) (χ : characterLattice T) : eval T (n • χ) = (n : ℝ) • eval T χ := by
  rw [eval_eq_pair, eval_eq_pair, TensorProduct.tmul_smul, map_zsmul]
  exact (Int.cast_smul_eq_zsmul ℝ n _).symm

/-- Evaluation as an additive map. -/
def evalHom (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    characterLattice T →+ Module.Dual ℝ (V T) where
  toFun := eval T
  map_zero' := eval_zero
  map_add' := eval_add

@[simp] theorem evalHom_apply (χ : characterLattice T) : evalHom T χ = eval T χ := rfl

theorem eval_eq_zero_iff (hT : IsSplitTorus T.toGrp) {χ : characterLattice T} :
    eval T χ = 0 ↔ χ = 0 :=
  ⟨fun h => eval_injective hT (h.trans eval_zero.symm), fun h => h ▸ eval_zero⟩

/-- Character restriction and cocharacter postcomposition are adjoint. -/
theorem eval_cocharacterMapReal (t : S ⟶ T) (a : characterLattice T) (v : V S) :
    eval T a (cocharacterMapReal t v) = eval S (t ≫ a) v := by
  rw [eval_eq_pair, eval_eq_pair, pair_cocharacterMapReal]
  rfl

theorem eval_comp_cocharacterMapReal (t : S ⟶ T) (a : characterLattice T) :
    (eval T a).comp (cocharacterMapReal t) = eval S (t ≫ a) :=
  LinearMap.ext (eval_cocharacterMapReal t a)

end Lattice

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "bmap" => algebraBaseMap k K

/-- Base change of real cocharacters. -/
def cocharacterBaseChangeReal (A : CommGroupScheme (Spec (CommRingCat.of k))) :
    V A →ₗ[ℝ] V ((CommGroupScheme.baseChange bmap).obj A) :=
  (cocharacterLattice.baseChange bmap A).toIntLinearMap.baseChange ℝ

/-- Evaluation commutes with base change. -/
theorem eval_baseChange (β : characterLattice A) (x : V A) :
    eval ((CommGroupScheme.baseChange bmap).obj A) (characterLattice.baseChange bmap A β)
      (cocharacterBaseChangeReal (K := K) A x) = eval A β x := by
  induction x using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [cocharacterBaseChangeReal, LinearMap.baseChange_tmul, eval_tmul]
    change r * (latticePairing _ (characterLattice.baseChange bmap A β)
      (cocharacterLattice.baseChange bmap A ν) : ℝ) = r * (latticePairing A β ν : ℝ)
    rw [latticePairing_baseChange]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Evaluation of a character of the larger split component on the image of a real
cocharacter of the original one. -/
theorem eval_fieldCocharacterInclusion {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
    (j : (CommGroupScheme.baseChange bmap).obj A ⟶ A₁) (α : characterLattice A₁) (x : V A) :
    eval A₁ α (fieldCocharacterInclusion j x) =
      eval ((CommGroupScheme.baseChange bmap).obj A) (j ≫ α)
        (cocharacterBaseChangeReal (K := K) A x) := by
  change eval A₁ α (cocharacterMapReal j (cocharacterBaseChangeReal (K := K) A x)) = _
  rw [eval_cocharacterMapReal]

theorem eval_fieldCocharacterInclusion_of_eq {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
    (j : (CommGroupScheme.baseChange bmap).obj A ⟶ A₁) {α : characterLattice A₁}
    {β : characterLattice A} (h : j ≫ α = characterLattice.baseChange bmap A β) (x : V A) :
    eval A₁ α (fieldCocharacterInclusion j x) = eval A β x := by
  rw [eval_fieldCocharacterInclusion, h, eval_baseChange]

end BaseChange

section Dimension

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The dimension of a finite supremum of independent subspaces is the sum of dimensions. -/
theorem finrank_biSup {I : Type*} {p : I → Submodule K M} (hp : iSupIndep p) (s : Finset I) :
    Module.finrank K (⨆ i ∈ s, p i : Submodule K M) = ∑ i ∈ s, Module.finrank K (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (p a) (⨆ i ∈ s, p i) := hp.disjoint_biSup ha
    have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ s, p i)
    rw [hd.eq_bot, finrank_bot, add_zero] at h
    exact h

end Dimension

section Weights

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

open Classical in
/-- **Dimensions of restricted weight spaces.** For a homomorphism of split tori `f : T' ⟶ T`
and a nonzero character `ψ` of `T'`, the weight space of `ψ` for the restricted action has
dimension the sum of the dimensions of the weight spaces of the roots of `T` restricting to
`ψ`. -/
theorem finrank_weightSpace_comp (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (f : T' ⟶ T) (i : T.toGrp ⟶ G) {ψ : characterLattice T'} (hψ : ψ ≠ 0) :
    Module.finrank k (weightSpace (CommGroupScheme.groupHom f ≫ i) ψ) =
      ∑ χ ∈ (hT.finite_relativeRoots i).toFinset.filter (fun χ => f ≫ χ = ψ),
        Module.finrank k (weightSpace i χ) := by
  have hind := (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep
  have heq : weightSpace (CommGroupScheme.groupHom f ≫ i) ψ =
      ⨆ χ ∈ (hT.finite_relativeRoots i).toFinset.filter (fun χ => f ≫ χ = ψ), weightSpace i χ := by
    rw [weightSpace_comp_eq_iSup hT hT' f i ψ]
    apply le_antisymm
    · refine iSup_le fun χ => ?_
      by_cases h : weightSpace i χ.val = ⊥
      · rw [h]
        exact bot_le
      · have hχ0 : χ.val ≠ 0 := by
          intro h0
          apply hψ
          rw [← χ.prop, h0]
          simp
        have hmem : χ.val ∈ (hT.finite_relativeRoots i).toFinset.filter
            (fun χ => f ≫ χ = ψ) := by
          rw [Finset.mem_filter, Set.Finite.mem_toFinset, relativeRoots_eq_roots]
          exact ⟨⟨hχ0, h⟩, χ.prop⟩
        exact le_biSup (fun χ => weightSpace i χ) hmem
    · refine iSup₂_le fun χ hχ => ?_
      exact le_iSup_of_le (⟨χ, (Finset.mem_filter.mp hχ).2⟩ :
        {χ : characterLattice T // f ≫ χ = ψ}) le_rfl
  rw [heq, finrank_biSup hind]

end Weights

end Langlands.GMFamily.FieldDescentTori
