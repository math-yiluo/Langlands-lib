import Langlands.Global.GMFamilyFieldDescentGroups
import Langlands.Global.GMFamilyFieldDescentRealization
import Langlands.GroupScheme.Lie.FiniteDimensional

/-! # Linear-algebra descent data from a split torus with an integral root datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Classical

namespace Langlands.GMFamily.FieldDescentTori

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {A₁ T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- The roots of a split torus, as real functionals. -/
def rootFunctionals (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) :
    Finset (Module.Dual ℝ (V T)) :=
  (hT.finite_relativeRoots t).toFinset.image (eval T)

/-- The multiplicity of a real functional: the total dimension of the weight spaces of the roots
with that functional. -/
def rootMult (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (ℓ : Module.Dual ℝ (V T)) : ℝ :=
  ∑ γ ∈ (hT.finite_relativeRoots t).toFinset.filter (fun γ => eval T γ = ℓ),
    (Module.finrank K (weightSpace t γ) : ℝ)

theorem rootMult_eval (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) {γ : characterLattice T}
    (hγ : γ ∈ relativeRoots t) :
    rootMult hT t (eval T γ) = Module.finrank K (weightSpace t γ) := by
  have h : (hT.finite_relativeRoots t).toFinset.filter (fun δ => eval T δ = eval T γ) = {γ} := by
    ext δ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact eval_injective hT h
    · rintro rfl
      exact ⟨hγ, rfl⟩
  rw [rootMult, h, Finset.sum_singleton]

theorem finrank_weightSpace_pos {t : T.toGrp ⟶ G} {γ : characterLattice T}
    (hγ : γ ∈ relativeRoots t) : 0 < Module.finrank K (weightSpace t γ) := by
  rw [relativeRoots_eq_roots] at hγ
  apply Nat.pos_of_ne_zero
  rw [Ne, Submodule.finrank_eq_zero]
  exact hγ.2

/-- **Descent data from a split torus.** A split torus `T ⟶ G` whose relative roots carry an
integral root datum with reflection-invariant multiplicities, a homomorphism `A₁ ⟶ T` identifying
the real cocharacters of `A₁` with a Levi flat, and complementary subspaces `B`, `K'` of `V A₁`
satisfying the fibre-sum condition give linear-algebra descent data. -/
def torusData (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (g : A₁ ⟶ T)
    (hinj : Function.Injective (cocharacterMapReal g))
    (hrange : LinearMap.range (cocharacterMapReal g) =
      rootAnnihilator T {γ | γ ∈ relativeRoots t ∧
        ∀ x : V A₁, eval T γ (cocharacterMapReal g x) = 0})
    (hcor : ∀ γ ∈ relativeRoots t, ∃ γv : cocharacterLattice T, latticePairing T γ γv = 2 ∧
      ∀ δ ∈ relativeRoots t, δ - latticePairing T δ γv • γ ∈ relativeRoots t ∧
        Module.finrank K (weightSpace t (δ - latticePairing T δ γv • γ)) =
          Module.finrank K (weightSpace t δ))
    (B K' : Submodule ℝ (V A₁)) (hcompl : IsCompl B K')
    (hspecial : ∀ γ ∈ relativeRoots t,
      ((eval T γ).comp (cocharacterMapReal g)).domRestrict B ≠ 0 → ∀ y ∈ K',
        ∑ δ ∈ (hT.finite_relativeRoots t).toFinset.filter (fun δ =>
            ((eval T δ).comp (cocharacterMapReal g)).domRestrict B =
              ((eval T γ).comp (cocharacterMapReal g)).domRestrict B),
          (Module.finrank K (weightSpace t δ) : ℝ) * eval T δ (cocharacterMapReal g y) = 0) :
    FieldDescentData (V A₁) (V T) where
  κ := cocharacterMapReal g
  injective := hinj
  roots := rootFunctionals hT t
  zero_notMem := by
    intro h
    obtain ⟨γ, hγ, h0⟩ := Finset.mem_image.mp h
    rw [Set.Finite.mem_toFinset, relativeRoots_eq_roots] at hγ
    exact hγ.1 ((eval_eq_zero_iff hT).mp h0)
  mult := rootMult hT t
  mult_pos := by
    intro ℓ h
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp h
    rw [Set.Finite.mem_toFinset] at hγ
    rw [rootMult_eval hT t hγ]
    exact_mod_cast finrank_weightSpace_pos hγ
  coroot := by
    intro ℓ h
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp h
    rw [Set.Finite.mem_toFinset] at hγ
    obtain ⟨γv, h2, hδ⟩ := hcor γ hγ
    refine ⟨(1 : ℝ) ⊗ₜ[ℤ] γv, ?_, ?_⟩
    · rw [eval_tmul, h2]
      norm_num
    · intro f₂ hf₂
      obtain ⟨δ, hδR, rfl⟩ := Finset.mem_image.mp hf₂
      rw [Set.Finite.mem_toFinset] at hδR
      obtain ⟨hmem, hdim⟩ := hδ δ hδR
      have hval : eval T δ ((1 : ℝ) ⊗ₜ[ℤ] γv) = (latticePairing T δ γv : ℝ) := by
        rw [eval_tmul, one_mul]
      have heq : eval T δ - eval T δ ((1 : ℝ) ⊗ₜ[ℤ] γv) • eval T γ =
          eval T (δ - latticePairing T δ γv • γ) := by
        rw [hval, eval_sub, eval_zsmul]
      refine ⟨?_, ?_, ⟨latticePairing T δ γv, hval⟩⟩
      · rw [heq]
        exact Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).mpr hmem)
      · rw [heq, rootMult_eval hT t hmem, rootMult_eval hT t hδR, hdim]
  range_eq := by
    rw [hrange]
    ext v
    rw [mem_rootAnnihilator]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro H ℓ hℓ
      obtain ⟨hℓR, hℓ0⟩ := Finset.mem_filter.mp hℓ
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hℓR
      rw [Set.Finite.mem_toFinset] at hγ
      exact H γ ⟨hγ, fun x => LinearMap.congr_fun hℓ0 x⟩
    · rintro H γ ⟨hγ, hγ0⟩
      exact H (eval T γ) (Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).mpr hγ), LinearMap.ext hγ0⟩)
  B := B
  K := K'
  isCompl := hcompl
  special := by
    intro ℓ h hβ y hy
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp h
    rw [Set.Finite.mem_toFinset] at hγ
    have hs := hspecial γ hγ hβ y hy
    rw [rootFunctionals, Finset.filter_image, Finset.sum_image
      (fun δ _ δ' _ hδ => eval_injective hT hδ)]
    rw [← hs]
    apply Finset.sum_congr rfl
    intro δ hδ
    rw [rootMult_eval hT t ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hδ).1)]

end Langlands.GMFamily.FieldDescentTori
