import Langlands.Cohomology.Tate.ZeroDefinitions
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- The actual representation coinduced from the trivial subgroup. -/
abbrev coinduced (A : Rep.{u} R G) : Rep.{u} R G :=
  Rep.coind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A)

/-- The underlying functions of coinduction from the trivial subgroup. -/
def coinducedFunctions (A : Rep.{u} R G) : (G → A) ≃ₗ[R] coinduced A where
  toFun f := ⟨f, fun h g => by
    have hh : (h : G) = 1 := Subgroup.mem_bot.mp h.property
    change f ((h : G) * g) = A.ρ h (f g)
    simp [hh]⟩
  invFun f := f.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The equivariant inclusion into the actual coinduced representation. -/
def coinducedEmbedding (A : Rep.{u} R G) : A ⟶ coinduced A :=
  Rep.resCoindToHom (⊥ : Subgroup G).subtype A
    (Rep.res (⊥ : Subgroup G).subtype A) (𝟙 _)

/-- Evaluation at the group identity splits the inclusion as a scalar-linear map. -/
def coinducedEvaluation (A : Rep.{u} R G) : coinduced A →ₗ[R] A :=
  (LinearMap.proj 1).comp (coinducedFunctions A).symm.toLinearMap

lemma coinducedEvaluation_embedding (A : Rep.{u} R G) (a : A) :
    coinducedEvaluation A ((coinducedEmbedding A).hom a) = a := by
  change A.ρ 1 a = a
  simp

/-- A vector supported at the identity, as an element of the coinduced module. -/
def coinducedDelta (A : Rep.{u} R G) : A →ₗ[R] coinduced A := by
  classical
  exact (coinducedFunctions A).toLinearMap.comp (LinearMap.single R (fun _ : G => A) 1)

lemma coinducedDelta_apply [DecidableEq G] (A : Rep.{u} R G) (a : A) (g : G) :
    (coinducedDelta A a).1 g = if g = 1 then a else 0 := by
  classical
  simp [coinducedDelta, coinducedFunctions, Pi.single_apply]

lemma coinduced_action_apply (A : Rep.{u} R G) (g : G) (f : coinduced A) (x : G) :
    ((coinduced A).ρ g f).1 x = f.1 (x * g) := rfl

variable [Fintype G]

lemma coinduced_norm_apply (A : Rep.{u} R G) (f : coinduced A) (x : G) :
    ((coinduced A).ρ.norm f).1 x = ∑ g : G, f.1 g := by
  simp only [Representation.norm, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply]
  exact Equiv.sum_comp (Equiv.mulLeft x) f.1

lemma coinduced_norm_delta (A : Rep.{u} R G) (a : A) (x : G) :
    ((coinduced A).ρ.norm (coinducedDelta A a)).1 x = a := by
  classical
  rw [coinduced_norm_apply]
  calc
    (∑ g : G, (coinducedDelta A a).1 g) = ∑ g : G, if g = 1 then a else 0 :=
      Finset.sum_congr rfl (fun g _ => coinducedDelta_apply A a g)
    _ = a := by simp

omit [Fintype G] in
lemma coinduced_invariant_constant (A : Rep.{u} R G) (f : (coinduced A).ρ.invariants) (g : G) :
    (f : coinduced A).1 g = (f : coinduced A).1 1 := by
  have hh := congrArg (fun z : coinduced A => z.1 1) (f.property g)
  change (f : coinduced A).1 (1 * g) = (f : coinduced A).1 1 at hh
  simpa only [one_mul] using hh

lemma coinduced_norm_surjective (A : Rep.{u} R G) :
    Function.Surjective (normToInvariants (coinduced A)) := by
  intro f
  refine ⟨coinducedDelta A ((f : coinduced A).1 1), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact (coinduced_norm_delta A _ g).trans (coinduced_invariant_constant A f g).symm

lemma coinduced_tate_zero (A : Rep.{u} R G) : IsZero (tateCohomology (coinduced A) 0) := by
  have hr : normImage (coinduced A) = ⊤ :=
    LinearMap.range_eq_top.mpr (coinduced_norm_surjective A)
  have hz : Subsingleton (InvariantsModNorm (coinduced A)) := by
    change Subsingleton ((coinduced A).ρ.invariants ⧸ normImage (coinduced A))
    rw [hr]
    infer_instance
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R (InvariantsModNorm (coinduced A)))).of_iso (zeroEquiv (coinduced A))

lemma coinduced_tate_pos (A : Rep.{u} R G) (n : ℕ) :
    IsZero (tateCohomology (coinduced A) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
    (Rep.res (⊥ : Subgroup G).subtype A) n).of_iso
      ((TateCohomology.isoGroupCohomology (n + 1)).app (coinduced A) ≪≫
        groupCohomology.coindIso (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))

lemma coinduced_tate_neg (A : Rep.{u} R G) (n : ℕ) :
    IsZero (tateCohomology (coinduced A) (-(n + 2 : ℤ))) := by
  classical
  exact (isZero_groupHomology_succ_of_subsingleton
    (Rep.res (⊥ : Subgroup G).subtype A) n).of_iso
      ((TateCohomology.isoGroupHomology (-(n + 2 : ℤ)) (n + 1) (by omega)).app (coinduced A) ≪≫
        (groupHomology.functor R G (n + 1)).mapIso
          (Rep.indCoindIso (Rep.res (⊥ : Subgroup G).subtype A)).symm ≪≫
        groupHomology.indIso (⊥ : Subgroup G) (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))

/-- A function is the sum of translates of its values supported at the identity. -/
lemma coinduced_decomposition (A : Rep.{u} R G) (f : coinduced A) :
    (∑ g : G, (coinduced A).ρ g⁻¹ (coinducedDelta A (f.1 g))) = f := by
  classical
  apply (coinducedFunctions A).symm.injective
  rw [map_sum]
  funext x
  simp only [Finset.sum_apply]
  change (∑ g : G, (coinducedDelta A (f.1 g)).1 (x * g⁻¹)) = f.1 x
  calc
    (∑ g : G, (coinducedDelta A (f.1 g)).1 (x * g⁻¹)) =
        ∑ g : G, if x * g⁻¹ = 1 then f.1 g else 0 :=
      Finset.sum_congr rfl (fun g _ => coinducedDelta_apply A (f.1 g) (x * g⁻¹))
    _ = f.1 x := by simp [mul_inv_eq_one]

/-- Every norm-zero coinduced vector is an explicit group-homology boundary. -/
lemma coinduced_norm_kernel_boundary (A : Rep.{u} R G) (f : coinduced A)
    (hf : (coinduced A).ρ.norm f = 0) :
    ∃ c : G →₀ coinduced A, groupHomology.d₁₀ (coinduced A) c = f := by
  classical
  have hs : (∑ g : G, f.1 g) = 0 := by
    calc
      (∑ g : G, f.1 g) = ((coinduced A).ρ.norm f).1 1 :=
        (coinduced_norm_apply A f 1).symm
      _ = 0 := congrArg (fun z : coinduced A => z.1 1) hf
  refine ⟨∑ g : G, Finsupp.single g (coinducedDelta A (f.1 g)), ?_⟩
  rw [map_sum]
  trans ∑ g : G, ((coinduced A).ρ g⁻¹ (coinducedDelta A (f.1 g)) -
    coinducedDelta A (f.1 g))
  · exact Finset.sum_congr rfl (fun g _ =>
      groupHomology.d₁₀_single (coinduced A) g (coinducedDelta A (f.1 g)))
  rw [Finset.sum_sub_distrib, coinduced_decomposition A f, ← map_sum, hs, map_zero, sub_zero]

/-- The coefficient presentation of the Tate complex at degree minus one. -/
abbrev minusOneShortComplex (A : Rep.{u} R G) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (groupHomology.d₁₀ A) A.norm.toModuleCatHom (Rep.comp_eq_zero A)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Comparison with the actual three terms of the Tate complex around degree minus one. -/
def minusOneShortComplexIso (A : Rep.{u} R G) :
    (tateComplex A).sc (-1) ≅ minusOneShortComplex A := by
  refine (tateComplex A).isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫ ?_
  change ShortComplex.mk ((groupHomology.inhomogeneousChains A).d 1 0) A.tateNorm _ ≅ _
  exact ShortComplex.isoMk (groupHomology.chainsIso₁ A) (groupHomology.chainsIso₀ A)
    (groupCohomology.cochainsIso₀ A) (groupHomology.comp_d₁₀_eq A)
    (by simp [Rep.tateNorm])

lemma coinduced_tate_minus_one (A : Rep.{u} R G) :
    IsZero (tateCohomology (coinduced A) (-1)) := by
  have he : (minusOneShortComplex (coinduced A)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    exact coinduced_norm_kernel_boundary A
  exact (ShortComplex.exact_iff_isZero_homology _).mp
    (ShortComplex.exact_of_iso (minusOneShortComplexIso (coinduced A)).symm he)

/-- Coinduction from the trivial subgroup is acyclic for actual Tate cohomology in every degree. -/
lemma coinduced_tate_isZero (A : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology (coinduced A) n) := by
  rcases n with n | n
  · rcases n with _ | n
    · exact coinduced_tate_zero A
    · exact coinduced_tate_pos A n
  · rcases n with _ | n
    · exact coinduced_tate_minus_one A
    · exact coinduced_tate_neg A n

end Langlands.Tate
