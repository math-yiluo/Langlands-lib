import Langlands.GroupScheme.IntegralLinearEmbedding.Comodule

/-! # Finite subcomodules of a flat coalgebra over a noetherian ring -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.IntegralLinearEmbedding

variable {R : Type*} [CommRing R] {B : Type*} [AddCommGroup B] [Module R B]
  [Coalgebra R B]

/-- The largest right subcomodule contained in `W`, defined by its quotient coaction. -/
def subcomoduleCore (W : Submodule R B) : Submodule R B :=
  LinearMap.ker (W.mkQ.rTensor B ∘ₗ comul)

theorem mem_subcomoduleCore {W : Submodule R B} {b : B} :
    b ∈ subcomoduleCore W ↔ W.mkQ.rTensor B (comul b) = 0 := Iff.rfl

theorem mem_subcomoduleCore_iff {W : Submodule R B} {b : B} :
    b ∈ subcomoduleCore W ↔ comul (R := R) b ∈ LinearMap.range (W.subtype.rTensor B) := by
  exact (rTensor_exact B (LinearMap.exact_subtype_mkQ W)
    (Submodule.mkQ_surjective W) (comul b))

theorem subcomoduleCore_le (W : Submodule R B) : subcomoduleCore W ≤ W := by
  intro b hb
  have hnat : W.mkQ ∘ₗ (TensorProduct.rid R B).toLinearMap ∘ₗ (counit (R := R)).lTensor B =
      (TensorProduct.rid R (B ⧸ W)).toLinearMap ∘ₗ (counit (R := R)).lTensor (B ⧸ W) ∘ₗ
        W.mkQ.rTensor B := by
    ext x y
    simp
  have h := LinearMap.congr_fun hnat (comul (R := R) b)
  have hb' := mem_subcomoduleCore.mp hb
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, lTensor_counit_comul,
    TensorProduct.rid_tmul, one_smul, hb', map_zero] at h
  exact (Submodule.Quotient.mk_eq_zero W).mp h

theorem comul_mem_range_subcomoduleCore [Module.Flat R B]
    (W : Submodule R B) {b : B} (hb : b ∈ subcomoduleCore W) :
    comul (R := R) b ∈ LinearMap.range ((subcomoduleCore W).subtype.rTensor B) := by
  let F : B →ₗ[R] (B ⧸ W) ⊗[R] B := W.mkQ.rTensor B ∘ₗ comul
  have hexact := Module.Flat.rTensor_exact B (LinearMap.exact_subtype_ker_map F)
  apply (hexact (comul b)).mp
  have hnat : (W.mkQ.rTensor B).rTensor B ∘ₗ
        (TensorProduct.assoc R B B B).symm.toLinearMap =
      (TensorProduct.assoc R (B ⧸ W) B B).symm.toLinearMap ∘ₗ W.mkQ.rTensor (B ⊗[R] B) := by
    apply TensorProduct.ext_threefold'
    intro x y z
    simp
  have hcomm : W.mkQ.rTensor (B ⊗[R] B) ∘ₗ (comul (R := R)).lTensor B =
      (comul (R := R)).lTensor (B ⧸ W) ∘ₗ W.mkQ.rTensor B := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  change F.rTensor B (comul b) = 0
  calc
    F.rTensor B (comul b) = (W.mkQ.rTensor B).rTensor B
        ((comul (R := R)).rTensor B (comul b)) := by
      simp only [F, LinearMap.rTensor_comp, LinearMap.comp_apply]
    _ = (W.mkQ.rTensor B).rTensor B
        ((TensorProduct.assoc R B B B).symm ((comul (R := R)).lTensor B (comul b))) := by
      rw [coassoc_symm_apply]
    _ = (TensorProduct.assoc R (B ⧸ W) B B).symm
        (W.mkQ.rTensor (B ⊗[R] B) ((comul (R := R)).lTensor B (comul b))) :=
      LinearMap.congr_fun hnat _
    _ = (TensorProduct.assoc R (B ⧸ W) B B).symm
        ((comul (R := R)).lTensor (B ⧸ W) (W.mkQ.rTensor B (comul b))) :=
      congrArg _ (LinearMap.congr_fun hcomm _)
    _ = 0 := by rw [mem_subcomoduleCore.mp hb, map_zero, map_zero]

/-- Every right subcomodule contained in `W` is contained in its core. -/
theorem le_subcomoduleCore {V W : Submodule R B} (hVW : V ≤ W)
    (hV : ∀ b ∈ V, comul (R := R) b ∈ LinearMap.range (V.subtype.rTensor B)) :
    V ≤ subcomoduleCore W := by
  intro b hb
  apply mem_subcomoduleCore_iff.mpr
  obtain ⟨t, ht⟩ := hV b hb
  refine ⟨(Submodule.inclusion hVW).rTensor B t, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  exact ht

private theorem exists_fg_comul_container (S : Finset B) :
    ∃ W : Submodule R B, W.FG ∧ ∀ b ∈ S,
      comul (R := R) b ∈ LinearMap.range (W.subtype.rTensor B) := by
  classical
  choose T hT using fun b : B => TensorProduct.exists_finset (R := R) (comul (R := R) b)
  let U (b : B) : Submodule R B := Submodule.span R ((T b).image Prod.fst : Set B)
  let W : Submodule R B := S.sup U
  have hmem : ∀ b ∈ S, ∀ x ∈ T b, x.1 ∈ W := by
    intro b hb x hx
    exact Finset.le_sup (f := U) hb (Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)))
  refine ⟨W, Submodule.fg_finset_sup S U (fun b _ =>
    Submodule.fg_span (Finset.finite_toSet _)), fun b hb => ?_⟩
  refine ⟨∑ x ∈ (T b).attach, (⟨x.1.1, hmem b hb x.1 x.2⟩ : W) ⊗ₜ[R] x.1.2, ?_⟩
  rw [hT b, map_sum, ← Finset.sum_attach (T b)]
  rfl

private theorem exists_fg_subcomodule [IsNoetherianRing R] [Module.Flat R B] (S : Finset B) :
    ∃ W : Submodule R B, W.FG ∧ (S : Set B) ⊆ W ∧
      ∀ b ∈ W, comul (R := R) b ∈ LinearMap.range (W.subtype.rTensor B) := by
  obtain ⟨W, hW, hS⟩ := exists_fg_comul_container (R := R) S
  exact ⟨subcomoduleCore W, Submodule.FG.of_le hW (subcomoduleCore_le W),
    fun b hb => mem_subcomoduleCore_iff.mpr (hS b hb),
    fun b hb => comul_mem_range_subcomoduleCore W hb⟩

/-- Choose a finite right subcomodule containing the given finite subset. -/
def finiteSubcomodule [IsNoetherianRing R] [Module.Flat R B] (S : Finset B) : Submodule R B :=
  (exists_fg_subcomodule (R := R) S).choose

theorem finiteSubcomodule_spec [IsNoetherianRing R] [Module.Flat R B] (S : Finset B) :
    (finiteSubcomodule (R := R) S).FG ∧ (S : Set B) ⊆ finiteSubcomodule (R := R) S ∧
      ∀ b ∈ finiteSubcomodule (R := R) S,
        comul (R := R) b ∈ LinearMap.range ((finiteSubcomodule (R := R) S).subtype.rTensor B) :=
  (exists_fg_subcomodule (R := R) S).choose_spec

/-- Matrix coefficients over a PID need only flatness of the coalgebra. -/
theorem exists_matrix_coefficients_of_flat [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Flat R B] (S : Finset B) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) B),
      (∀ i j, comul (R := R) (M i j) = ∑ l, M i l ⊗ₜ[R] M l j) ∧
      (∀ i j, counit (R := R) (M i j) = (1 : Matrix (Fin N) (Fin N) R) i j) ∧
      (S : Set B) ⊆ Submodule.span R (Set.range fun p : Fin N × Fin N => M p.1 p.2) := by
  classical
  let Λ := finiteSubcomodule (R := R) S
  obtain ⟨hfg, hS, hΛ⟩ := finiteSubcomodule_spec (R := R) S
  have : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  have : IsTorsionFree R Λ :=
    Function.Injective.moduleIsTorsionFree Λ.subtype Subtype.val_injective (fun _ _ => rfl)
  obtain ⟨N, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := Λ)
  refine ⟨N, coefficientMatrix e hΛ, comul_coefficientMatrix e hΛ,
    counit_coefficientMatrix e hΛ, fun a ha => ?_⟩
  have hspan : Λ ≤ Submodule.span R
      (Set.range fun p : Fin N × Fin N => coefficientMatrix e hΛ p.1 p.2) := by
    intro b hb
    have h := congrArg Subtype.val (e.sum_repr ⟨b, hb⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (basis_mem_span_coefficientMatrix e hΛ j)
  exact hspan (hS ha)

end Langlands.GroupScheme.IntegralLinearEmbedding
