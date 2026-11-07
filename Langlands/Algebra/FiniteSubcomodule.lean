import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType

/-! # Finitely generated subcomodules of flat coalgebras over noetherian rings -/

open TensorProduct Coalgebra

namespace Langlands.Algebra.FiniteSubcomodule

variable {R : Type*} {C : Type*} [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- A submodule `N` of a coalgebra `C` is a right subcomodule when the
comultiplication maps it into the image of `N ⊗ C` in `C ⊗ C`. -/
def IsRightSubcomodule (N : Submodule R C) : Prop :=
  ∀ x ∈ N, comul x ∈ LinearMap.range (N.subtype.rTensor C)

/-- The preimage under the comultiplication of the image of `N ⊗ C`. -/
def core (N : Submodule R C) : Submodule R C :=
  (LinearMap.range (N.subtype.rTensor C)).comap (comul (R := R) (A := C))

theorem mem_core {N : Submodule R C} {x : C} :
    x ∈ core N ↔ comul x ∈ LinearMap.range (N.subtype.rTensor C) :=
  Iff.rfl

/-- The core of `N` is contained in `N`, by the counit law. -/
theorem core_le (N : Submodule R C) : core N ≤ N := by
  intro y hy
  obtain ⟨z, hz⟩ := hy
  have h1 : (counit (R := R) (A := C)).lTensor C (comul y) = y ⊗ₜ[R] (1 : R) :=
    lTensor_counit_comul y
  have h2 : (counit (R := R) (A := C)).lTensor C (N.subtype.rTensor C z) =
      N.subtype.rTensor R ((counit (R := R) (A := C)).lTensor N z) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← hz] at h1
  rw [h1] at h2
  have h3 := congrArg (TensorProduct.rid R C) h2
  rw [TensorProduct.rid_tmul, one_smul] at h3
  rw [h3]
  induction ((counit (R := R) (A := C)).lTensor N z) with
  | tmul n r => simpa using N.smul_mem r n.2
  | add a b ha hb => simpa using N.add_mem ha hb

/-- The core of `N` is the kernel of comultiplication followed by reduction
modulo `N` in the first factor. -/
theorem core_eq_ker (N : Submodule R C) :
    core N = LinearMap.ker ((N.mkQ.rTensor C) ∘ₗ comul (R := R) (A := C)) := by
  have hex : Function.Exact (N.subtype.rTensor C) (N.mkQ.rTensor C) :=
    rTensor_exact C (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)
  ext x
  simp only [mem_core, LinearMap.mem_ker, LinearMap.comp_apply]
  exact (hex (comul x)).symm

/-- Reduction modulo `N` kills the coassociativity image of `N ⊗ C`. -/
theorem rTensor_mkQ_assoc_symm_lTensor_comul (N : Submodule R C) (z : N ⊗[R] C) :
    ((N.mkQ.rTensor C).rTensor C)
      ((TensorProduct.assoc R C C C).symm
        ((comul (R := R) (A := C)).lTensor C (N.subtype.rTensor C z))) = 0 := by
  induction z with
  | tmul n c =>
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, LinearMap.lTensor_tmul]
    induction (comul (R := R) (A := C) c) with
    | tmul c₁ c₂ =>
      simp [(Submodule.Quotient.mk_eq_zero N).mpr n.2]
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb, add_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

/-- For a flat coalgebra, the core of any submodule is a right subcomodule. -/
theorem isRightSubcomodule_core [Module.Flat R C] (N : Submodule R C) :
    IsRightSubcomodule (core N) := by
  intro y hy
  set φ : C →ₗ[R] (C ⧸ N) ⊗[R] C := (N.mkQ.rTensor C) ∘ₗ comul (R := R) (A := C)
  have hker : core N = LinearMap.ker φ := core_eq_ker N
  have hex : Function.Exact (core N).subtype φ := by
    rw [hker]
    exact LinearMap.exact_subtype_ker_map φ
  have hexT : Function.Exact ((core N).subtype.rTensor C) (φ.rTensor C) :=
    Module.Flat.rTensor_exact C hex
  apply (hexT (comul y)).mp
  obtain ⟨z, hz⟩ := (mem_core.mp hy)
  have hco : (comul (R := R) (A := C)).rTensor C (comul y) =
      (TensorProduct.assoc R C C C).symm ((comul (R := R) (A := C)).lTensor C (comul y)) :=
    (coassoc_symm_apply y).symm
  simp only [φ, LinearMap.rTensor_comp, LinearMap.comp_apply]
  rw [hco, ← hz]
  exact rTensor_mkQ_assoc_symm_lTensor_comul N z

/-- The sum of two right subcomodules is a right subcomodule. -/
theorem IsRightSubcomodule.sup {N N' : Submodule R C} (hN : IsRightSubcomodule N)
    (hN' : IsRightSubcomodule N') : IsRightSubcomodule (N ⊔ N') := by
  have mono : ∀ {P Q : Submodule R C}, P ≤ Q →
      LinearMap.range (P.subtype.rTensor C) ≤ LinearMap.range (Q.subtype.rTensor C) := by
    intro P Q hPQ
    rintro _ ⟨z, rfl⟩
    refine ⟨(Submodule.inclusion hPQ).rTensor C z, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    rfl
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact add_mem (mono le_sup_left (hN a ha)) (mono le_sup_right (hN' b hb))

/-- Serre's local finiteness: over a noetherian ring, every element of a flat
coalgebra lies in a finitely generated right subcomodule. -/
theorem exists_fg_isRightSubcomodule [IsNoetherianRing R] [Module.Flat R C] (x : C) :
    ∃ N : Submodule R C, N.FG ∧ x ∈ N ∧ IsRightSubcomodule N := by
  obtain ⟨N, hNfin, hN⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite
      ({comul (R := R) (A := C) x} : Set (C ⊗[R] C)) (Set.finite_singleton _)
  have hNfg : N.FG := (Module.Finite.iff_fg (N := N)).mp hNfin
  refine ⟨core N, ?_, hN (Set.mem_singleton _), isRightSubcomodule_core N⟩
  have : IsNoetherian R N := isNoetherian_of_fg_of_noetherian N hNfg
  have hfg := (IsNoetherian.noetherian (Submodule.comap N.subtype (core N))).map N.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr (core_le N)] at hfg

/-- A finitely generated flat bialgebra over a noetherian ring has a finitely
generated right subcomodule that generates it as an algebra. -/
theorem exists_fg_isRightSubcomodule_adjoin_eq_top {A : Type*} [CommRing A] [Bialgebra R A]
    [IsNoetherianRing R] [Module.Flat R A] [Algebra.FiniteType R A] :
    ∃ V : Submodule R A, V.FG ∧ IsRightSubcomodule V ∧ Algebra.adjoin R (V : Set A) = ⊤ := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  classical
  have key : ∀ t : Finset A, ∃ V : Submodule R A, V.FG ∧ (t : Set A) ⊆ V ∧
      IsRightSubcomodule V := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨⊥, Submodule.fg_bot, by simp, fun x hx => by
        rw [(Submodule.mem_bot R).mp hx, map_zero]; exact zero_mem _⟩
    | insert a t _ ih =>
      obtain ⟨V, hV, htV, hVc⟩ := ih
      obtain ⟨W, hW, haW, hWc⟩ := exists_fg_isRightSubcomodule (R := R) a
      refine ⟨V ⊔ W, hV.sup hW, ?_, hVc.sup hWc⟩
      rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨(le_sup_right : W ≤ V ⊔ W) haW, htV.trans (le_sup_left : V ≤ V ⊔ W)⟩
  obtain ⟨V, hV, hsV, hVc⟩ := key s
  refine ⟨V, hV, hVc, eq_top_iff.mpr ?_⟩
  rw [← hs]
  exact Algebra.adjoin_mono hsV

end Langlands.Algebra.FiniteSubcomodule
