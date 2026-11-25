/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension

/-!
# Cohomological amplitude of right derived functors of finite cohomological dimension

Let `F : C ⥤ D` be a left exact additive functor of finite cohomological dimension `d`
(`R^q F = 0` for `q > d`). Then the unbounded right derived functor `RF` sends `D^{≤ n}` into
`D^{≤ n + d}` (`CategoryTheory.Functor.isLE_rightDerivedFunctor_obj`), with no boundedness
assumption on the objects. The proof is the dimension shifting argument of
`HomologicalComplex.Acyclic.map_of_rightAcyclic_of_forall_isZero`, run only in the
degrees where the complex is exact
(`HomologicalComplex.exactAt_map_of_rightAcyclic_of_isZero_rightDerived`).

A left adjoint `F` between triangulated categories with t-structures sending `D^{≤ n}` into
`D^{≤ n + N}` has a right adjoint sending `D^{≥ n}` into `D^{≥ n - N}`
(`CategoryTheory.Adjunction.isGE_obj_of_isLE`).
-/

@[expose] public section

universe w

open CategoryTheory Limits Pretriangulated

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

/-- A left exact additive functor `F : C ⥤ D` of finite cohomological dimension `d` sends a
cochain complex `K` of `F`-acyclic objects which is exact in degrees `> n` to a complex which is
exact in degrees `> n + d`. The short exact sequences `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Zᵏ⁺¹ ⟶ 0` of cycles for
`k ≥ n` give injections `R^q F(Zᵏ⁺¹) ⟶ R^{q+1} F(Zᵏ)` for `q ≥ 1`, so the cycles `Zᵏ` are
`F`-acyclic for `k ≥ n + d`, and `F` keeps the corresponding short exact sequences exact. -/
theorem exactAt_map_of_rightAcyclic_of_isZero_rightDerived {K : CochainComplex C ℤ}
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (d : ℕ)
    (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (hK' : ∀ n, F.rightAcyclic (K.X n)) (n : ℤ) (hK : ∀ k, n < k → K.ExactAt k)
    (m : ℤ) (hm : n + d < m) :
    ((F.mapHomologicalComplex _).obj K).ExactAt m := by
  have hS (k : ℤ) (hk : n ≤ k) := (hK (k + 1) (by lia)).shortExact_cyclesShortComplex
    (i := k) (by simp)
  -- dimension shifting: `R^{q+1} F(Zᵏ) = 0` as soon as `n + j ≤ k` and `d ≤ q + j`
  have hZ' (j : ℕ) : ∀ (k : ℤ) (q : ℕ), n + j ≤ k → d ≤ q + j →
      IsZero ((F.rightDerived (q + 1)).obj (K.cycles k)) := by
    induction j with
    | zero => exact fun k q _ hq ↦ hF _ _ (by lia)
    | succ j ih =>
      intro k q hk hq
      obtain ⟨δ, w₁, w₂, h, -⟩ := (hS (k - 1) (by lia)).exists_rightDerived_δ_exact F (q + 1)
      have : Mono δ := h.mono_g ((hK' (k - 1) q).eq_of_src _ _)
      have h' : IsZero ((F.rightDerived (q + 1)).obj (K.cycles (k - 1 + 1))) :=
        IsZero.of_mono δ (ih (k - 1) (q + 1) (by lia) (by lia))
      rwa [sub_add_cancel] at h'
  have hZ (k : ℤ) (hk : n + d ≤ k) : F.rightAcyclic (K.cycles k) := fun q ↦
    hZ' d k q hk (by lia)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 2) (by simp) (by simp; lia)]
  let T := ShortComplex.mk (F.map (K.iCycles (k + 1))) (F.map (K.d (k + 1) (k + 2)))
    (by rw [← F.map_comp, iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (k + 1) (k + 2) (by simp; lia))
  have : Epi (F.map (K.toCycles k (k + 1))) :=
    ((hS k (by lia)).map_of_rightAcyclic (hZ k (by lia))).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' k (k + 1) (k + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles k (k + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

end HomologicalComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- **Cohomological amplitude of a right derived functor of finite cohomological dimension.**
Let `C` be a Grothendieck abelian category and `F : C ⥤ D` a left exact additive functor with
`R^q F = 0` for `q > d`. Then the unbounded right derived functor `RF` sends objects `≤ n` of
`D(C)` to objects `≤ n + d` of `D(D)`, with no boundedness below.

An object `K ≤ n` is represented by a K-injective complex `I` with injective components, which is
exact in degrees `> n`; `RF(K) ≅ F(I)`, which is exact in degrees `> n + d`
(`HomologicalComplex.exactAt_map_of_rightAcyclic_of_isZero_rightDerived`). -/
theorem isLE_rightDerivedFunctor_obj [IsGrothendieckAbelian.{w} C] [HasInjectiveResolutions C]
    (d : ℕ) (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (K : DerivedCategory C) (n : ℤ) [K.IsLE n] :
    (F.rightDerivedFunctor.obj K).IsLE (n + d) := by
  let I := (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj (DerivedCategory.Q.objPreimage K)
  have hι : IsIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{w}
      C).app (DerivedCategory.Q.objPreimage K))) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C _) _
      ((CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C _).2)
  let e : DerivedCategory.Q.obj I ≅ K := (asIso (DerivedCategory.Q.map
    ((CochainComplex.toKInjectiveResolution.{w} C).app
      (DerivedCategory.Q.objPreimage K)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso _
  have hI : I.IsLE n := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso e.symm n
  have hinj (k : ℤ) : Injective (I.X k) :=
    CochainComplex.injective_kInjectiveResolutionFunctor_obj_X.{w} _ k
  have hu : IsIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)) :=
    F.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic d hF I
      fun k ↦ have := hinj k; rightAcyclic_of_injective _
  let e' : DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj I) ≅
      F.rightDerivedFunctor.obj K :=
    (DerivedCategory.quotientCompQhIso D).symm.app _ ≪≫
      asIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)) ≪≫
        F.rightDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso C).app I ≪≫ e)
  have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj I)).IsLE (n + d) := by
    rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff]
    exact fun m hm ↦ HomologicalComplex.exactAt_map_of_rightAcyclic_of_isZero_rightDerived F d hF
      (fun k ↦ have := hinj k; rightAcyclic_of_injective _) n
      (fun k hk ↦ I.exactAt_of_isLE n k hk) m hm
  exact DerivedCategory.TStructure.t.isLE_of_iso e' (n + d)

end Functor

/-- Let `F ⊣ G` be an adjunction between categories with t-structures `t` and `t'`. If `F`
sends objects `≤ n` to objects `≤ n + N` for every `n`, then `G` sends objects `≥ n` to objects
`≥ n - N`: for `X ≤ n - N - 1`, `Hom(X, G Y) = Hom(F X, Y) = 0` as `F X ≤ n - 1`. -/
lemma Adjunction.isGE_obj_of_isLE {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (t : Triangulated.TStructure C) (t' : Triangulated.TStructure D) (N : ℤ)
    (hF : ∀ (X : C) (n : ℤ), t.IsLE X n → t'.IsLE (F.obj X) (n + N))
    (Y : D) (n : ℤ) [t'.IsGE Y n] : t.IsGE (G.obj Y) (n - N) := by
  rw [t.isGE_iff_orthogonal (n - N - 1) (n - N) (by lia)]
  intro X f hX
  have := adj.isRightAdjoint
  have := hF X _ hX
  have h0 : (adj.homEquiv X Y).symm f = 0 := t'.zero _ (n - N - 1 + N) n (by lia)
  rw [← (adj.homEquiv X Y).apply_symm_apply f, h0, Adjunction.homEquiv_apply,
    Functor.map_zero, comp_zero]

end CategoryTheory
