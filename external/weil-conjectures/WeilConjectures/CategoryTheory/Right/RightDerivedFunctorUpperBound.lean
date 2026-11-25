/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Upper bounds for right derived functors of finite cohomological dimension

Source: Stacks Project, Tag 07K7, lemma-unbounded-right-derived, part (4)(c).
-/

@[expose] public section

set_option autoImplicit false

universe w v u v' u'

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [HasInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

private theorem isLE_map_of_rightAcyclic_of_dimension
    (d : ℕ) (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsLE b]
    (hK : ∀ n, F.rightAcyclic (K.X n)) :
    CochainComplex.IsLE ((F.mapHomologicalComplex (.up ℤ)).obj K) (b + d) := by
  have hZ' (k : ℕ) : ∀ (n : ℤ) (q : ℕ), b + k ≤ n → d ≤ q + k →
      IsZero ((F.rightDerived (q + 1)).obj (K.cycles n)) := by
    induction k with
    | zero => exact fun n q _ hq ↦ hF _ _ (by omega)
    | succ k ih =>
      intro n q hn hq
      have hS := (K.exactAt_of_isLE b n (by omega)).shortExact_cyclesShortComplex
        (i := n - 1) (by simp)
      obtain ⟨δ, _, _, h, _⟩ := hS.exists_rightDerived_δ_exact F (q + 1)
      have : Mono δ := h.mono_g ((hK (n - 1) q).eq_of_src _ _)
      have hz : IsZero ((F.rightDerived (q + 1)).obj (K.cycles n)) :=
        IsZero.of_mono δ (ih (n - 1) (q + 1) (by omega) (by omega))
      exact hz
  have hZ (n : ℤ) (hn : b + d ≤ n) : F.rightAcyclic (K.cycles n) :=
    fun q ↦ hZ' d n q hn (by omega)
  rw [CochainComplex.isLE_iff]
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; omega)]
  let T := ShortComplex.mk (F.map (K.iCycles (n + 1))) (F.map (K.d (n + 1) (n + 2)))
    (by rw [← F.map_comp, HomologicalComplex.iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp; omega))
  have hS := (K.exactAt_of_isLE b (n + 1) (by omega)).shortExact_cyclesShortComplex
    (i := n) (by simp)
  have : Epi (F.map (K.toCycles n (n + 1))) :=
    (hS.map_of_rightAcyclic (hZ n (by omega))).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

variable [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C] [IsGrothendieckAbelian.{w} C]

/-- A uniform classical cohomological-dimension bound gives the same upper amplitude
on the unbounded derived category.

Source: Stacks Project, Tag 07K7, lemma-unbounded-right-derived, part (4)(c).
(blueprint: lem-etale-derived-functor-upper-amplitude)

Proof: represent L by a K-injective complex I with injective components. Its cycles in
degrees n above b satisfy the short exact sequences of cycles. Repeatedly inject
R^(q+1) F(Z^n I) into R^(q+2) F(Z^(n-1) I); after d steps the latter vanishes by hF,
provided n ≥ b+d. Thus these cycles are F-acyclic, so F preserves the corresponding
short exact sequences of cycles. This makes F(I) exact above b+d. The comparison
RF(QI) ≅ Q(FI), followed by the original representing isomorphism, gives the result.
-/
theorem isLE_rightDerivedFunctor_obj_of_dimension
    (d : ℕ) (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (L : DerivedCategory C) (b : ℤ) (hL : DerivedCategory.TStructure.t.IsLE L b) :
    DerivedCategory.TStructure.t.IsLE (F.rightDerivedFunctor.obj L) (b + d) := by
  let K := DerivedCategory.Q.objPreimage L
  let I := (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K
  let ι : K ⟶ I := (CochainComplex.toKInjectiveResolution.{w} C).app K
  have : QuasiIso ι := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C K).2
  have : IsIso (DerivedCategory.Q.map ι) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C _) _
      ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)
  let e : DerivedCategory.Q.obj I ≅ L :=
    (asIso (DerivedCategory.Q.map ι)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L
  have : DerivedCategory.TStructure.t.IsLE (DerivedCategory.Q.obj I) b :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have : I.IsLE b := (DerivedCategory.isLE_Q_obj_iff I b).1 inferInstance
  have : CochainComplex.IsLE ((F.mapHomologicalComplex (.up ℤ)).obj I) (b + d) :=
    isLE_map_of_rightAcyclic_of_dimension F d hF I b fun n ↦
      have : Injective (I.X n) :=
        CochainComplex.injective_kInjectiveResolutionFunctor_obj_X.{w} K n
      rightAcyclic_of_injective _
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((F.rightDerivedFunctorObjQIso I).symm ≪≫ F.rightDerivedFunctor.mapIso e) (b + d)

end CategoryTheory.Functor
