/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.Algebra.Homology.SixFunctors.DegreeZeroComplexReplacement
import WeilConjectures.CategoryTheory.Right.RightDerivedFromAdaptedComplexes
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension

/-!
# Finite cohomological dimension and unbounded right derived functors

Source: Stacks Project, `literature/stacks-project/derived.tex`, Tag 07K7,
lemma-unbounded-right-derived (1) and (4)(c) (blueprint: lem-sf-finite-cd-derived-upper-bound).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Tag 07K7: the least eventual-vanishing degree satisfies the hypotheses of 07K6. -/
private theorem exists_rightAcyclic_replacement
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (D : ℕ)
    (hF : ∀ (X : A) (q : ℕ), D < q → IsZero ((F.rightDerived q).obj X))
    (K : CochainComplex A ℤ) :
    ∃ (L : CochainComplex A ℤ) (f : K ⟶ L), QuasiIso f ∧
      ∀ r : ℤ, F.rightAcyclic (L.X r) := by
  classical
  let P (X : A) (n : ℕ) := ∀ q : ℕ, n < q → IsZero ((F.rightDerived q).obj X)
  have hex (X : A) : ∃ n, P X n := ⟨D, hF X⟩
  let d (X : A) := Nat.find (hex X)
  have hd (X : A) : P X (d X) := Nat.find_spec (hex X)
  have hle (X : A) (n : ℕ) (h : P X n) : d X ≤ n := Nat.find_min' (hex X) h
  have hbound (X : A) : d X ≤ D := hle X D (hF X)
  have hembed (X : A) : ∃ (I : A) (j : X ⟶ I), Mono j ∧ d I = 0 := by
    refine ⟨Injective.under X, Injective.ι X, inferInstance, ?_⟩
    apply Nat.eq_zero_of_le_zero
    apply hle
    intro q hq
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact F.isZero_rightDerived_obj_injective_succ q _
  have hsum (X Y : A) : d (biprod X Y) ≤ max (d X) (d Y) := by
    apply hle
    intro q hq
    have := preservesBinaryBiproducts_of_preservesBiproducts (F.rightDerived q)
    exact ((biprod_isZero_iff _ _).2 ⟨hd X q (by omega), hd Y q (by omega)⟩).of_iso
      ((F.rightDerived q).mapBiprod X Y)
  have hshort (S : ShortComplex A) (hS : S.ShortExact) :
      d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂) := by
    apply hle
    intro q hq
    obtain ⟨δ, w₁, w₂, h, _⟩ := hS.exists_rightDerived_δ_exact F q
    exact h.isZero_X₂_iff.mpr
      ⟨(hd S.X₂ q (by omega)).eq_of_src _ _,
        (hd S.X₁ (q + 1) (by omega)).eq_of_tgt _ _⟩
  obtain ⟨L, f, hf, hL⟩ :=
    CochainComplex.exists_quasiIso_degree_zero_of_bounded_degree
      A d D hbound hembed hsum hshort K
  refine ⟨L, f, hf, fun r q ↦ ?_⟩
  exact hd (L.X r) (q + 1) (by rw [hL r]; omega)

/-- Finite dimension shifting of cycles above the last nonzero cohomology degree. -/
private theorem map_rightAcyclic_upper_bound
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (D : ℕ)
    (hF : ∀ (X : A) (q : ℕ), D < q → IsZero ((F.rightDerived q).obj X))
    (K : CochainComplex A ℤ) (hK : ∀ n, F.rightAcyclic (K.X n))
    (t : ℤ) (ht : ∀ i, t < i → K.ExactAt i) :
    ∀ i, t + (D : ℤ) < i → ((F.mapHomologicalComplex _).obj K).ExactAt i := by
  have hS (n : ℤ) (hn : t ≤ n) :=
    (ht (n + 1) (by omega)).shortExact_cyclesShortComplex (i := n) (by simp)
  have hZ' (k : ℕ) : ∀ (n : ℤ) (q : ℕ), t + (k : ℤ) ≤ n → D ≤ q + k →
      IsZero ((F.rightDerived (q + 1)).obj (K.cycles n)) := by
    induction k with
    | zero => exact fun n q _ hq ↦ hF _ _ (by omega)
    | succ k ih =>
      intro n q hn hq
      obtain ⟨δ, w₁, w₂, h, _⟩ :=
        (hS (n - 1) (by omega)).exists_rightDerived_δ_exact F (q + 1)
      have : Mono δ := h.mono_g ((hK (n - 1) q).eq_of_src _ _)
      have h' : IsZero ((F.rightDerived (q + 1)).obj (K.cycles (n - 1 + 1))) :=
        IsZero.of_mono δ (ih (n - 1) (q + 1) (by omega) (by omega))
      simpa only [sub_add_cancel] using h'
  have hZ (n : ℤ) (hn : t + (D : ℤ) ≤ n) : F.rightAcyclic (K.cycles n) :=
    fun q ↦ hZ' D n q hn (by omega)
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; omega)]
  let T := ShortComplex.mk (F.map (K.iCycles (n + 1))) (F.map (K.d (n + 1) (n + 2)))
    (by rw [← F.map_comp, HomologicalComplex.iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp; omega))
  have : Epi (F.map (K.toCycles n (n + 1))) :=
    ((hS n (by omega)).map_of_rightAcyclic (hZ n (by omega))).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

/-- Fully faithful precomposition makes a factorization isomorphism a Kan extension. -/
private theorem isLeftKanExtension_of_full_whiskering
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (G : D ⥤ E)
    [((Functor.whiskeringLeft C D E).obj L).Full]
    [((Functor.whiskeringLeft C D E).obj L).Faithful]
    {F : C ⥤ E} (e : F ≅ L ⋙ G) : G.IsLeftKanExtension e.hom := by
  let W := (Functor.whiskeringLeft C D E).obj L
  refine ⟨⟨IsInitial.ofUniqueHom
    (fun Y ↦ StructuredArrow.homMk (W.preimage (e.inv ≫ Y.hom)) ?_) ?_⟩⟩
  · change e.hom ≫ W.map (W.preimage (e.inv ≫ Y.hom)) = Y.hom
    rw [W.map_preimage]
    simp
  · intro Y m
    apply StructuredArrow.hom_ext
    apply W.map_injective
    change W.map m.right = W.map (W.preimage (e.inv ≫ Y.hom))
    rw [W.map_preimage]
    have h := m.w
    change e.hom ≫ W.map m.right = Y.hom at h
    rw [← h]
    simp

/-- (blueprint: lem-sf-finite-cd-derived-upper-bound)
Finite cohomological dimension gives an unbounded total right derived functor and
raises an upper cohomological bound by at most the dimension.  This is the statement of
Stacks Project Tag 07K7, parts (1) and (4)(c), with the unbounded cochain derived
categories represented by Mathlib's `DerivedCategory` and the total derived functor
characterized by `Functor.IsRightDerivedFunctor`.

Proof:
1. Set `d(X) = max ({0} ∪ {q > 0 | R^q F(X) ≠ 0})`, which is at most `N`.
   Injectives have degree zero by `lem-weil-pbc-derived-functor-injective-vanishing`,
   so enough injectives gives degree-zero embeddings. For a short exact sequence
   `0 → X → Y → Z → 0`, `lem-weil-pbc-derived-functor-long-exact` gives
   `d(Z) ≤ max (d(X) - 1) (d(Y))`, with truncated subtraction. The split biproduct
   sequence likewise gives `d(X ⊕ Y) ≤ max (d(X)) (d(Y))`.
2. Apply `lem-sf-degree-zero-complex-replacement` (Tag 07K6) with this degree
   function and bound `N`. Every unbounded complex has a quasi-isomorphism into
   a complex of right `F`-acyclic objects. Denote this class of complexes by `I`.
3. Specialize `lem-kun-pointwise-finite-cd-exact-complex` to the singleton family
   consisting of the identity of `B`, with bound `N`. The identity preserves monos
   and detects zero objects, so `F` takes every exact complex in `I` to an exact
   complex. No Grothendieck or boundedness hypothesis is needed.
4. A quasi-isomorphism between complexes in `I` has exact cone by
   `lem-pur-quasi-iso-cone-acyclic`. Its terms are biproducts of right acyclic
   objects and are right acyclic by the long exact sequence. Step 3 makes its image
   exact. Additivity identifies the image of the cone differential matrix with
   the cone differential of the image map, including the minus sign. The cone
   criterion in `B` then says that the image map is a quasi-isomorphism.
5. Additivity carries cochain homotopies to homotopies, commutes with the signed
   shift, and preserves cone triangles. Thus termwise `F`, followed by localization
   in `B`, defines an exact functor on the homotopy category, using
   `lem-pur-homotopy-category-triangulated`. Steps 2 and 4 verify the hypotheses of
   `lem-sf-right-derived-from-adapted-complexes` (Tag 06XN). It supplies `RF` and
   its universal comparison, and identifies `RF(Q(L))` with `Q(F(L))` for `L ∈ I`.
   Equivalently this is the displayed right derived functor relative to the
   localization from cochain complexes.
6. Represent `E` by `L ∈ I`. Write `Z^r = ker(d_L^r)`. For `r ≥ t` the vanishing
   of `H^(r+1)(L)` gives `0 → Z^r → L^r → Z^(r+1) → 0`. The long exact sequence
   and right acyclicity of `L^r` give `R^p F(Z^(r+1)) ≅ R^(p+1) F(Z^r)` for
   `p ≥ 1`. Left exactness identifies the cycles of `F(L)` with `F(Z^i)`;
   `R^0 F ≅ F` from `lemma-acyclic-resolutions` identifies its degree `i > t`
   cohomology with `R^1 F(Z^(i-1))`. For `i > t + N`, iterate the connecting
   isomorphisms `N` times to identify this with `R^(N+1) F(Z^(i-N-1)) = 0`.
   Every sequence used has index at least `t`. If `N = 0`, the given vanishing
   of `R^1 F` already suffices. Step 5 transfers the bound to `RF(E)`.
-/
theorem finiteCDDerivedUpperBound
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (N : ℤ)
    (hN0 : 0 ≤ N)
    (hN : ∀ (q : ℕ), N < (q : ℤ) → ∀ (X : A),
      IsZero ((F.rightDerived q).obj X)) :
    ∃ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (α : (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)) ⟶
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙ RF),
      RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
        ∀ (t : ℤ) (E : DerivedCategory A),
          (∀ (i : ℤ), t < i →
            IsZero ((DerivedCategory.homologyFunctor A i).obj E)) →
          ∀ (i : ℤ), t + N < i →
            IsZero ((DerivedCategory.homologyFunctor B i).obj (RF.obj E)) := by
  classical
  let D := N.toNat
  have hDN : (D : ℤ) = N := Int.toNat_of_nonneg hN0
  have hF (X : A) (q : ℕ) (hq : D < q) : IsZero ((F.rightDerived q).obj X) :=
    hN q (by omega) X
  let qA := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let G := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh (C := B))
  let I : Set (HomotopyCategory A (ComplexShape.up ℤ)) :=
    {K | ∀ n, F.rightAcyclic (K.as.X n)}
  have hrep (K : HomotopyCategory A (ComplexShape.up ℤ)) :
      ∃ (L : HomotopyCategory A (ComplexShape.up ℤ)) (f : K ⟶ L),
        L ∈ I ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) f := by
    obtain ⟨L, f, hf, hL⟩ := exists_rightAcyclic_replacement F D hF K.as
    exact ⟨qA.obj L, qA.map f, hL,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf⟩
  have hinv (K L : HomotopyCategory A (ComplexShape.up ℤ))
      (hK : K ∈ I) (hL : L ∈ I) (s : K ⟶ L)
      (hs : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s) : IsIso (G.map s) := by
    let f : K.as ⟶ L.as := qA.preimage s
    have hf : qA.map f = s := qA.map_preimage s
    rw [← hf] at hs ⊢
    have : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mp hs
    have := F.quasiIso_map_of_rightAcyclic_of_isZero_rightDerived f D hF hK hL
    dsimp only [G, Functor.comp_map]
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance))
  obtain ⟨RF, αh, hRF, hα⟩ :=
    Functor.exists_rightDerivedFunctor_of_adapted_complexes G I hrep hinv
  let e : qA ⋙ G ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let α := e.inv ≫ Functor.whiskerLeft qA αh ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom RF
  have hkan : G.IsLeftKanExtension e.inv :=
    isLeftKanExtension_of_full_whiskering qA G e.symm
  have : RF.IsLeftKanExtension αh := hRF.isLeftKanExtension
  have hαRF : RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (.up ℤ)) := by
    constructor
    exact (Functor.isLeftKanExtension_iff_postcompose e.inv
      DerivedCategory.Q (DerivedCategory.quotientCompQhIso A) αh α (by rfl)).mp inferInstance
  refine ⟨RF, α, hαRF, ?_⟩
  intro t E hE i hi
  obtain ⟨L, f, hf, hL⟩ := exists_rightAcyclic_replacement F D hF
    (DerivedCategory.Q.objPreimage E)
  have : QuasiIso f := hf
  let eEL : E ≅ DerivedCategory.Q.obj L :=
    (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫ asIso (DerivedCategory.Q.map f)
  have hLex (j : ℤ) (hj : t < j) : L.ExactAt j := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hE j hj).of_iso
      (((DerivedCategory.homologyFunctorFactors A j).app L).symm ≪≫
        (DerivedCategory.homologyFunctor A j).mapIso eEL.symm)
  have hFL := map_rightAcyclic_upper_bound F D hF L hL t hLex i (by omega)
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hFL
  have : IsIso (αh.app (qA.obj L)) := hα _ hL
  have : IsIso (α.app L) := by
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact hFL.of_iso
    ((DerivedCategory.homologyFunctor B i).mapIso
      (RF.mapIso eEL ≪≫ (asIso (α.app L)).symm) ≪≫
      (DerivedCategory.homologyFunctorFactors B i).app _)

end CategoryTheory
