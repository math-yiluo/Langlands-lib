/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.FieldTheory.InseparableDegreeDrop
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.FinTrdeg

/-!
# Making a finitely generated field extension separably generated

Source: Stacks Project, Algebra, Lemma Tag 04KM (lemma-make-separably-generated)
(blueprint: lem-weil-pbc-make-separably-generated).

## Main statements

* `FieldExtension.exists_finitePurelyInseparable_separablyGenerated`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace FieldExtension

/-- A finitely generated field extension becomes separably generated after finite purely
inseparable extensions of the base and the extension.
Source: Stacks Project, Algebra, Lemma Tag 04KM (lemma-make-separably-generated)
(blueprint: lem-weil-pbc-make-separably-generated).

Proof, following the ten steps of the node and Stacks Tag 04KM:

1. In characteristic zero, `lem-weil-pbc-char-zero-field-extension-separable` makes the
   finitely generated extension separably generated. Use the identity extensions.
2. In characteristic p > 0 choose a finite transcendence basis x using
   `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`. Put E = k(x).
   The generators are algebraic over E, so `lem-weil-pbc-algebraic-generators-finite-extension`
   makes K/E finite. Its relative separable closure K_s gives a separable algebraic
   extension K_s/E and a purely inseparable extension K/K_s by
   `lem-weil-pbc-separable-first-purely-inseparable`. Induct strongly on e = [K : K_s],
   simultaneously for all extensions and finite transcendence bases.
3. If e = 1 then K = K_s, so x is separating. Again use the identity extensions.
4. Otherwise take an element outside K_s, and its least p-power in K_s. This gives
   beta outside K_s with alpha = beta^p in K_s. The minimal polynomial P of alpha
   over E is separable and has distinct roots (`def-pc-separable-polynomial`).
5. In an algebraic closure of K, write each coefficient c_j of P as f_j(x)/g_j(x),
   and set h_j = f_j * g_j^(p-1). Adjoin to k the p-th roots of the finitely many
   coefficients of all h_j, obtaining k_1. Put E_1 = k_1(x_i^(1/p)). Frobenius
   (`def-weil-ring-frobenius`) shows c_j is the p-th power of the polynomial with
   rooted coefficients evaluated at x_i^(1/p), divided by g_j(x).
6. Adjoining finitely many elements whose p-th powers lie in a field is finite
   algebraic and purely inseparable: the elements whose p-th powers lie in that
   field form a subfield. Thus k_1/k is finite purely inseparable, k_1^p lies in k,
   and the compositum L = K E_1 is finite purely inseparable over K.
7. L/k_1 is finitely generated, and `lem-weil-pbc-compositum-degree-bound` makes
   L/E_1 finite. Raising an alleged polynomial relation among x_i^(1/p) to the
   p-th power yields a nonzero relation among x_i over k, a contradiction.
   Consequently x_i^(1/p) is a finite transcendence basis of L/k_1.
8. Let L_s be the relative separable closure of E_1 in L. The minimal polynomial
   over E_1 of an element of K_s divides its separable polynomial over E, so K_s
   lies in L_s. By `lem-weil-pbc-separable-root-pth-power`, since P has distinct
   roots and p-th-power coefficients in E_1, alpha has a p-th root alpha_1 in L_s.
   Injectivity of Frobenius gives beta = alpha_1, hence beta lies in L_s.
9. Put K_1 = K_s(beta). The compositum K L_s equals L, so
   `lem-weil-pbc-compositum-degree-bound` gives [L : L_s] <= [K : K_1]. The tower law
   (`lem-weil-pbc-field-degree-multiplicativity`) and [K_1 : K_s] >= 2 give
   [L : L_s] < e.
10. Apply induction to L/k_1 with its rooted transcendence basis, obtaining L'/L
    and k_2/k_1. Compose the maps and use
    `lem-weil-pbc-finite-purely-inseparable-transitive` to obtain finite purely
    inseparable L'/K and k_2/k. The square commutes and L'/k_2 is separably generated.
    Finite extensions and subfields can be represented in Type (max u v).
-/
theorem exists_finitePurelyInseparable_separablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ (k' : Type (max u v)) (hk' : Field k') (akk' : Algebra k k')
      (K' : Type (max u v)) (hK' : Field K') (aKK' : Algebra K K') (akK' : Algebra k' K'),
      letI := hk'
      letI := akk'
      letI := hK'
      letI := aKK'
      letI := akK'
      Module.Finite k k' ∧ IsPurelyInseparable k k' ∧
      Module.Finite K K' ∧ IsPurelyInseparable K K' ∧
      Algebra.IsSeparablyGenerated k' K' ∧
      (algebraMap k' K').comp (algebraMap k k') =
        (algebraMap K K').comp (algebraMap k K) := by
  classical
  have induction : ∀ n : ℕ, ∀ (l L : Type (max u v))
      [Field l] [Field L] [Algebra l L],
      (⊤ : IntermediateField l L).FG → ∀ s : Finset L,
      IsTranscendenceBasis l ((↑) : s → L) →
      ∀ (_ : Module.Finite (IntermediateField.adjoin l (s : Set L)) L),
      Field.finInsepDegree (IntermediateField.adjoin l (s : Set L)) L = n →
      ∃ (l' : Type (max u v)) (hl' : Field l') (all' : Algebra l l')
        (L' : Type (max u v)) (hL' : Field L') (aLL' : Algebra L L')
        (alL' : Algebra l' L') (al0L' : Algebra l L')
        (htl : IsScalarTower l l' L') (htL : IsScalarTower l L L'),
        Module.Finite l l' ∧ IsPurelyInseparable l l' ∧
        Module.Finite L L' ∧ IsPurelyInseparable L L' ∧
        Algebra.IsSeparablyGenerated l' L' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l L hl hL alL hfgL s hs hfin hn
      by_cases hsep : Field.finInsepDegree (IntermediateField.adjoin l (s : Set L)) L = 1
      · have hseparable : Algebra.IsSeparable (IntermediateField.adjoin l (s : Set L)) L :=
          (isSeparable_iff_finInsepDegree_eq_one _ _).mpr hsep
        exact ⟨l, hl, inferInstance, L, hL, inferInstance, alL, alL,
          inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, inferInstance, (s : Set L), hs, hseparable⟩
      · obtain ⟨l₁, hl₁, all₁, L₁, hL₁, aLL₁, al₁L₁, alL₁, htl₁, htL₁,
          hfinl₁, hpurel₁, hfinL₁, hpureL₁, hfg₁, t, ht, hfint, hdrop⟩ :=
          exists_inseparableDegree_drop l L hfgL s hs hsep
        have hlt : Field.finInsepDegree (IntermediateField.adjoin l₁ (t : Set L₁)) L₁ < n :=
          hdrop.trans_eq hn
        obtain ⟨l₂, hl₂, al₁l₂, L₂, hL₂, aL₁L₂, al₂L₂, al₁L₂, ht₁₂, htL₁₂,
          hfinl₂, hpurel₂, hfinL₂, hpureL₂, hgen⟩ :=
          ih _ hlt l₁ L₁ hfg₁ t ht hfint rfl
        let all₂ : Algebra l l₂ := ((algebraMap l₁ l₂).comp (algebraMap l l₁)).toAlgebra
        let aLL₂ : Algebra L L₂ := ((algebraMap L₁ L₂).comp (algebraMap L L₁)).toAlgebra
        let alL₂ : Algebra l L₂ := ((algebraMap l₁ L₂).comp (algebraMap l l₁)).toAlgebra
        have : IsScalarTower l l₁ l₂ := IsScalarTower.of_algebraMap_eq' rfl
        have : IsScalarTower L L₁ L₂ := IsScalarTower.of_algebraMap_eq' rfl
        have : IsScalarTower l l₁ L₂ := IsScalarTower.of_algebraMap_eq' rfl
        have towerl : IsScalarTower l l₂ L₂ := by
          apply IsScalarTower.of_algebraMap_eq'
          ext x
          exact congrArg (fun f : l₁ →+* L₂ ↦ f (algebraMap l l₁ x)) ht₁₂.algebraMap_eq
        have towerL : IsScalarTower l L L₂ := by
          apply IsScalarTower.of_algebraMap_eq'
          ext x
          change algebraMap l₁ L₂ (algebraMap l l₁ x) =
            algebraMap L₁ L₂ (algebraMap L L₁ (algebraMap l L x))
          rw [← IsScalarTower.algebraMap_apply l L L₁,
            IsScalarTower.algebraMap_apply l l₁ L₁,
            ← IsScalarTower.algebraMap_apply l₁ L₁ L₂]
        exact ⟨l₂, hl₂, all₂, L₂, hL₂, aLL₂, al₂L₂, alL₂, towerl, towerL,
          Module.Finite.trans l₁ l₂, IsPurelyInseparable.trans l l₁ l₂,
          Module.Finite.trans L₁ L₂, IsPurelyInseparable.trans L L₁ L₂, hgen⟩
  let k₀ := ULift.{v} k
  let K₀ := ULift.{u} K
  let : Algebra k₀ k := ULift.algebra' _ _
  let : Algebra k₀ K := ULift.algebra' _ _
  let : Algebra k₀ K₀ := ULift.algebra' _ _
  have : IsScalarTower k₀ k K₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType k K₀ :=
    Algebra.EssFiniteType.of_surjective (ULift.algEquiv (R := k)).symm.toAlgHom
      (ULift.algEquiv (R := k)).symm.surjective
  have : Algebra.EssFiniteType k₀ k :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k₀ k₀ k)
      ULift.down_surjective
  have : Algebra.EssFiniteType k₀ K₀ := Algebra.EssFiniteType.comp k₀ k K₀
  have hfg₀ : (⊤ : IntermediateField k₀ K₀).FG := IntermediateField.fg_top_iff.mpr
    (inferInstance : Algebra.EssFiniteType k₀ K₀)
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k₀ K₀
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k₀ (s : Set K₀)) K₀ := by
    convert! hs.isAlgebraic_field <;> simp
  have : Algebra.EssFiniteType (IntermediateField.adjoin k₀ (s : Set K₀)) K₀ :=
    Algebra.EssFiniteType.of_comp k₀ _ K₀
  have : Module.Finite (IntermediateField.adjoin k₀ (s : Set K₀)) K₀ :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨k', hk', a₀k', K', hK', a₀K', akK', a₀K0', htk, htK,
      hfin, hpure, hfinK, hpureK, hgen⟩ := induction _ k₀ K₀ hfg₀ s hs inferInstance rfl
  let : Module k₀ k' := @Algebra.toModule k₀ k' _ _ a₀k'
  let : Module K₀ K' := @Algebra.toModule K₀ K' _ _ a₀K'
  let : SMul k₀ k' := a₀k'.toSMul
  let : SMul K₀ K' := a₀K'.toSMul
  let : SMul k₀ K' := a₀K0'.toSMul
  let akk' : Algebra k k' := ((algebraMap k₀ k').comp (algebraMap k k₀)).toAlgebra
  let aKK' : Algebra K K' := ((algebraMap K₀ K').comp (algebraMap K K₀)).toAlgebra
  let akK0' : Algebra k K' := ((algebraMap k₀ K').comp (algebraMap k k₀)).toAlgebra
  have : IsScalarTower k k₀ k' :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := k₀) (A := k') rfl
  have : IsScalarTower K K₀ K' :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := K₀) (A := K') rfl
  have : Module.Finite k k₀ := Module.Finite.of_surjective
    (ULift.algEquiv (R := k)).symm.toLinearMap (ULift.algEquiv (R := k)).symm.surjective
  have : Module.Finite K K₀ := Module.Finite.of_surjective
    (ULift.algEquiv (R := K)).symm.toLinearMap (ULift.algEquiv (R := K)).symm.surjective
  have : IsPurelyInseparable k k₀ := (ULift.algEquiv (R := k)).symm.isPurelyInseparable
  have : IsPurelyInseparable K K₀ := (ULift.algEquiv (R := K)).symm.isPurelyInseparable
  have : Module.Finite k₀ k' := hfin
  have : Module.Finite K₀ K' := hfinK
  refine ⟨k', hk', akk', K', hK', aKK', akK', Module.Finite.trans k₀ k',
    IsPurelyInseparable.trans k k₀ k', Module.Finite.trans K₀ K',
    IsPurelyInseparable.trans K K₀ K', hgen, ?_⟩
  ext x
  change algebraMap k' K' (algebraMap k₀ k' (ULift.up x)) =
    algebraMap K₀ K' (ULift.up (algebraMap k K x))
  rw [← IsScalarTower.algebraMap_apply k₀ k' K',
    IsScalarTower.algebraMap_apply k₀ K₀ K']
  rfl

end FieldExtension
