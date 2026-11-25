/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subcategory
public import WeilConjectures.WeilSheaf.LisseAbelian

/-!
# The abelian category of lisse Weil representations

Lisse Weil representations contain zero and are closed under subobjects, quotients and finite
direct sums in `Rep ℚ̄_ℓ W(C₀)`, so they form an abelian full subcategory whose inclusion is
exact. Consequently every equivalence between lisse Weil sheaves on `C₀` and lisse Weil
representations of `W(C₀)`, in particular the lisse sheaf–representation equivalence, matches
short exact sequences (`AlgebraicGeometry.WeilGroup.isLisse_shortExact_iff`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) (l : ℕ) [Fact l.Prime]

instance isLisseRep.isClosedUnderIsomorphisms : (W.isLisseRep l).IsClosedUnderIsomorphisms where
  of_iso e h := (W.isLisseRep l).prop_of_mono e.inv h

instance isLisseRep.containsZero : (W.isLisseRep l).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have : Subsingleton (0 : Rep.{u} (PadicAlgCl l) W.carrier).V :=
      ModuleCat.subsingleton_of_isZero
        ((forget₂ (Rep.{u} (PadicAlgCl l) W.carrier) (ModuleCat.{u} (PadicAlgCl l))).map_isZero
          (isZero_zero _))
    refine ⟨Module.Finite.of_injective (0 : _ →ₗ[PadicAlgCl l] PadicAlgCl l)
      fun _ _ _ ↦ Subsingleton.elim _ _, IsLisse.of_continuous_apply fun φ v ↦ ?_⟩
    simp only [Subsingleton.elim v 0, map_zero]
    exact continuous_const

variable {W l} in
/-- A direct sum of lisse Weil representations is lisse: a vector `v` of `X ⊞ Y` is
`inl (fst v) + inr (snd v)`, so every coefficient of `X ⊞ Y` is a sum of coefficients of `X`
and of `Y`. -/
theorem isLisseRep.biprod {X Y : Rep.{u} (PadicAlgCl l) W.carrier} (hX : W.isLisseRep l X)
    (hY : W.isLisseRep l Y) : W.isLisseRep l (X ⊞ Y) := by
  obtain ⟨_, hρX⟩ := hX
  obtain ⟨_, hρY⟩ := hY
  have htot (v : (X ⊞ Y).V) : (biprod.inl : X ⟶ X ⊞ Y).hom ((biprod.fst : X ⊞ Y ⟶ X).hom v) +
      (biprod.inr : Y ⟶ X ⊞ Y).hom ((biprod.snd : X ⊞ Y ⟶ Y).hom v) = v := by
    have h := congrArg (fun f : X ⊞ Y ⟶ X ⊞ Y ↦ f.hom v) (biprod.total (X := X) (Y := Y))
    simp only [Rep.add_hom, Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.coe_add,
      Pi.add_apply,
      Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.id_apply] at h
    exact h
  have hinj : Function.Injective (LinearMap.prod (biprod.fst : X ⊞ Y ⟶ X).hom.toLinearMap
      (biprod.snd : X ⊞ Y ⟶ Y).hom.toLinearMap) := by
    intro v w h
    have h₁ : (biprod.fst : X ⊞ Y ⟶ X).hom v = (biprod.fst : X ⊞ Y ⟶ X).hom w :=
      congrArg Prod.fst h
    have h₂ : (biprod.snd : X ⊞ Y ⟶ Y).hom v = (biprod.snd : X ⊞ Y ⟶ Y).hom w :=
      congrArg Prod.snd h
    rw [← htot v, ← htot w, h₁, h₂]
  refine ⟨Module.Finite.of_injective _ hinj, IsLisse.of_continuous_apply fun φ v ↦ ?_⟩
  have key (g : W.geometric) : φ ((X ⊞ Y).ρ g v) =
      (φ ∘ₗ (biprod.inl : X ⟶ X ⊞ Y).hom.toLinearMap) (X.ρ g ((biprod.fst : X ⊞ Y ⟶ X).hom v)) +
      (φ ∘ₗ (biprod.inr : Y ⟶ X ⊞ Y).hom.toLinearMap)
        (Y.ρ g ((biprod.snd : X ⊞ Y ⟶ Y).hom v)) := by
    conv_lhs => rw [← htot v]
    simp [← Rep.hom_comm_apply]
  simp_rw [key]
  exact (hρX.continuous_apply _ _).add (hρY.continuous_apply _ _)

instance isLisseRep.isClosedUnderFiniteProducts : (W.isLisseRep l).IsClosedUnderFiniteProducts :=
  have : (W.isLisseRep l).IsClosedUnderBinaryProducts :=
    .mk' (by
      rintro _ ⟨F, hF⟩
      exact (W.isLisseRep l).prop_of_iso
        ((biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
        (isLisseRep.biprod (hF ⟨.left⟩) (hF ⟨.right⟩)))
  .mk'

/-- Blueprint `definition-weil-representation--1` (subsection
`definition-weil-representation--1`): exactness of the lisse sheaf–representation
equivalence.

Let `e` be an equivalence between lisse Weil sheaves on `C₀` and lisse Weil representations of
`W(C₀)`, such as `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`. A short complex
`0 → ℱ' → ℱ → ℱ'' → 0` of lisse Weil sheaves is short exact in the category of Weil sheaves if
and only if the corresponding complex `0 → V' → V → V'' → 0` of representations is short exact:
both categories are abelian full subcategories, closed under kernels, cokernels and finite
direct sums (`AlgebraicGeometry.WeilSheaf.IsLisse.kernel_cokernel`,
`AlgebraicGeometry.WeilGroup.isLisseRep.isClosedUnderKernels`), so their inclusions are exact,
and an equivalence of abelian categories is exact. In particular subobjects, quotients and
subquotients match on the two sides. -/
theorem isLisse_shortExact_iff {C : Scheme.{u}} [C.Over (Spec (.of K))]
    [IsCurve (C ↘ Spec (.of K))] [Fact (ringChar K ≠ l)] {W : WeilGroup (C ↘ Spec (.of K))}
    (e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
      ObjectProperty.FullSubcategory (W.isLisseRep l))
    (S : ShortComplex (ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))) :
    (S.map (ObjectProperty.ι _)).ShortExact ↔
      (S.map (e.functor ⋙ ObjectProperty.ι _)).ShortExact :=
  ObjectProperty.shortExact_map_ι_iff_of_equivalence e S

end AlgebraicGeometry.WeilGroup
