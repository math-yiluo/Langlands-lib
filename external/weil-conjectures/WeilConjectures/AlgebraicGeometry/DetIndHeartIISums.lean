/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.DirectSum.Basic
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts

/-!
# Ext from a constructible sheaf commutes with ind-constructible sums

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-ind-constructible-sheaves/sk-cor-ind-heart-ii/sk-cor-ind-heart-ii-sums.md
and its proof
(blueprint: corollary-ind-heart-b--2).

The Noetherian scope is the accepted correction recorded in the node's stage-1 report.
Both coefficient choices are condensed rings pulled back to the small pro-etale site.
The coproduct is specified by its universal property in the ambient module category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj DirectSum

namespace AlgebraicGeometry.ProEtale

-- Elaborating the summand comparison unfolds the direct-sum model of the heart.
/-- Ext from a constructible sheaf commutes with arbitrary small sums of
ind-constructible sheaves, in every integer degree. The displayed additive homomorphism
is the unique map whose restriction to each summand is postcomposition with the shifted
coprojection. Bijectivity is equivalent to its being an isomorphism of abelian groups.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-ind-constructible-sheaves/sk-cor-ind-heart-ii/sk-cor-ind-heart-ii-sums.md
and its proof
(blueprint: corollary-ind-heart-b--2).

Proof: first the degree-zero embedding, the shift, and additive Hom from C preserve
finite sums, including the empty sum. Express the ambient sum as the filtered colimit
of its finite subcoproducts, indexed by finite subsets of S. Their standard cocone is
colimiting. Apply constructible_sheaf_ext_continuity to this diagram: it identifies Ext
of that filtered colimit with the filtered colimit of Ext. Finite additivity identifies
the latter with the direct sum of the individual Ext groups. Under these identifications
the map on each summand is postcomposition by its shifted coprojection, so the composite
is exactly DirectSum.toAddMonoid below. Hence that additive homomorphism is bijective. -/
theorem det_ind_heart_ii_sums
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (C : CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C)
    (q : ℤ) (S : Type (u + 1))
    (B : S → CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (_hB : ∀ s : S, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (coefficientHeartRingObj R) X) (B s))
    (c : Cofan B) (hc : IsColimit c) :
    Function.Bijective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun s : S ↦
        Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj C)
          ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor _ 0).map (c.inj s)))) :
        (⨁ s : S,
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj (B s)))) →+
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt))) := by
  classical
  let : HasCoproduct B := ⟨⟨c, hc⟩⟩
  let s := (DerivedCategory.singleFunctor _ 0).obj C
  let Y (i : S) := (shiftFunctor _ q).obj
    ((DerivedCategory.singleFunctor _ 0).obj (B i))
  have hcont : DerivedCategory.HomFactorsThroughFilteredColimits.{u + 1} s := by
    let Y' := preadditiveCoyoneda.obj (Opposite.op s)
    intro I _ _ M cM hcM n f
    let G₀ := DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (-n) ⋙ Y'
    have hi : IsIso (colimit.post M G₀) := by
      exact constructible_sheaf_ext_continuity ℓ E R hR X C hC M
        (colimit.cocone M) (colimit.isColimit M) (-n)
    let : IsIso (colimit.post M G₀) := hi
    have : PreservesColimit M G₀ := preservesColimit_of_isIso_post _ _
    have : PreservesColimit M ((DerivedCategory.singleFunctor _ 0 ⋙
        shiftFunctor _ (-n)) ⋙ Y') := preservesColimit_of_natIso M
      (Functor.associator _ _ _).symm
    let G := DerivedCategory.singleFunctor _ n ⋙ Y'
    have : PreservesColimit M G := preservesColimit_of_natIso M
      (Functor.isoWhiskerRight ((DerivedCategory.singleFunctors _).shiftIso (-n) n 0
        (by omega)) Y')
    obtain ⟨i, g, hg⟩ := Concrete.isColimit_exists_rep (M ⋙ G)
      (isColimitOfPreserves G hcM) f
    exact ⟨i, g, hg.symm⟩
  let : HasColimitsOfSize.{u + 1, u + 1} (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)) :=
    IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1} (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)) := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let : HasCoproducts.{u + 1} (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))) :=
    fun J ↦ inferInstance
  have hcompact0 :=
    DerivedCategory.compactFor_singleFunctor_of_homFactorsThroughFilteredColimits
      hcont (-q) B
  have hcompact : CategoryTheory.CompactFor s Y :=
    CategoryTheory.CompactFor.of_iso
      (fun i ↦ ((DerivedCategory.singleFunctors _).shiftIso q (-q) 0 (by omega)).app (B i))
      hcompact0
  let F : (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)) ⥤
      DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X)) :=
    DerivedCategory.singleFunctor
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj R) X)) 0 ⋙
      shiftFunctor (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X))) q
  let cY : Cofan Y := Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.inj i))
  have hcY : IsColimit cY := by
    simpa [cY, F, Y] using
      (isColimitCofanMkObjOfIsColimit (G := F) (f := B) (P := c.pt)
        (fun i ↦ c.inj i) hc)
  have hsurj : Function.Surjective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun i : S ↦
        Preadditive.rightComp s ((shiftFunctor _ q).map
          ((DerivedCategory.singleFunctor _ 0).map (c.inj i)))) :
        (⨁ i : S, (s ⟶ Y i)) →+ (s ⟶
          (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt))) := by
    intro f
    obtain ⟨T, g, hg⟩ := CompactFor.of_isColimit hcompact hcY f
    refine ⟨∑ i ∈ T, DirectSum.of (fun i : S ↦ s ⟶ Y i) i (g i), ?_⟩
    simp only [map_sum, DirectSum.toAddMonoid_of]
    simpa [cY, Y, F, Preadditive.rightComp, ← Functor.map_comp, Category.assoc] using hg.symm
  have hinj : Function.Injective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun i : S ↦
        Preadditive.rightComp s ((shiftFunctor _ q).map
          ((DerivedCategory.singleFunctor _ 0).map (c.inj i)))) :
        (⨁ i : S, (s ⟶ Y i)) →+ (s ⟶
          (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt))) := by
    let proj (j : S) : c.pt ⟶ B j :=
      hc.desc (Cofan.mk _ (fun i ↦ if h : i = j then eqToHom (congrArg B h) else 0))
    have proj_comp (i j : S) : c.inj i ≫ proj j =
        if h : i = j then eqToHom (congrArg B h) else 0 := by
      exact hc.fac _ ⟨i⟩
    let projShift (j : S) := (shiftFunctor _ q).map
      ((DerivedCategory.singleFunctor _ 0).map (proj j))
    have comp_proj (d : ⨁ i : S, (s ⟶ Y i)) (j : S) :
        (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun i : S ↦
          Preadditive.rightComp s ((shiftFunctor _ q).map
            ((DerivedCategory.singleFunctor _ 0).map (c.inj i)))) d) ≫ projShift j = d j := by
      induction d using DirectSum.induction_on with
      | zero => simp
      | of i x =>
          rw [DirectSum.toAddMonoid_of]
          by_cases h : i = j
          · subst j
            dsimp [Preadditive.rightComp]
            change (x ≫ _) ≫ _ = _
            rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, proj_comp]
            simp only [dite_eq_left, eqToHom_refl]
            rw [(DerivedCategory.singleFunctor _ 0).map_id, (shiftFunctor _ q).map_id]
            simp only [DirectSum.of_apply, dite_eq_left]
            change x ≫ 𝟙 (Y i) = x
            exact Category.comp_id x
          · dsimp [projShift, Preadditive.rightComp]
            change (x ≫ _) ≫ _ = _
            rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, proj_comp]
            simp [DirectSum.of_apply, h]
      | add d₁ d₂ h₁ h₂ => simp [Preadditive.add_comp, h₁, h₂]
    intro x y hxy
    ext j
    have hz' :
        (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun i : S ↦
          Preadditive.rightComp s ((shiftFunctor _ q).map
            ((DerivedCategory.singleFunctor _ 0).map (c.inj i)))) (x - y)) ≫ projShift j = 0 := by
      rw [map_sub, sub_eq_zero.mpr hxy, zero_comp]
    have hxy' := (comp_proj (x - y) j).symm.trans hz'
    rw [DirectSum.sub_apply] at hxy'
    exact sub_eq_zero.mp hxy'
  exact ⟨hinj, hsurj⟩

end AlgebraicGeometry.ProEtale
