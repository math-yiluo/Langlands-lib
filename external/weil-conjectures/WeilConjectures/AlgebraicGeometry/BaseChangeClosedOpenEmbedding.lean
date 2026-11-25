/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Closed–open coefficient embedding

Source: Stacks Project, Tag 0F07, closed–open part of the proof.
(blueprint: lem-sbc-closed-open-coefficient-embedding)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
/-- The open injective embedding and the closed unit jointly embed the coefficient sheaf.

Source: Stacks Project, Tag 0F07, proof of condition (3).
(blueprint: lem-sbc-closed-open-coefficient-embedding)

Proof: if a morphism into F is killed by both components, adjunction identifies
its open restriction followed by the injective embedding with zero. Monicity of
the injective embedding kills the open restriction. The closed unit similarly kills
the closed restriction. The geometric points obtained from the algebraic closures
of residue fields of V and Z jointly cover T. Pullback-stalk comparison makes the
morphism zero on all these stalks, so their conservative family makes it zero.
The cancellation-of-zero criterion proves that the pair is monic.
-/
theorem mono_closedOpen_coefficient_embedding {T Z : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : T.Opens) (i : Z ⟶ T) [IsClosedImmersion i]
    (hi : Set.range i.base = (V : Set T)ᶜ) :
    Mono (biprod.lift
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.ι).unit.app F ≫
        ((V.ι)_*[ModuleCat.{u + 1} Λ]).map
          (Injective.ι (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj F)))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F)) := by
  apply Preadditive.mono_of_cancel_zero
  intro Q γ hγ
  have hγV := congrArg (fun k ↦ k ≫ biprod.fst) hγ
  simp only [Category.assoc, biprod.lift_fst, zero_comp] at hγV
  have hγZ := congrArg (fun k ↦ k ≫ biprod.snd) hγ
  simp only [Category.assoc, biprod.lift_snd, zero_comp] at hγZ
  have hV : ((V.ι)^*[ModuleCat.{u + 1} Λ]).map γ = 0 := by
    apply (cancel_mono (Injective.ι _)).1
    apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.ι).homEquiv Q _).injective
    simp only [Adjunction.homEquiv_apply, Functor.map_comp, Functor.map_zero]
    have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.ι).unit.naturality γ
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc]
    simpa only [Functor.id_obj, zero_comp, comp_zero] using hγV
  have hZ : ((i)^*[ModuleCat.{u + 1} Λ]).map γ = 0 := by
    apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).homEquiv Q _).injective
    simp only [Adjunction.homEquiv_apply, Functor.map_zero, comp_zero]
    have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.naturality γ
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn]
    exact hγZ
  let Ω : V.toScheme ⊕ Z → Type u := fun t ↦ match t with
    | .inl v => AlgebraicClosure (V.toScheme.residueField v)
    | .inr z => AlgebraicClosure (Z.residueField z)
  let : ∀ t, Field (Ω t) := fun t ↦ by cases t <;> dsimp [Ω] <;> infer_instance
  let : ∀ t, IsAlgClosed (Ω t) := fun t ↦ by cases t <;> dsimp [Ω] <;> infer_instance
  let points : ∀ t, Spec (CommRingCat.of (Ω t)) ⟶ T := fun t ↦ match t with
    | .inl v => V.toScheme.algClosurePoint v ≫ V.ι
    | .inr z => Z.algClosurePoint z ≫ i
  have hcover : (⋃ t, Set.range (points t)) = Set.univ := by
    refine Set.eq_univ_of_forall fun t ↦ ?_
    by_cases ht : t ∈ V
    · let v : V.toScheme := ⟨t, ht⟩
      obtain ⟨s, y, hy⟩ : ∃ s : V.toScheme, ∃ y, V.toScheme.algClosurePoint s y = v := by
        have hv : v ∈ ⋃ s, Set.range (V.toScheme.algClosurePoint s) := by
          rw [V.toScheme.iUnion_range_algClosurePoint]; trivial
        simpa only [Set.mem_iUnion, Set.mem_range] using hv
      exact Set.mem_iUnion.2 ⟨Sum.inl s, y, congrArg (fun v ↦ V.ι v) hy⟩
    · obtain ⟨z, rfl⟩ := (hi.symm ▸ ht : t ∈ Set.range i.base)
      obtain ⟨s, y, hy⟩ : ∃ s : Z, ∃ y, Z.algClosurePoint s y = z := by
        have hz : z ∈ ⋃ s, Set.range (Z.algClosurePoint s) := by
          rw [Z.iUnion_range_algClosurePoint]; trivial
        simpa only [Set.mem_iUnion, Set.mem_range] using hz
      exact Set.mem_iUnion.2 ⟨Sum.inr s, y, congrArg (fun z ↦ i z) hy⟩
  have : LocallySmall.{u + 1} T.Etale := locallySmall_max.{u + 1, u}
  have : LocallySmall.{u + 1} V.toScheme.Etale := locallySmall_max.{u + 1, u}
  have : LocallySmall.{u + 1} Z.Etale := locallySmall_max.{u + 1, u}
  have hP := (Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    T points hcover).jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ)
  refine hP.eq_zero_of_map_eq_zero γ ?_
  rintro ⟨-, ⟨t⟩⟩
  cases t with
  | inl v =>
    change ((Scheme.pointSmallEtale
      (V.toScheme.algClosurePoint v ≫ V.ι)).ulift.{u + 1}).sheafFiber.map γ = 0
    rw [← NatIso.naturality_1 (upperStarCompUliftSheafFiberIso _ V.ι
      (V.toScheme.algClosurePoint v)) γ]
    simp [hV]
  | inr z =>
    change ((Scheme.pointSmallEtale (Z.algClosurePoint z ≫ i)).ulift.{u + 1}).sheafFiber.map γ = 0
    rw [← NatIso.naturality_1 (upperStarCompUliftSheafFiberIso _ i
      (Z.algClosurePoint z)) γ]
    simp [hZ]

end AlgebraicGeometry.Etale
