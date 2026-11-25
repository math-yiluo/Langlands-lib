/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.Triangulated.MilnorBoundaryFactorization
import WeilConjectures.CategoryTheory.Triangulated.MilnorProjectionFactorization

/-!
# Milnor exact sequence for a derived inverse limit

Source: Stacks Project, More on Algebra, Tags 07KY and 08U5;
Derived Categories of Schemes, Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-limit-milnor-sequence).

The maps are chosen simultaneously for all specified Roos triangles and are natural
for morphisms of these triangles. No functorial choice of a derived-limit object is assumed.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

noncomputable section

attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive


/-- The cohomology projections of a Roos triangle form a cone over the tower. -/
private def milnorProjectionCone [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (i : ℤ) (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
    [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
    (L : DerivedCategory AddCommGrpCat.{u})
    (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
    (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ) :
    Cone (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) where
  pt := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L
  π := NatTrans.ofOpSequence
    (fun n => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (p ≫ Pi.π (fun n : ℕ => K.obj (Opposite.op n)) n)) (by
      intro n
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
        Functor.comp_map, ← Functor.map_comp]
      apply congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      have hzero := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
      have hn := congrArg
        (fun f => f ≫ Pi.π (fun n : ℕ => K.obj (Opposite.op n)) n) hzero
      simp only [zero_comp] at hn
      change (p ≫ towerTransitionEndomorphism
        (fun n => K.map (homOfLE (Nat.le_succ n)).op)) ≫
          Pi.π (fun n : ℕ => K.obj (Opposite.op n)) n = 0 at hn
      simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
        Category.id_comp, Pi.lift_comp_π, Preadditive.comp_sub, Category.assoc] at hn
      simpa only [Category.assoc] using (sub_eq_zero.mp hn))

/-- The natural Milnor short exact sequence for every derived inverse limit of abelian groups.
Source: Stacks Project, Tags 07KY and 08U5; Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-limit-milnor-sequence).

Proof, following the node:
1. Use the defining distinguished Roos triangle (`def-weil-derived-limit`). Exactness of
countable products in abelian groups (`lem-pc-abelian-groups-exact-products`) and part (2)
of `lemma-reduction-derived-nakayama` identify the cohomology of the product with the
product of the cohomology groups, compatibly with every projection. Under this identification
cohomology sends the transition endomorphism to the transition endomorphism of the cohomology
system, since its projection is `pr n - pr (n + 1) ≫ f n`.
2. Apply `lem-sf-derived-homology-long-exact` to this triangle. The resulting five-term
segment starts with `1 - s` on the product in degree `i - 1` and ends with `1 - s` in
degree `i`. By `lem-pc-derived-limit-roos-abelian-groups`, their cokernel and kernel are
respectively the actual first right derived functor of inverse limit and inverse limit.
Factor the connecting map through that cokernel and the cohomology of `p` through that
kernel. Exactness gives the displayed short exact complex. The factorization of the latter
map is recorded by its equations after every limit projection. The natural Roos
identifications and natural long exact sequence give both commuting squares for every
morphism of specified triangles. This construction chooses the maps simultaneously.

`K` is the tower functor. The transition maps are recovered from its successor arrows.
The product instance supplies the product already present in the specified derived-limit
triangle, rather than a finiteness or boundedness hypothesis. All degrees are integers. -/
theorem milnor_shortExact [HasDerivedCategory.{v} AddCommGrpCat.{u}] (i : ℤ) :
    ∃ (a : ∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (_p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (_δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj (K ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)) ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L)
      (b : ∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (_p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (_δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶ limit (K ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)),
      (∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ →
        (∃ hz : a K L p δ ≫ b K L p δ = 0,
          (ShortComplex.mk (a K L p δ) (b K L p δ) hz).ShortExact) ∧
        ∀ n : ℕ, b K L p δ ≫ limit.π (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
          (Opposite.op n) =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map (p ≫ Pi.π (fun n : ℕ => K.obj
            (Opposite.op n)) n)) ∧
      ∀ (K K' : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        [HasProduct (fun n : ℕ => K'.obj (Opposite.op n))]
        (L L' : DerivedCategory AddCommGrpCat.{u})
        (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (p' : L' ⟶ ∏ᶜ fun n : ℕ => K'.obj (Opposite.op n))
        (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧)
        (δ' : (∏ᶜ fun n : ℕ => K'.obj (Opposite.op n)) ⟶ L'⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ →
        IsDerivedLimitTriangle (fun n => K'.map (homOfLE (Nat.le_succ n)).op) L' p' δ' →
        ∀ (φ : K ⟶ K') (g : L ⟶ L'),
          p ≫ Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) = g ≫ p' →
          δ ≫ (shiftFunctor _ (1 : ℤ)).map g =
            Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) ≫ δ' →
          ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).map
            (Functor.whiskerRight φ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1))) ≫ a
            K' L' p' δ' =
            a K L p δ ≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g ∧
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g ≫ b K' L' p' δ' =
            b K L p δ ≫ limMap (Functor.whiskerRight φ (DerivedCategory.homologyFunctor
              AddCommGrpCat.{u} i)) := by
  obtain ⟨a, ha, hnat⟩ := milnor_boundary_factorization.{u, v} i
  classical
  let b : ∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
      [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
      (L : DerivedCategory AddCommGrpCat.{u})
      (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
      (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶
        limit (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) :=
    fun K _ L p δ =>
      if hT : IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ
      then limit.lift _ (milnorProjectionCone i K L p δ hT)
      else 0
  have hb (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
      [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
      (L : DerivedCategory AddCommGrpCat.{u})
      (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
      (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧)
      (hT : IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ) :
      Epi (b K L p δ) ∧
        ∀ n : ℕ, b K L p δ ≫ limit.π
          (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (Opposite.op n) =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
            (p ≫ Pi.π (fun n : ℕ => K.obj (Opposite.op n)) n) := by
    have hπ (n : ℕ) : b K L p δ ≫ limit.π
        (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (Opposite.op n) =
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
          (p ≫ Pi.π (fun n : ℕ => K.obj (Opposite.op n)) n) := by
      simp only [b, dite_eq_left hT, limit.lift_π, milnorProjectionCone,
        NatTrans.ofOpSequence_app]
    exact ⟨milnor_projection_epi i K L p δ hT _ hπ, hπ⟩
  refine ⟨a, b, ?_, ?_⟩
  · intro K hP L p δ hT
    obtain ⟨hm, hz, he⟩ := ha K L p δ hT
    obtain ⟨hep, hπ⟩ := hb K L p δ hT
    let j := Pi.lift
      (f := fun n : ℕ => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        (K.obj (Opposite.op n))) (fun n : ℕ => limit.π
      (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (Opposite.op n))
    have hj : Mono j := ⟨by
      intro Z f g h
      apply limit.hom_ext
      intro n
      obtain ⟨n⟩ := n
      have hn := congrArg
        (fun k => k ≫ Pi.π
          (fun n : ℕ => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
            (K.obj (Opposite.op n))) n) h
      dsimp only [Functor.comp_obj] at hn ⊢
      simpa only [j, Category.assoc, Pi.lift_comp_π] using hn⟩
    have hbj : b K L p δ ≫ j =
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p ≫
          piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
            (fun n : ℕ => K.obj (Opposite.op n)) := by
      apply Pi.hom_ext
      intro n
      simpa only [j, Category.assoc, Pi.lift_comp_π, piComparison_comp_π,
        ← Functor.map_comp] using hπ n
    have hz' : a K L p δ ≫ b K L p δ = 0 := by
      apply (cancel_mono j).1
      simpa only [Category.assoc, hbj, zero_comp] using hz
    refine ⟨⟨hz', ?_⟩, hπ⟩
    let φ : ShortComplex.mk (a K L p δ) (b K L p δ) hz' ⟶
        ShortComplex.mk (a K L p δ)
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p ≫
            piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
              (fun n : ℕ => K.obj (Opposite.op n))) hz :=
      ShortComplex.homMk (𝟙 _) (𝟙 _) j
        (by simp) (by simpa using hbj.symm)
    have : Epi φ.τ₁ := by change Epi (𝟙 _); infer_instance
    have : IsIso φ.τ₂ := by change IsIso (𝟙 _); infer_instance
    have : Mono φ.τ₃ := hj
    have hex : (ShortComplex.mk (a K L p δ) (b K L p δ) hz').Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 he
    exact ShortComplex.ShortExact.mk' hex hm hep
  · intro K K' hP hP' L L' p p' δ δ' hT hT' φ g hp hδ
    refine ⟨hnat K K' L L' p p' δ δ' hT hT' φ g hp hδ, ?_⟩
    apply limit.hom_ext
    intro n
    obtain ⟨n⟩ := n
    have hπ := (hb K L p δ hT).2 n
    have hπ' := (hb K' L' p' δ' hT').2 n
    have hpπ := congrArg
      (fun f => f ≫ Pi.π (fun n : ℕ => K'.obj (Opposite.op n)) n) hp
    simp only [Category.assoc, Pi.map_π] at hpπ
    rw [Category.assoc, hπ', Category.assoc, limMap_π]
    change (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
          (p' ≫ Pi.π (fun n : ℕ => K'.obj (Opposite.op n)) n) =
      b K L p δ ≫ limit.π
        (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (Opposite.op n) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map (φ.app (Opposite.op n))
    rw [← Category.assoc, hπ, ← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
    simpa only [Category.assoc] using hpπ.symm

end
end CategoryTheory
