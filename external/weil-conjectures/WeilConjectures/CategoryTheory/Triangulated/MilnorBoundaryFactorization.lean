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
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Category.Grp.AB

/-!
# Connecting-map factorization for the Milnor sequence

Source: Stacks Project, More on Algebra, Tags 07KW and 07KY.
(blueprint: lem-pc-milnor-boundary-factorization).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
noncomputable section
attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

@[reassoc]
private theorem comparison_transition
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (K : ℕ → C) [HasProduct K]
    [HasProduct (fun n => F.obj (K n))] (f : ∀ n, K (n + 1) ⟶ K n) :
    F.map (towerTransitionEndomorphism f) ≫ piComparison F K =
      piComparison F K ≫ towerTransitionEndomorphism (fun n => F.map (f n)) := by
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
    Functor.map_id, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    piComparison_comp_π, Limits.Pi.lift_comp_π, Category.id_comp]
  rw [← F.map_comp, Limits.Pi.lift_comp_π]
  rw [← Category.assoc, piComparison_comp_π, ← F.map_comp]

@[reassoc]
private theorem comparison_natural
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (K K' : ℕ → C) [HasProduct K] [HasProduct K']
    [HasProduct (fun n => F.obj (K n))] [HasProduct (fun n => F.obj (K' n))]
    (φ : ∀ n, K n ⟶ K' n) :
    F.map (Limits.Pi.map φ) ≫ piComparison F K' =
      piComparison F K ≫ Limits.Pi.map (fun n => F.map (φ n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
  rw [← F.map_comp, Limits.Pi.map_π]
  rw [← Category.assoc, piComparison_comp_π, ← F.map_comp]

private theorem cokernel_exact {C : Type*} [Category C] [Abelian C]
    {X Y Z W : C} (f : X ⟶ Y) (d : Y ⟶ Z) (q : Z ⟶ W)
    (hfd : f ≫ d = 0) (hdq : d ≫ q = 0)
    (hex : (ShortComplex.mk d q hdq).Exact) :
    ∃ hz : cokernel.desc f d hfd ≫ q = 0,
      (ShortComplex.mk (cokernel.desc f d hfd) q hz).Exact := by
  have hz : cokernel.desc f d hfd ≫ q = 0 := by
    rw [← cancel_epi (cokernel.π f)]
    simpa using hdq
  refine ⟨hz, ?_⟩
  let φ : ShortComplex.mk d q hdq ⟶
      ShortComplex.mk (cokernel.desc f d hfd) q hz :=
    ShortComplex.homMk (cokernel.π f) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : Epi φ.τ₁ := by change Epi (cokernel.π f); infer_instance
  have : IsIso φ.τ₂ := by change IsIso (𝟙 Z); infer_instance
  have : Mono φ.τ₃ := by change Mono (𝟙 W); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex

set_option backward.isDefEq.respectTransparency false in
/-- Factor the connecting map of a Roos triangle through the first derived limit.
Source: Stacks Project, More on Algebra, Tag 07KY; Tag 07KW.
(blueprint: lem-pc-milnor-boundary-factorization).

Proof: preserve countable products under cohomology using Tag 07KC and identify
cohomology of the transition endomorphism componentwise with the Roos map.
The long exact cohomology sequence in degrees i-1 and i has a connecting map
from the product in degree i-1 to H^i(L). Its kernel is the image of the Roos map.
Descend through the cokernel and compose with the natural Roos isomorphism
R^1 lim H^{i-1}(K) to this cokernel (Tag 07KW). The descended arrow is mono
by exactness at the connecting map's source. Exactness at H^i(L) identifies
its image with the kernel of H^i(p). Both factorizations are unique since the
cokernel projection is epi. Naturality of the connecting map and of the Roos
isomorphism therefore gives the displayed naturality square. Choose zero maps
for triples which are not distinguished; for distinguished triples use these
unique factorizations. This chooses all maps simultaneously. -/
theorem milnor_boundary_factorization [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (i : ℤ) :
    ∃ (a : ∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (_p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (_δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj (K ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)) ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L),
      (∀ (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
        [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
        (L : DerivedCategory AddCommGrpCat.{u})
        (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
        (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ →
        Mono (a K L p δ) ∧
        ∃ hz : a K L p δ ≫
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p ≫
              piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
                (fun n : ℕ => K.obj (Opposite.op n))) = 0,
          (ShortComplex.mk (a K L p δ)
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p ≫
              piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
                (fun n : ℕ => K.obj (Opposite.op n))) hz).Exact) ∧
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
            a K L p δ ≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g := by
  classical
  obtain ⟨hP, _, hH, _⟩ :=
    derivedCategory_countableProducts_and_towerLimit.{0, v, u, u+1} AddCommGrpCat.{u}
  let : HasCountableProducts (DerivedCategory AddCommGrpCat.{u}) := hP
  have (j : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} j) := hH ℕ j
  obtain ⟨_, e₀, e₁, he, _⟩ := derivedLimitRoosAbelianGroups.{u}
  let a := fun (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
      [HasProduct (fun n : ℕ => K.obj (Opposite.op n))]
      (L : DerivedCategory AddCommGrpCat.{u})
      (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (Opposite.op n))
      (δ : (∏ᶜ fun n : ℕ => K.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧) =>
    if hT : IsDerivedLimitTriangle (fun n => K.map (homOfLE (Nat.le_succ n)).op) L p δ
    then
      let T := Pretriangulated.Triangle.mk p
        (towerTransitionEndomorphism (fun n => K.map (homOfLE (Nat.le_succ n)).op)) δ
      let c := piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1))
        (fun n : ℕ => K.obj (Opposite.op n))
      let d := inv c ≫ DerivedCategory.HomologySequence.δ T (i - 1) i (by omega)
      have hd : roosMap (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)) ≫
          d = 0 := by
        dsimp [d]
        rw [← cancel_epi c]
        dsimp only [c, roosMap, Functor.comp_map]
        rw [← comparison_transition_assoc]
        simp only [IsIso.hom_inv_id_assoc, comp_zero]
        exact DerivedCategory.HomologySequence.comp_δ T hT (i - 1) i (by omega)
      (e₁ (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1))).hom ≫
        cokernel.desc _ d hd
    else 0
  refine ⟨a, ?_, ?_⟩
  · intro K _ L p δ hT
    dsimp only [a]
    rw [dite_eq_left hT]
    let T := Pretriangulated.Triangle.mk p
      (towerTransitionEndomorphism (fun n => K.map (homOfLE (Nat.le_succ n)).op)) δ
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)
    let c := piComparison H (fun n : ℕ => K.obj (Opposite.op n))
    let d := inv c ≫ DerivedCategory.HomologySequence.δ T (i - 1) i (by omega)
    let f := roosMap (K ⋙ H)
    let q := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p ≫
      piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
        (fun n : ℕ => K.obj (Opposite.op n))
    have hfd : f ≫ d = 0 := by
      rw [← cancel_epi c]
      dsimp only [c, f, d, roosMap, Functor.comp_map]
      rw [← comparison_transition_assoc]
      simp only [IsIso.hom_inv_id_assoc, comp_zero]
      exact DerivedCategory.HomologySequence.comp_δ T hT (i - 1) i (by omega)
    change Mono ((e₁ (K ⋙ H)).hom ≫ cokernel.desc f d hfd) ∧ _
    have h₃ : (ShortComplex.mk f d hfd).Exact := by
      apply ShortComplex.exact_of_iso _
        (DerivedCategory.HomologySequence.exact₃ T hT (i - 1) i (by omega))
      refine ShortComplex.isoMk (asIso c) (asIso c) (Iso.refl _) ?_ ?_
      · change c ≫ f = H.map
          (towerTransitionEndomorphism (fun n => K.map (homOfLE (Nat.le_succ n)).op)) ≫ c
        exact (comparison_transition H (fun n : ℕ => K.obj (Opposite.op n))
          (fun n => K.map (homOfLE (Nat.le_succ n)).op)).symm
      · simp [d]
    have : Mono (cokernel.desc f d hfd) := h₃.mono_cokernelDesc
    refine ⟨inferInstance, ?_⟩
    have hdq : d ≫ q = 0 := by
      dsimp only [d, q]
      rw [Category.assoc, ← Category.assoc
        (DerivedCategory.HomologySequence.δ T (i - 1) i (by omega))]
      have z := DerivedCategory.HomologySequence.δ_comp T hT (i - 1) i (by omega)
      change DerivedCategory.HomologySequence.δ T (i - 1) i (by omega) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map p = 0 at z
      rw [z, zero_comp, comp_zero]
    have h₁ : (ShortComplex.mk d q hdq).Exact := by
      apply ShortComplex.exact_of_iso _
        (DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega))
      refine ShortComplex.isoMk (asIso c) (Iso.refl _)
        (asIso (piComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)
          (fun n : ℕ => K.obj (Opposite.op n)))) ?_ ?_
      · simp [d]
      · rfl
    obtain ⟨hz, hex⟩ := cokernel_exact f d q hfd hdq h₁
    have hz' : ((e₁ (K ⋙ H)).hom ≫ cokernel.desc f d hfd) ≫ q = 0 := by
      simp [Category.assoc, hz]
    refine ⟨hz', ?_⟩
    change (ShortComplex.mk ((e₁ (K ⋙ H)).hom ≫ cokernel.desc f d hfd) q hz').Exact
    let e : ShortComplex.mk (cokernel.desc f d hfd) q hz ≅
        ShortComplex.mk ((e₁ (K ⋙ H)).hom ≫ cokernel.desc f d hfd) q hz' :=
      ShortComplex.isoMk (e₁ (K ⋙ H)).symm (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)
    exact ShortComplex.exact_of_iso e hex
  · intro K K' _ _ L L' p p' δ δ' hT hT' φ g hp hδ
    dsimp only [a]
    rw [dite_eq_left hT, dite_eq_left hT']
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)
    let T := Pretriangulated.Triangle.mk p
      (towerTransitionEndomorphism (fun n => K.map (homOfLE (Nat.le_succ n)).op)) δ
    let T' := Pretriangulated.Triangle.mk p'
      (towerTransitionEndomorphism (fun n => K'.map (homOfLE (Nat.le_succ n)).op)) δ'
    let c := piComparison H (fun n : ℕ => K.obj (Opposite.op n))
    let c' := piComparison H (fun n : ℕ => K'.obj (Opposite.op n))
    let P := Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n))
    let M := Limits.Pi.map (fun n : ℕ => H.map (φ.app (Opposite.op n)))
    have hP : P ≫ T'.mor₂ = T.mor₂ ≫ P := by
      apply (towerTransitionEndomorphism_natural_iff _ _ _).2
      intro n
      exact (φ.naturality (homOfLE (Nat.le_succ n)).op).symm
    let ψ : T ⟶ T' :=
      { hom₁ := g, hom₂ := P, hom₃ := P, comm₁ := hp, comm₂ := hP.symm, comm₃ := hδ }
    have hconn : H.map P ≫ DerivedCategory.HomologySequence.δ T' (i - 1) i (by omega) =
        DerivedCategory.HomologySequence.δ T (i - 1) i (by omega) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g :=
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ_naturality
        ψ (i - 1) i (by omega)
    obtain ⟨h, _, hn⟩ := he (K ⋙ H) (K' ⋙ H) (Functor.whiskerRight φ H)
    rw [← Category.assoc, hn, Category.assoc]
    rw [Category.assoc]
    apply congrArg ((e₁ (K ⋙ H)).hom ≫ ·)
    apply cokernel.map_desc
    change (inv c ≫ DerivedCategory.HomologySequence.δ T (i - 1) i (by omega)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map g =
      M ≫ inv c' ≫ DerivedCategory.HomologySequence.δ T' (i - 1) i (by omega)
    rw [← cancel_epi c]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have hc : c ≫ M = H.map P ≫ c' :=
      (comparison_natural H (fun n : ℕ => K.obj (Opposite.op n))
        (fun n : ℕ => K'.obj (Opposite.op n))
        (fun n => φ.app (Opposite.op n))).symm
    rw [← Category.assoc c M, hc]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact hconn.symm

end
end CategoryTheory
