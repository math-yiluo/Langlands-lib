/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison

/-! # Splitting off the first coefficient block

Source: Stacks Project, Tags 01CD and 09MS.
(blueprint: lem-sc-boundary-coefficient-degree-split).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

-- The next two helpers adapt the proved private helpers of
-- SquareZeroTensorSectionProductComparison; no multiplication-of-sections theorem is used.
private theorem power_add_aux {X Z : Scheme.{u}} (F : X.Modules ⥤ Z.Modules)
    [F.LaxMonoidal] (L : X.Modules)
    (P : ∀ d : ℕ, F.obj (L.tensorPow d) ≅ (F.obj L).tensorPow d)
    (h0 : (P 0).inv = Functor.LaxMonoidal.ε F)
    (hs : ∀ d : ℕ, (P (d + 1)).inv =
      (𝟙 (F.obj L) ⊗ₘ (P d).inv) ≫ Functor.LaxMonoidal.μ F L (L.tensorPow d))
    (a b : ℕ) :
    ((P a).inv ⊗ₘ (P b).inv) ≫
      Functor.LaxMonoidal.μ F (L.tensorPow a) (L.tensorPow b) ≫
      F.map (L.tensorPowAddIso a b).inv =
    ((F.obj L).tensorPowAddIso a b).inv ≫ (P (a + b)).inv := by
  induction a with
  | zero =>
    rw [h0]
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Functor.map_comp, Category.assoc]
    change (Functor.LaxMonoidal.ε F ⊗ₘ
      (P b).inv) ≫
        Functor.LaxMonoidal.μ F (𝟙_ X.Modules) (L.tensorPow b) ≫
          F.map (λ_ (L.tensorPow b)).hom ≫
          F.map (eqToHom _) = _
    rw [Functor.LaxMonoidal.ε_tensorHom_comp_μ_assoc]
    simp only [← Functor.map_comp]
    rw [← eqToHom_iso_inv_naturality (P)
      (Nat.zero_add b).symm]
    rw [leftUnitor_naturality_assoc]
    simp only [Iso.inv_hom_id_assoc, eqToHom_map]
  | succ a ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, Functor.map_comp, Category.assoc]
    rw [← eqToHom_iso_inv_naturality (P)
      (Nat.succ_add a b).symm]
    rw [hs a, hs (a + b)]
    simp only [Category.assoc]
    simp only [tensorHom_def, comp_whiskerRight, id_whiskerRight,
      Category.id_comp, Category.assoc]
    rw [← whisker_exchange_assoc]
    erw [Functor.LaxMonoidal.associativity_assoc F L (L.tensorPow a) (L.tensorPow b)]
    rw [associator_naturality_right_assoc, associator_naturality_middle_assoc]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [← whiskerLeft_comp_assoc, ← tensorHom_def,
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    rw [ih]
    simp only [whiskerLeft_comp, Category.assoc, eqToHom_map]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_power_add {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (a b : ℕ) :
    ((boundaryPullbackPowIso j L a).inv ⊗ₘ (boundaryPullbackPowIso j L b).inv) ≫
      (boundaryPullbackTensorIso j (L.tensorPow a) (L.tensorPow b)).inv ≫
      (tensorPullback j).map (L.tensorPowAddIso a b).inv =
    (((tensorPullback j).obj L).tensorPowAddIso a b).inv ≫
      (boundaryPullbackPowIso j L (a + b)).inv := by
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hT (A B : X.Modules) : (boundaryPullbackTensorIso j A B).inv =
      Functor.LaxMonoidal.μ (tensorPullback j) A B := by
    rfl
  have he : (pullbackObjUnitIso j).inv = Functor.LaxMonoidal.ε (pullback j) := by
    apply (cancel_mono (pullbackObjUnitIso j).hom).mp
    rw [Iso.inv_hom_id, ← pullback_monoidal_unit_comparison j]
    exact (Functor.Monoidal.ε_η (pullback j)).symm
  have h0 : (boundaryPullbackPowIso j L 0).inv =
      Functor.LaxMonoidal.ε (tensorPullback j) := by
    change (pullbackObjUnitIso j).inv ≫ (boundaryPullbackComparison j).inv.app _ =
      Functor.LaxMonoidal.ε (pullback j) ≫ (boundaryPullbackComparison j).inv.app _
    rw [he]
    rfl
  rw [hT]
  exact power_add_aux (tensorPullback j) L (boundaryPullbackPowIso j L) h0
    (fun d ↦ by
      change (𝟙 _ ⊗ₘ (boundaryPullbackPowIso j L d).inv) ≫
        (boundaryPullbackTensorIso j L (L.tensorPow d)).inv = _
      rw [hT]) a b

private theorem pullback_power_mul {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (n d : ℕ) :
    (boundaryTensorPowIso (boundaryPullbackPowIso j L n) d).inv ≫
      (boundaryPullbackPowIso j (L.tensorPow n) d).inv ≫
      (tensorPullback j).map (L.tensorPowMulIso n d).inv =
    (((tensorPullback j).obj L).tensorPowMulIso n d).inv ≫
      (boundaryPullbackPowIso j L (n * d)).inv := by
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hn {A B C D : X.Modules} (f : A ⟶ B) (g : C ⟶ D) :
      (boundaryPullbackTensorIso j A C).inv ≫ (tensorPullback j).map (f ⊗ₘ g) =
        ((tensorPullback j).map f ⊗ₘ (tensorPullback j).map g) ≫
          (boundaryPullbackTensorIso j B D).inv := by
    exact (Functor.LaxMonoidal.μ_natural (tensorPullback j) f g).symm
  induction d with
  | zero =>
    simp only [boundaryTensorPowIso, boundaryPullbackPowIso, tensorPowMulIso,
      Iso.trans_inv, Iso.refl_inv, eqToIso.inv, Nat.mul_zero,
      eqToHom_refl, tensorPow_zero, Category.id_comp]
    rw [(tensorPullback j).map_id, Category.comp_id]
  | succ d ih =>
    simp only [boundaryTensorPowIso, boundaryPullbackPowIso,
      tensorPowMulIso, Iso.trans_inv, Iso.refl_inv, tensorIso_inv,
      eqToIso.inv, Functor.map_comp, tensorPow_succ, Category.assoc]
    rw [reassoc_of% hn (𝟙 (L.tensorPow n)) (L.tensorPowMulIso n d).inv]
    rw [(tensorPullback j).map_id]
    rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id, Category.assoc]
    rw [ih]
    have ht :
        ((boundaryPullbackPowIso j L n).inv ⊗ₘ
          ((((tensorPullback j).obj L).tensorPowMulIso n d).inv ≫
            (boundaryPullbackPowIso j L (n * d)).inv)) =
        (𝟙 (((tensorPullback j).obj L).tensorPow n) ⊗ₘ
          (((tensorPullback j).obj L).tensorPowMulIso n d).inv) ≫
        ((boundaryPullbackPowIso j L n).inv ⊗ₘ
          (boundaryPullbackPowIso j L (n * d)).inv) := by
      rw [tensorHom_comp_tensorHom, Category.id_comp]
    rw [ht]
    simp only [Category.assoc]
    rw [reassoc_of% pullback_power_add j L n (n * d)]
    rw [eqToHom_map, eqToHom_iso_inv_naturality (boundaryPullbackPowIso j L)
      (by ring : n + n * d = n * (d + 1))]

private theorem tensorPowAddIso_zero_inv {X : Scheme.{u}} (L : X.Modules) (n : ℕ) :
    (L.tensorPowAddIso n 0).inv =
      (ρ_ (L.tensorPow n)).hom ≫ eqToHom (congrArg L.tensorPow (Nat.add_zero n).symm) := by
  induction n with
  | zero =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorPow_zero, eqToHom_refl, Category.comp_id]
    monoidal
  | succ n ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, tensorPow_succ, Category.assoc]
    rw [ih]
    simp only [id_tensorHom, eqToHom_refl, Category.comp_id]
    monoidal

private theorem tensorPowMulIso_one_inv {X : Scheme.{u}} (L : X.Modules) (n : ℕ) :
    (L.tensorPowMulIso n 1).inv =
      (ρ_ (L.tensorPow n)).hom ≫ eqToHom (congrArg L.tensorPow (Nat.mul_one n).symm) := by
  simp only [tensorPowMulIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    eqToIso.inv, Nat.mul_zero, eqToHom_refl, tensorHom_id, id_whiskerRight]
  rw [tensorPowAddIso_zero_inv]
  simp only [tensorPow_zero, Category.assoc, eqToHom_trans]
  erw [Category.id_comp]

private theorem coefficient_zero_inv {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (n : ℕ) :
    (boundaryCoefficientDegreeIso j L n 0).inv =
      (ρ_ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n))).hom ≫
        (tensorPullback j).map (j.ker.toModules ◁
          eqToHom (congrArg L.tensorPow (Nat.mul_one n).symm)) := by
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have he : (pullbackObjUnitIso j).inv = Functor.LaxMonoidal.ε (pullback j) := by
    apply (cancel_mono (pullbackObjUnitIso j).hom).mp
    rw [Iso.inv_hom_id, ← pullback_monoidal_unit_comparison j]
    exact (Functor.Monoidal.ε_η (pullback j)).symm
  have h0 : (boundaryPullbackPowIso j (L.tensorPow n) 0).inv =
      Functor.LaxMonoidal.ε (tensorPullback j) := by
    change (pullbackObjUnitIso j).inv ≫ (boundaryPullbackComparison j).inv.app _ =
      Functor.LaxMonoidal.ε (pullback j) ≫ (boundaryPullbackComparison j).inv.app _
    rw [he]
    rfl
  simp only [boundaryCoefficientDegreeIso, Iso.trans_inv, tensorIso_inv,
    Iso.refl_inv, Functor.mapIso_inv, boundaryTensorPowIso, Category.assoc,
    tensorPow_zero, Category.id_comp]
  rw [h0, tensorPowMulIso_one_inv]
  have hα : (α_ j.ker.toModules (L.tensorPow n) (𝟙_ X.Modules)).hom ≫
      j.ker.toModules ◁ (ρ_ (L.tensorPow n)).hom =
      (ρ_ (j.ker.toModules ⊗ L.tensorPow n)).hom := by monoidal
  simp only [Iso.symm_inv, id_tensorHom, whiskerLeft_comp, Functor.map_comp]
  rw [← Functor.map_comp_assoc, hα]
  have hT : (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow n)
      (𝟙_ X.Modules)).inv =
      Functor.LaxMonoidal.μ (tensorPullback j) (j.ker.toModules ⊗ L.tensorPow n)
        (𝟙_ X.Modules) := rfl
  rw [hT, ← Functor.LaxMonoidal.right_unitality_assoc]

private theorem coefficient_positive_inv {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (n d : ℕ) :
    (boundaryCoefficientDegreeIso j L n d).inv =
      (𝟙 ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)) ⊗ₘ
        ((((tensorPullback j).obj L).tensorPowMulIso n d).inv ≫
          (boundaryPullbackPowIso j L (n * d)).inv)) ≫
      (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow n)
        (L.tensorPow (n * d))).inv ≫
      (tensorPullback j).map ((α_ _ _ _).hom ≫
        j.ker.toModules ◁ (L.tensorPowAddIso n (n * d)).inv ≫
        j.ker.toModules ◁ eqToHom
          (congrArg L.tensorPow (by ring : n + n * d = n * (d + 1)))) := by
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  simp only [boundaryCoefficientDegreeIso, Iso.trans_inv, tensorIso_inv,
    Iso.refl_inv, Functor.mapIso_inv, Category.assoc]
  rw [show (L.tensorPowMulIso n (d + 1)).inv =
    (𝟙 (L.tensorPow n) ⊗ₘ (L.tensorPowMulIso n d).inv) ≫
      (L.tensorPowAddIso n (n * d)).inv ≫
      eqToHom (congrArg L.tensorPow (by ring : n + n * d = n * (d + 1))) from rfl]
  simp only [Iso.symm_inv, id_tensorHom, whiskerLeft_comp, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, ← associator_naturality_right, Functor.map_comp]
  have hT (A B : X.Modules) : (boundaryPullbackTensorIso j A B).inv =
      Functor.LaxMonoidal.μ (tensorPullback j) A B := rfl
  simp only [hT, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [pullback_power_mul]
  simp only [whiskerLeft_comp, Category.assoc]

private theorem coefficient_zero_hom {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (n : ℕ) :
    (boundaryCoefficientDegreeIso j L n 0).hom ≫
      (ρ_ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n))).hom =
        (tensorPullback j).map (j.ker.toModules ◁
          eqToHom (congrArg L.tensorPow (Nat.mul_one n))) := by
  apply (cancel_epi (boundaryCoefficientDegreeIso j L n 0).inv).mp
  rw [Iso.inv_hom_id_assoc, coefficient_zero_inv]
  simp only [Category.assoc, ← Functor.map_comp, ← whiskerLeft_comp,
    eqToHom_trans, eqToHom_refl, whiskerLeft_id]
  rw [(tensorPullback j).map_id, Category.comp_id]

private theorem coefficient_product_cast {X : Scheme.{u}} (J L : X.Modules)
    (a b n c : ℕ) (hb : b = n) (hc : b + a = c) (hc' : n + a = c) :
    (α_ J (L.tensorPow b) (L.tensorPow a)).hom ≫
        J ◁ (L.tensorPowAddIso b a).inv ≫ J ◁ eqToHom (congrArg L.tensorPow hc) =
      (J ◁ eqToHom (congrArg L.tensorPow hb)) ▷ L.tensorPow a ≫
        (α_ J (L.tensorPow n) (L.tensorPow a)).hom ≫
        J ◁ (L.tensorPowAddIso n a).inv ≫ J ◁ eqToHom (congrArg L.tensorPow hc') := by
  subst b
  simp only [eqToHom_refl, whiskerLeft_id, id_whiskerRight, Category.id_comp]

/-- The coefficient comparison splits off the initial n factors and compares the
remaining factors with the section degree. Unlike block interchange this holds
for arbitrary L; it never permutes its factors.

Source: Stacks Project, Tag 01CD, lemma-tensor-product-pullback, and Tag 09MS,
coherent-equation-ses (expansion of the canonical tensor identifications).
(blueprint: lem-sc-boundary-coefficient-degree-split).
Proof: expand tensorPowMulIso at e+2: its first step splits off n factors by
tensorPowAddIso, and its remaining step groups n(e+1) factors into e+1 blocks.
Naturality and associativity of the monoidal pullback comparison move this
initial split through pullback. Induction on d in boundaryPullbackPowIso shows
that pulling back a concatenation of d factors is the iterated tensorator on
those factors. Induction on e, using associator coherence at each successor,
then identifies the grouped remaining factors with boundarySectionDegreeIso.
The initial coefficient factor stays fixed throughout. The degree-zero
coefficient comparison, followed by its right unitor, is just the arithmetic
identification n*1=n: its pullback unit comparison cancels the unit comparison
in the tensorator by right unitality. Substituting this zero-degree identity
and the preceding grouping identity gives the displayed morphism equality.
At n=0 every L block is the unit and the same induction uses triangle identities;
at e=0 there is one remaining block. No symmetry, invertibility, square-zero
hypothesis, or assertion that arbitrary sheaf tensor sections are pure is used. -/
theorem boundaryCoefficientDegreeIso_split {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (n e : ℕ) :
    let a := n * (e + 1)
    let b := n * (0 + 1)
    let c := n * ((e + 1) + 1)
    let k : (j.ker.toModules ⊗ L.tensorPow b) ⊗ L.tensorPow a ⟶
        j.ker.toModules ⊗ L.tensorPow c :=
      (α_ _ _ _).hom ≫ j.ker.toModules ◁ (L.tensorPowAddIso b a).inv ≫
        j.ker.toModules ◁ (eqToHom (by
          dsimp [a, b, c]
          congr 1
          simp only [Nat.mul_add, Nat.mul_one]
          omega) : L.tensorPow (b + a) ⟶ L.tensorPow c)
    (tensorPullback j).map k ≫ (boundaryCoefficientDegreeIso j L n (e + 1)).hom =
      (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow b)
        (L.tensorPow a)).hom ≫
        (((boundaryCoefficientDegreeIso j L n 0).hom ≫
          (ρ_ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n))).hom) ⊗ₘ
          (boundarySectionDegreeIso j L n e).hom) := by
  dsimp only
  let a := n * (e + 1)
  let b := n * (0 + 1)
  let c := n * ((e + 1) + 1)
  have hb : b = n := by simp [b]
  have hc : b + a = c := by simp [a, b, c, Nat.mul_add, Nat.add_comm]
  have hc' : n + a = c := by simp [a, c, Nat.mul_add, Nat.add_comm]
  let k : (j.ker.toModules ⊗ L.tensorPow b) ⊗ L.tensorPow a ⟶
      j.ker.toModules ⊗ L.tensorPow c :=
    (α_ _ _ _).hom ≫ j.ker.toModules ◁ (L.tensorPowAddIso b a).inv ≫
      j.ker.toModules ◁ eqToHom (congrArg L.tensorPow hc)
  let k' : (j.ker.toModules ⊗ L.tensorPow n) ⊗ L.tensorPow a ⟶
      j.ker.toModules ⊗ L.tensorPow c :=
    (α_ _ _ _).hom ≫ j.ker.toModules ◁ (L.tensorPowAddIso n a).inv ≫
      j.ker.toModules ◁ eqToHom (congrArg L.tensorPow hc')
  have hk : k = (j.ker.toModules ◁ eqToHom (congrArg L.tensorPow hb)) ▷
      L.tensorPow a ≫ k' :=
    coefficient_product_cast j.ker.toModules L a b n c hb hc hc'
  have hi := coefficient_positive_inv j L n (e + 1)
  change (boundaryCoefficientDegreeIso j L n (e + 1)).inv =
    (𝟙 ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)) ⊗ₘ
      (boundarySectionDegreeIso j L n e).inv) ≫
    (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow n)
      (L.tensorPow a)).inv ≫ (tensorPullback j).map k' at hi
  have hp : (tensorPullback j).map k' ≫
      (boundaryCoefficientDegreeIso j L n (e + 1)).hom =
      (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow n)
        (L.tensorPow a)).hom ≫
      (𝟙 ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)) ⊗ₘ
        (boundarySectionDegreeIso j L n e).hom) := by
    apply (cancel_mono (boundaryCoefficientDegreeIso j L n (e + 1)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hi]
    simp only [tensorHom_comp_tensorHom_assoc,
      Iso.hom_inv_id, Category.id_comp, tensorHom_id, id_whiskerRight,
      Iso.hom_inv_id_assoc]
  change (tensorPullback j).map k ≫
    (boundaryCoefficientDegreeIso j L n (e + 1)).hom = _
  rw [hk, Functor.map_comp, Category.assoc, hp, coefficient_zero_hom]
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hn {A B C : X.Modules} (f : A ⟶ B) :
      (tensorPullback j).map (f ▷ C) ≫ (boundaryPullbackTensorIso j B C).hom =
        (boundaryPullbackTensorIso j A C).hom ≫
          (tensorPullback j).map f ▷ (tensorPullback j).obj C := by
    exact (Functor.OplaxMonoidal.δ_natural_left (tensorPullback j) f C).symm
  rw [← Category.assoc, hn, Category.assoc]
  rw [← tensorHom_id, tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp]
  dsimp only [a, b]

end
end AlgebraicGeometry.Scheme.Modules
