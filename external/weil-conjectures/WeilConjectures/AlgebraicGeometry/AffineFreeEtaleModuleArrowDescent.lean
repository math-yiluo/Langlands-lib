/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleEventualHomLift
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible

/-!
# Descent of arrows between finite sums of affine etale free module sheaves

Source: Stacks Project, Tags 09YU (3), 09YQ, 095N and 03S6.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An arrow between finite sums of affine etale free sheaves descends to an arrow
between constructible module sheaves at a common stage.

Source: Stacks Project, Tag 09YU (3), proof of essential surjectivity using Tag 095N;
Tag 09YQ for sections, Tag 03S6 for free sheaves and base change.
(blueprint: lem-weil-pbc-affine-free-etale-module-arrow-descent).

Proof:
1. Descend the finitely many affine etale objects U and V using the essential
surjectivity of the affine etale site colimit. Directedness gives one common stage.
Transport the original arrow through the induced free-sheaf isomorphisms.
2. At that stage form the finite sum Q of the descended U free sheaves. Base change
of free sheaves and preservation of sums identify its inverse image with the target
of f. Represent f on each V summand by a section of this inverse image of Q, using
free Yoneda followed by sheafification.
3. The section-colimit theorem 09YQ represents each such section at a later stage.
Choose a common upper bound of those finitely many stages, moving sections along
transition maps. Form A from the free sheaves on the V objects at this later stage,
and B as the pullback of Q from the initial common stage. The sections define a map a.
4. Free-sheaf base change and composition give isomorphisms eA and eB. Check the
asserted square on each free generator: the section comparison is precisely the unit
of inverse image followed by its composition isomorphism. Yoneda and the coproduct
universal property identify the two arrows.
5. Each descended affine etale free sheaf is constructible by 03S8. Finite sums are
constructible by the Serre property 03RZ, including the empty sum (zero); inverse
image preserves constructibility. Thus both A and B are constructible.
No cokernel or constructible sheaf F is involved in this statement. -/
theorem exists_affine_free_etaleModule_arrow_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (n m : ℕ) (U : Fin n → c.pt.Etale) (V : Fin m → c.pt.Etale)
    (hU : ∀ k : Fin n, IsAffine (U k).left)
    (hV : ∀ k : Fin m, IsAffine (V k).left) :
    let P : c.pt.Etale → Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun W => (presheafToSheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∀ f : (∐ fun j : Fin m => P (V j)) ⟶ (∐ fun k : Fin n => P (U k)),
      ∃ (i : I)
        (A B : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (a : A ⟶ B),
        IsConstructibleEtaleModuleSheaf A ∧ IsConstructibleEtaleModuleSheaf B ∧
        ∃ (eA : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj A ≅
            (∐ fun j : Fin m => P (V j)))
          (eB : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj B ≅
            (∐ fun k : Fin n => P (U k))),
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).map a ≫ eB.hom =
            eA.hom ≫ f := by
  classical
  intro P f
  obtain ⟨i, WU, WV, hWU, hWV, ⟨eB⟩, ⟨eA⟩⟩ :=
    exists_affine_free_etaleModule_family_models D c hc Λ n m U V hU hV
  let Q : (D.obj (op i)).Etale →
      Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun W ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))
  let A₀ := ∐ fun k : Fin m ↦ Q (WV k)
  let B₀ := ∐ fun k : Fin n ↦ Q (WU k)
  obtain ⟨j, h, a, ha⟩ := exists_affine_free_etaleModule_eventual_hom_lift
    D c hc Λ i m WV hWV B₀ (eA.hom ≫ f ≫ eB.inv)
  let t := Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)
  let E := Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
    (D.map (homOfLE h).op) (c.π.app (op i)) (c.w (homOfLE h).op).symm
  have : ∀ k, IsAffine (WU k).left := hWU
  have : ∀ k, IsAffine (WV k).left := hWV
  have hQ (W : (D.obj (op i)).Etale) [IsAffine W.left] :
      IsConstructibleEtaleModuleSheaf (Q W) :=
    isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
      (X := D.obj (op i)) (U := W.left) W.hom (ModuleCat.of Λ Λ)
  have hQA (k : Fin m) : IsConstructibleSheaf (Q (WV k)) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hQ (WV k))
  have hQB (k : Fin n) : IsConstructibleSheaf (Q (WU k)) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hQ (WU k))
  have : HasFiniteBiproducts
      (Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    Abelian.hasFiniteBiproducts
  have : IsConstructibleSheaf (⨁ fun k : Fin m ↦ Q (WV k)) :=
    IsConstructibleSheaf.biproduct _
  have : IsConstructibleSheaf (⨁ fun k : Fin n ↦ Q (WU k)) :=
    IsConstructibleSheaf.biproduct _
  have hA₀ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) A₀ :=
    IsConstructibleSheaf.of_iso (biproduct.isoCoproduct _)
      (F := ⨁ fun k : Fin m ↦ Q (WV k))
  have hB₀ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) B₀ :=
    IsConstructibleSheaf.of_iso (biproduct.isoCoproduct _)
      (F := ⨁ fun k : Fin n ↦ Q (WU k))
  have hAj : IsConstructibleEtaleModuleSheaf (t.obj A₀) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.upperStar (D.map (homOfLE h).op) A₀)
  have hBj : IsConstructibleEtaleModuleSheaf (t.obj B₀) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.upperStar (D.map (homOfLE h).op) B₀)
  refine ⟨j, t.obj A₀, t.obj B₀, a, hAj, hBj,
    (E.app A₀).symm ≪≫ eA, (E.app B₀).symm ≪≫ eB, ?_⟩
  change _ ≫ (E.inv.app B₀ ≫ eB.hom) = (E.inv.app A₀ ≫ eA.hom) ≫ f
  rw [← Category.assoc, ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl


end AlgebraicGeometry.Scheme
