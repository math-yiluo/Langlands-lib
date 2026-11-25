/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Transport of a scalar distributivity diagram
Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-cartesian-scalar-distributivity-transport). -/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorTransportComparison
    {C : Type*} [Category C] [CartesianMonoidalCategory C] [HasBinaryProducts C]
    {D : Type*} [Category D] [CartesianMonoidalCategory D] [HasBinaryProducts D]
    (F : C ⥤ D) [PreservesFiniteLimits F]
    (X Y : C) (X' Y' : D) (ex : X' ≅ F.obj X) (ey : Y' ≅ F.obj Y) :
    let eV := (limit.isLimit (pair X Y)).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    let eU := (limit.isLimit (pair X' Y')).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X' Y')
    eU.inv ≫ prod.map ex.hom ey.hom ≫ inv (prodComparison F X Y) ≫ F.map eV.hom =
      (ex.hom ⊗ₘ ey.hom) ≫ inv (CartesianMonoidalCategory.prodComparison F X Y) := by
  dsimp only
  have hvf := (limit.isLimit (pair X Y)).conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.left⟩
  have hvs := (limit.isLimit (pair X Y)).conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.right⟩
  have huf := (limit.isLimit (pair X' Y')).conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X' Y') ⟨WalkingPair.left⟩
  have hus := (limit.isLimit (pair X' Y')).conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X' Y') ⟨WalkingPair.right⟩
  change ((limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)).hom ≫
      CartesianMonoidalCategory.fst X Y = prod.fst at hvf
  change ((limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)).hom ≫
      CartesianMonoidalCategory.snd X Y = prod.snd at hvs
  change ((limit.isLimit (pair X' Y')).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X' Y')).inv ≫
      prod.fst = CartesianMonoidalCategory.fst X' Y' at huf
  change ((limit.isLimit (pair X' Y')).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X' Y')).inv ≫
      prod.snd = CartesianMonoidalCategory.snd X' Y' at hus
  rw [← cancel_mono (CartesianMonoidalCategory.prodComparison F X Y)]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
      ← F.map_comp]
    rw [hvf]
    simp only [inv_prodComparison_map_fst,
      CartesianMonoidalCategory.inv_prodComparison_map_fst, prod.map_fst,
      CartesianMonoidalCategory.tensorHom_fst]
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ ex.hom) huf
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd,
      ← F.map_comp]
    rw [hvs]
    simp only [inv_prodComparison_map_snd,
      CartesianMonoidalCategory.inv_prodComparison_map_snd, prod.map_snd,
      CartesianMonoidalCategory.tensorHom_snd]
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ ey.hom) hus

private theorem transportScalarDiagram
    {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {D : Type*} [Category D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal]
    (X Y : C) (X' Y' : D) (ex : X' ≅ F.obj X) (ey : Y' ≅ F.obj Y)
    (axV : X ⊗ X ⟶ X) (ayV : Y ⊗ Y ⟶ Y) (muV : X ⊗ Y ⟶ Y)
    (ax : X' ⊗ X' ⟶ X') (ay : Y' ⊗ Y' ⟶ Y') (mu : X' ⊗ Y' ⟶ Y')
    (hx : (ex.hom ⊗ₘ ex.hom) ≫ Functor.LaxMonoidal.μ F X X ≫
      F.map axV ≫ ex.inv = ax)
    (hy : (ey.hom ⊗ₘ ey.hom) ≫ Functor.LaxMonoidal.μ F Y Y ≫
      F.map ayV ≫ ey.inv = ay)
    (hm : (ex.hom ⊗ₘ ey.hom) ≫ Functor.LaxMonoidal.μ F X Y ≫
      F.map muV ≫ ey.inv = mu)
    (hsource :
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫ axV)
        (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ muV =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
            CartesianMonoidalCategory.fst X X)
          (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ muV)
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
            CartesianMonoidalCategory.snd X X)
          (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ muV) ≫ ayV) :
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst (X' ⊗ X') Y' ≫ ax)
      (CartesianMonoidalCategory.snd (X' ⊗ X') Y') ≫ mu =
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (X' ⊗ X') Y' ≫
          CartesianMonoidalCategory.fst X' X')
        (CartesianMonoidalCategory.snd (X' ⊗ X') Y') ≫ mu)
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (X' ⊗ X') Y' ≫
          CartesianMonoidalCategory.snd X' X')
        (CartesianMonoidalCategory.snd (X' ⊗ X') Y') ≫ mu) ≫ ay := by
  let p := CartesianMonoidalCategory.fst (X' ⊗ X') Y'
  let q := CartesianMonoidalCategory.snd (X' ⊗ X') Y'
  let r := p ≫ CartesianMonoidalCategory.fst X' X'
  let s := p ≫ CartesianMonoidalCategory.snd X' X'
  let t := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift (r ≫ ex.hom) (s ≫ ex.hom) ≫
      Functor.LaxMonoidal.μ F X X) (q ≫ ey.hom) ≫
        Functor.LaxMonoidal.μ F (X ⊗ X) Y
  have ht1 : t ≫ F.map (CartesianMonoidalCategory.fst (X ⊗ X) Y) =
      CartesianMonoidalCategory.lift (r ≫ ex.hom) (s ≫ ex.hom) ≫
        Functor.LaxMonoidal.μ F X X := by
    simp [t, Category.assoc]
  have ht2 : t ≫ F.map (CartesianMonoidalCategory.snd (X ⊗ X) Y) = q ≫ ey.hom := by
    simp [t, Category.assoc]
  have hlift {P Q T : C} (a : T ⟶ P) (b : T ⟶ Q)
      {Z : D} (c : Z ⟶ F.obj T) :
      c ≫ F.map (CartesianMonoidalCategory.lift a b) =
        CartesianMonoidalCategory.lift (c ≫ F.map a) (c ≫ F.map b) ≫
          Functor.LaxMonoidal.μ F P Q := by
    rw [← Functor.Monoidal.lift_μ]
    simp only [← Category.assoc, CartesianMonoidalCategory.comp_lift]
  have hh := congrArg (fun k ↦ t ≫ F.map k ≫ ey.inv) hsource
  simp only [Functor.map_comp, ← Category.assoc, hlift, ht1, ht2] at hh
  have hpair : CartesianMonoidalCategory.lift (r ≫ ex.hom) (s ≫ ex.hom) =
      p ≫ (ex.hom ⊗ₘ ex.hom) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [r, s]
  have hx' := congrArg (fun k ↦ k ≫ ex.hom) hx
  have hm' := congrArg (fun k ↦ k ≫ ey.hom) hm
  simp only [Category.assoc, ex.inv_hom_id, Category.comp_id] at hx'
  simp only [Category.assoc, ey.inv_hom_id, Category.comp_id] at hm'
  have hmlift {Z : D} (a : Z ⟶ X') (b : Z ⟶ Y') :
      CartesianMonoidalCategory.lift (a ≫ ex.hom) (b ≫ ey.hom) ≫
        Functor.LaxMonoidal.μ F X Y ≫ F.map muV =
          CartesianMonoidalCategory.lift a b ≫ mu ≫ ey.hom := by
    rw [← CartesianMonoidalCategory.lift_map, Category.assoc, hm']
  have haylift {Z : D} (a b : Z ⟶ Y') :
      CartesianMonoidalCategory.lift (a ≫ ey.hom) (b ≫ ey.hom) ≫
        Functor.LaxMonoidal.μ F Y Y ≫ F.map ayV ≫ ey.inv =
          CartesianMonoidalCategory.lift a b ≫ ay := by
    rw [← CartesianMonoidalCategory.lift_map, Category.assoc, hy]
  simp only [Category.assoc, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd,
    CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd] at hh
  simp only [hpair, Category.assoc, hx'] at hh
  simp only [hmlift] at hh
  have hleft := congrArg (fun k ↦ k ≫ ey.inv) (hmlift (p ≫ ax) q)
  have hright := haylift (CartesianMonoidalCategory.lift r q ≫ mu)
    (CartesianMonoidalCategory.lift s q ≫ mu)
  simp only [Category.assoc, ey.hom_inv_id, Category.comp_id] at hleft
  simp only [Category.assoc] at hright
  rw [hleft, hright] at hh
  simpa only [p, q, r, s] using hh

private theorem typesFst_apply {X Y : Type u} (z : X × Y) :
    (CartesianMonoidalCategory.fst X Y) z = z.1 := rfl

private theorem typesSnd_apply {X Y : Type u} (z : X × Y) :
    (CartesianMonoidalCategory.snd X Y) z = z.2 := rfl

private theorem typesLift_apply {X Y Z : Type u} (a : Z ⟶ X) (b : Z ⟶ Y) (z : Z) :
    (CartesianMonoidalCategory.lift a b) z = (a z, b z) := by
  apply Prod.ext
  · exact congrArg (fun k : Z ⟶ X ↦ k z) (CartesianMonoidalCategory.lift_fst a b)
  · exact congrArg (fun k : Z ⟶ Y ↦ k z) (CartesianMonoidalCategory.lift_snd a b)

private theorem presheafLift_app
    {C : Type*} [Category C] {X Y Z : C ⥤ Type u}
    (a : Z ⟶ X) (b : Z ⟶ Y) (W : C) :
    (CartesianMonoidalCategory.lift a b).app W =
      CartesianMonoidalCategory.lift (a.app W) (b.app W) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg (fun k : Z ⟶ X ↦ k.app W)
      (CartesianMonoidalCategory.lift_fst a b)
  · exact congrArg (fun k : Z ⟶ Y ↦ k.app W)
      (CartesianMonoidalCategory.lift_snd a b)

/-- Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-cartesian-scalar-distributivity-transport).

Proof: Regard the sectionwise hypothesis as equality of morphisms from
`(X tensor X) tensor Y` to Y, using the two projections to X and the projection
 to Y. Apply L to this equality. The comparison from each chosen tensor product
 to its image is invertible, since L preserves finite limits. Naturality of
 product comparisons carries projections and pairing to their target versions.
 Precompose with the comparison for the three-variable product and conjugate
 by ex and ey. The two assumed equations replace transported addition with ax
 and ay. Cancel the comparison isomorphisms. Evaluate the resulting morphism
 equality at ((r,s),x). This proves the displayed equality; no ring, group,
 adjunction, or module structures are needed. -/
theorem cartesianScalarDistributivityTransport
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits L]
    (X Y : Sheaf J (Type u)) (X' Y' : Sheaf K (Type u))
    (ex : X' ≅ L.obj X) (ey : Y' ≅ L.obj Y)
    (axV : X ⊗ X ⟶ X) (ayV : Y ⊗ Y ⟶ Y)
    (ax : X' ⊗ X' ⟶ X') (ay : Y' ⊗ Y' ⟶ Y')
    (muV : X ⨯ Y ⟶ Y) :
    let eV := fun (P Q : Sheaf J (Type u)) ↦
      (limit.isLimit (pair P Q)).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
    let eU := fun (P Q : Sheaf K (Type u)) ↦
      (limit.isLimit (pair P Q)).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
    let cx := (eU X' X').inv ≫ prod.map ex.hom ex.hom ≫
      inv (prodComparison L X X) ≫ L.map (eV X X).hom
    let cy := (eU Y' Y').inv ≫ prod.map ey.hom ey.hom ≫
      inv (prodComparison L Y Y) ≫ L.map (eV Y Y).hom
    let nuV := (eV X Y).inv ≫ muV
    let nu := (eU X' Y').inv ≫ prod.map ex.hom ey.hom ≫
      inv (prodComparison L X Y) ≫ L.map muV ≫ ey.inv
    cx ≫ L.map axV ≫ ex.inv = ax →
    cy ≫ L.map ayV ≫ ey.inv = ay →
    (∀ (W : Cᵒᵖ) (r s : X.obj.obj W) (x : Y.obj.obj W),
      nuV.hom.app W (axV.hom.app W (r, s), x) =
        ayV.hom.app W (nuV.hom.app W (r, x), nuV.hom.app W (s, x))) →
    ∀ (W : Dᵒᵖ) (r s : X'.obj.obj W) (x : Y'.obj.obj W),
      nu.hom.app W (ax.hom.app W (r, s), x) =
        ay.hom.app W (nu.hom.app W (r, x), nu.hom.app W (s, x)) := by
  dsimp only
  intro hx hy hs
  let : L.Monoidal := Functor.Monoidal.ofChosenFiniteProducts L
  have hμ (P Q : Sheaf J (Type u)) :
      Functor.LaxMonoidal.μ L P Q =
        inv (CartesianMonoidalCategory.prodComparison L P Q) := by
    rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory]
    apply (cancel_mono (CartesianMonoidalCategory.prodComparison L P Q)).1
    change (CartesianMonoidalCategory.prodComparisonIso L P Q).inv ≫
      (CartesianMonoidalCategory.prodComparisonIso L P Q).hom = _
    rw [IsIso.inv_hom_id]
    exact (CartesianMonoidalCategory.prodComparisonIso L P Q).inv_hom_id
  rw [tensorTransportComparison] at hx hy
  rw [← hμ] at hx hy
  let eV := (limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
  let eU := (limit.isLimit (pair X' Y')).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X' Y')
  let nuV := eV.inv ≫ muV
  let nu := eU.inv ≫ prod.map ex.hom ey.hom ≫
    inv (prodComparison L X Y) ≫ L.map muV ≫ ey.inv
  have hm : (ex.hom ⊗ₘ ey.hom) ≫ Functor.LaxMonoidal.μ L X Y ≫
      L.map nuV ≫ ey.inv = nu := by
    rw [hμ, ← Category.assoc, ← Category.assoc,
      ← tensorTransportComparison L X Y X' Y' ex ey]
    simp [nuV, nu, eV, eU, Functor.map_comp, Category.assoc]
  have hs' :
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫ axV)
        (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ nuV =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
            CartesianMonoidalCategory.fst X X)
          (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ nuV)
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
            CartesianMonoidalCategory.snd X X)
          (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ nuV) ≫ ayV := by
    ext W z
    simpa [typesFst_apply, typesSnd_apply, typesLift_apply, presheafLift_app, nuV, eV]
      using hs W z.1.1 z.1.2 z.2
  have ht := transportScalarDiagram L X Y X' Y' ex ey axV ayV nuV ax ay nu hx hy hm hs'
  intro W r s x
  have he := congrArg (fun k : (X' ⊗ X') ⊗ Y' ⟶ Y' ↦ k.hom.app W ((r, s), x)) ht
  simpa [typesFst_apply, typesSnd_apply, typesLift_apply, presheafLift_app, nu, eU] using he

end CategoryTheory
