/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Localization description of an affine pushforward stalk

Source: Stacks Project, Tag 0AVW, affine stalk calculation.
(blueprint: lem-sc-affine-pushforward-stalk-localization)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- On an affine neighborhood, the pushforward stalk is the localization of the
sections of its inverse image at the images of functions not vanishing at the point.
Source: Stacks Project, Tag 0AVW, affine stalk calculation.
(blueprint: lem-sc-affine-pushforward-stalk-localization)

Proof: Put B = Γ(Y,U), A = Γ(X,f⁻¹U), and q = hU.primeIdealOf y. The distinguished
opens D(b), b ∉ q, are cofinal among neighborhoods of y inside U. Their inverse
images are the distinguished opens D(f.app U b) in the affine open f⁻¹U. Their
section rings are A localized at f.app U b, compatibly with the restriction maps.
Consequently their filtered colimit, the pushforward stalk at y, is A localized
at the submonoid consisting of the images of B minus q. The map from A into this
colimit is exactly the germ map. Equivalently the images of the submonoid are
units, every stalk element has a numerator in A and a denominator in that
submonoid, and a numerator with zero germ is killed by a member of that submonoid.
These are the three defining properties of IsLocalization. This also covers
an empty inverse image, where A and the stalk are the zero ring. -/
theorem affine_pushforward_stalk_isLocalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {U : Y.Opens} (hU : IsAffineOpen U) (y : U) :
    let F := (TopCat.Presheaf.pushforward CommRingCat f.base).obj X.presheaf
    letI : Algebra (X.presheaf.obj (op (f ⁻¹ᵁ U))) (F.stalk y) :=
      (F.germ U y y.property).hom.toAlgebra
    IsLocalization
      ((hU.primeIdealOf y).asIdeal.primeCompl.map (f.app U).hom) (F.stalk y) := by
  dsimp only
  let F := (TopCat.Presheaf.pushforward CommRingCat f.base).obj X.presheaf
  let A := X.presheaf.obj (op (f ⁻¹ᵁ U))
  let M := (hU.primeIdealOf y).asIdeal.primeCompl.map (f.app U).hom
  let S := F.stalk y
  let : Algebra A S := (F.germ U y y.property).hom.toAlgebra
  have hyunit (b : Y.presheaf.obj (op U)) :
      y.val ∈ Y.basicOpen b ↔ b ∈ (hU.primeIdealOf y).asIdeal.primeCompl := by
    have := hU.isLocalization_stalk y
    rw [Y.mem_basicOpen b y y.property]
    exact IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (hU.primeIdealOf y).asIdeal b
  refine (isLocalization_iff M S).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨v, hv⟩
    obtain ⟨b, hb, rfl⟩ := hv
    have := hU.isLocalization_stalk y
    have hu := IsLocalization.map_units (Y.presheaf.stalk y) ⟨b, hb⟩
    change IsUnit (F.germ U y y.property (f.app U b))
    have hh := hu.map ((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c).hom
    change IsUnit (((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c)
      (Y.presheaf.germ U y y.property b)) at hh
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hh
    exact hh
  · intro z
    obtain ⟨V, hyV, z, rfl⟩ := F.exists_germ_eq z
    obtain ⟨b, hbV, hyb⟩ := hU.exists_basicOpen_le ⟨y, hyV⟩ y.property
    let W := Y.basicOpen b
    let j : W ⟶ V := homOfLE hbV
    let i : W ⟶ U := homOfLE (Y.basicOpen_le b)
    let z' := F.map j.op z
    have hz : F.germ W y hyb z' = F.germ V y hyV z := F.germ_res_apply j y hyb z
    let : Algebra A (F.obj (op W)) := (F.map i.op).hom.toAlgebra
    have hl := (hU.preimage f).isLocalization_of_eq_basicOpen
      (f.app U b) ((TopologicalSpace.Opens.map f.base).map i) (f.preimage_basicOpen b)
    have : IsLocalization.Away (f.app U b) (F.obj (op W)) := hl
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (f.app U b)) z'
    refine ⟨⟨a, ⟨f.app U b, ⟨b, (hyunit b).mp hyb, rfl⟩⟩ ^ n⟩, ?_⟩
    change F.germ V y hyV z * (F.germ U y y.property).hom ((f.app U b) ^ n) =
      (F.germ U y y.property).hom a
    rw [← hz]
    have hg (a : A) : F.germ U y y.property a = F.germ W y hyb (F.map i.op a) :=
      (F.germ_res_apply i y hyb a).symm
    rw [hg, hg, ← map_mul]
    exact congrArg (fun a ↦ F.germ W y hyb a) ha
  · intro a b hab
    obtain ⟨V, hyV, i, j, he⟩ := F.germ_eq y y.property y.property a b hab
    obtain ⟨c, hcV, hyc⟩ := hU.exists_basicOpen_le ⟨y, hyV⟩ y.property
    let W := Y.basicOpen c
    let k : W ⟶ V := homOfLE hcV
    let l : W ⟶ U := homOfLE (Y.basicOpen_le c)
    have he' : F.map l.op a = F.map l.op b := by
      have hh := congrArg (fun z ↦ F.map k.op z) he
      have hi : i.op ≫ k.op = l.op := Subsingleton.elim _ _
      have hj : j.op ≫ k.op = l.op := Subsingleton.elim _ _
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hi, hj] using hh
    let : Algebra A (F.obj (op W)) := (F.map l.op).hom.toAlgebra
    have hl := (hU.preimage f).isLocalization_of_eq_basicOpen
      (f.app U c) ((TopologicalSpace.Opens.map f.base).map l) (f.preimage_basicOpen c)
    have : IsLocalization.Away (f.app U c) (F.obj (op W)) := hl
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (f.app U c)) he'
    refine ⟨⟨f.app U c, ⟨c, (hyunit c).mp hyc, rfl⟩⟩ ^ n, ?_⟩
    exact hn

end AlgebraicGeometry
