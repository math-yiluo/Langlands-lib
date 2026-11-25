/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualNumbers

/-!
# First-order restriction along the diagonal

The diagonal of the dual-number thickening kills the mixed infinitesimal term.
Source: the square-zero pushout calculation in Stacks Project, Tag 0B2B,
proof of Lemma 33.16.2, applied locally over an arbitrary base ring.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme

private def diagonalRingHom {R : Type u} [CommRing R] :
    DualNumber (DualNumber R) →+* DualNumber R where
  toFun x := x.fst + TrivSqZeroExt.inr x.snd.fst
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [mul_add, add_mul]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [add_assoc, add_left_comm, add_comm]

private noncomputable def diagonalNatTrans : CommRingCat.dualNumber ⋙ CommRingCat.dualNumber ⟶
    CommRingCat.dualNumber where
  app R := CommRingCat.ofHom diagonalRingHom
  naturality R T f := by
    ext x : 2
    change diagonalRingHom (DualNumber.mapRingHom (DualNumber.mapRingHom f.hom) x) =
      DualNumber.mapRingHom f.hom (diagonalRingHom x)
    apply TrivSqZeroExt.ext
    · simp only [diagonalRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero,
        DualNumber.fst_mapRingHom]
    · simp only [diagonalRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, DualNumber.snd_mapRingHom,
        DualNumber.fst_mapRingHom]
      exact (map_add f.hom _ _).symm

private noncomputable def diagonalMap (S : Scheme.{u}) :
    S.dualNumbers ⟶ S.dualNumbers.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft S.presheaf diagonalNatTrans ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := S.dualNumbers.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    have h := (S.presheaf.isUnit_germ_dualNumber_iff x U hxU
      (diagonalRingHom g)).mp hs
    apply (S.dualNumbers.presheaf.isUnit_germ_dualNumber_iff x U hxU g).mpr
    apply (S.presheaf.isUnit_germ_dualNumber_iff x U hxU g.fst).mpr
    simpa [diagonalRingHom] using h

private theorem diagonalMap_proj₁ (S : Scheme.{u}) :
    diagonalMap S ≫ S.dualNumbers.dualNumbersProj = 𝟙 _ := by
  refine Scheme.Hom.ext rfl fun U => ?_
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  ext a : 2
  change diagonalRingHom (TrivSqZeroExt.inl a) = a
  ext <;> simp [diagonalRingHom]

private theorem diagonalMap_proj₂ (S : Scheme.{u}) :
    diagonalMap S ≫ S.dualNumbersProj.dualNumbers = 𝟙 _ := by
  refine Scheme.Hom.ext rfl fun U => ?_
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  ext a : 2
  change diagonalRingHom (DualNumber.mapRingHom (TrivSqZeroExt.inlHom _ _) a) = a
  ext <;> simp [diagonalRingHom]

private theorem ring_diagonal_apply {R : Type u} [CommRing R]
    (q : DualNumber (DualNumber R) →+* DualNumber R)
    (h₁ : ∀ y, q (TrivSqZeroExt.inl y) = y)
    (h₂ : ∀ y, q (DualNumber.mapRingHom (TrivSqZeroExt.inlHom R R) y) = y)
    (x : DualNumber (DualNumber R)) :
    q x = x.fst + TrivSqZeroExt.inr x.snd.fst := by
  have hi (r : R) : q (TrivSqZeroExt.inr (TrivSqZeroExt.inl r)) =
      TrivSqZeroExt.inr r := by
    simpa [DualNumber.mapRingHom] using h₂ (TrivSqZeroExt.inr r)
  have hm (r : R) : q (TrivSqZeroExt.inr (TrivSqZeroExt.inr r)) = 0 := by
    have e : (TrivSqZeroExt.inr (TrivSqZeroExt.inr r) : DualNumber (DualNumber R)) =
        TrivSqZeroExt.inl (TrivSqZeroExt.inr r) * TrivSqZeroExt.inr (TrivSqZeroExt.inl 1) := by
      ext <;> simp
    rw [e, map_mul, h₁, hi, TrivSqZeroExt.inr_mul_inr]
  have ex : x = TrivSqZeroExt.inl x.fst +
      TrivSqZeroExt.inr (TrivSqZeroExt.inl x.snd.fst) +
      TrivSqZeroExt.inr (TrivSqZeroExt.inr x.snd.snd) := by
    ext <;> simp
  rw [ex, map_add, map_add, h₁, hi, hm, add_zero]
  simp

private theorem iterated_axes (S Y : Scheme.{u})
    (f g : S.dualNumbers.dualNumbers ⟶ Y)
    (h₁ : S.dualNumbers.dualNumbersι ≫ f = S.dualNumbers.dualNumbersι ≫ g)
    (h₂ : S.dualNumbersι.dualNumbers ≫ f = S.dualNumbersι.dualNumbers ≫ g)
    (d : S.dualNumbers ⟶ S.dualNumbers.dualNumbers)
    (hd₁ : d ≫ S.dualNumbers.dualNumbersProj = 𝟙 _)
    (hd₂ : d ≫ S.dualNumbersProj.dualNumbers = 𝟙 _) : d ≫ f = d ≫ g := by
  have hb : f.base = g.base := by
    exact congrArg (fun k : S.dualNumbers ⟶ Y => k.base) h₁
  have hd : d.base = 𝟙 S.carrier := by
    exact congrArg (fun k : S.dualNumbers ⟶ S.dualNumbers => k.base) hd₁
  rcases f with ⟨⟨⟨fb, fc⟩, fp⟩⟩
  rcases g with ⟨⟨⟨gb, gc⟩, gp⟩⟩
  rcases d with ⟨⟨⟨db, dc⟩, dp⟩⟩
  change fb = gb at hb
  change db = 𝟙 S.carrier at hd
  subst gb
  subst db
  refine Scheme.Hom.ext rfl ?_
  intro U
  have e₁ := Scheme.Hom.congr_app h₁ U
  have e₂ := Scheme.Hom.congr_app h₂ U
  have ed₁ := Scheme.Hom.congr_app hd₁ ((TopologicalSpace.Opens.map fb).obj U)
  have ed₂ := Scheme.Hom.congr_app hd₂ ((TopologicalSpace.Opens.map fb).obj U)
  simp only [Scheme.Hom.comp_app] at e₁ e₂ ed₁ ed₂ ⊢
  simp only [eqToHom_op, eqToHom_map] at e₁ e₂ ed₁ ed₂ ⊢
  simp only [eqToHom_refl, Category.comp_id] at e₁ e₂ ed₁ ed₂ ⊢
  let R := Γ(S, (TopologicalSpace.Opens.map fb).obj U)
  change fc.app _ ≫ dc.app _ = gc.app _ ≫ dc.app _
  change fc.app _ ≫ CommRingCat.ofHom
      (TrivSqZeroExt.fstHom (DualNumber R) (DualNumber R) (DualNumber R)).toRingHom =
    gc.app _ ≫ CommRingCat.ofHom
      (TrivSqZeroExt.fstHom (DualNumber R) (DualNumber R) (DualNumber R)).toRingHom at e₁
  change fc.app _ ≫ CommRingCat.ofHom
      (DualNumber.mapRingHom (TrivSqZeroExt.fstHom R R R).toRingHom) =
    gc.app _ ≫ CommRingCat.ofHom
      (DualNumber.mapRingHom (TrivSqZeroExt.fstHom R R R).toRingHom) at e₂
  change CommRingCat.ofHom (TrivSqZeroExt.inlHom (DualNumber R) (DualNumber R)) ≫
    dc.app _ = 𝟙 _ at ed₁
  change CommRingCat.ofHom
      (DualNumber.mapRingHom (TrivSqZeroExt.inlHom R R)) ≫ dc.app _ = 𝟙 _ at ed₂
  ext a : 2
  have ef := congrArg (fun k => (k : Γ(Y, U) ⟶ CommRingCat.of (DualNumber R)) a) e₁
  have es := congrArg (fun k => (k : Γ(Y, U) ⟶ CommRingCat.of (DualNumber R)) a) e₂
  have q₁ (y : DualNumber R) := congrArg
    (fun k => (k : CommRingCat.of (DualNumber R) ⟶ CommRingCat.of (DualNumber R)) y) ed₁
  have q₂ (y : DualNumber R) := congrArg
    (fun k => (k : CommRingCat.of (DualNumber R) ⟶ CommRingCat.of (DualNumber R)) y) ed₂
  change (fc.app _ a).fst = (gc.app _ a).fst at ef
  change DualNumber.mapRingHom (TrivSqZeroExt.fstHom R R R).toRingHom (fc.app _ a) =
    DualNumber.mapRingHom (TrivSqZeroExt.fstHom R R R).toRingHom (gc.app _ a) at es
  have ess : (fc.app _ a).snd.fst = (gc.app _ a).snd.fst :=
    by simpa using congrArg TrivSqZeroExt.snd es
  let q := (dc.app (Opposite.op ((TopologicalSpace.Opens.map fb).obj U))).hom
  have hf := ring_diagonal_apply q q₁ q₂ (fc.app _ a)
  have hg := ring_diagonal_apply q q₁ q₂ (gc.app _ a)
  exact hf.trans ((congrArg₂
    (fun (x : DualNumber R) (y : R) => x + TrivSqZeroExt.inr y) ef ess).trans hg.symm)

/-- Maps out of the product of two dual-number thickenings which agree on both axes
agree on the diagonal.
Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, square-zero pushout calculation.
(blueprint: lem-ag-dual-numbers-diagonal)

Proof: use the iterated thickening, whose sections are double dual numbers, and the
comparison to the categorical product given by its two projections. On double dual
numbers the map `x ↦ x.fst + TrivSqZeroExt.inr x.snd.fst` identifies the two infinitesimals. It is a
natural ring homomorphism and induces a scheme morphism from the single to the double
thickening; locality follows because units are detected by the constant coefficient.
Its two projections are identities, so its composite with the comparison is the diagonal.
The composites of the two standard axes with the comparison are the categorical axes.

For maps from the iterated thickening, equality on the first axis identifies their base
maps and their first dual-number coefficients; equality on the second identifies the
remaining unmixed coefficient. Any ring map whose restrictions to the two inclusions
are identities kills the mixed coefficient: `inr (inr r)` is the product of
`inl (inr r)` and `inr (inl 1)`, which maps to the product of two square-zero terms.
Its value on a section is therefore `x.fst + inr x.snd.fst`. Apply this on every open of
the target, and use scheme-morphism extensionality. Pull the given maps back along the
comparison, apply this sectionwise equality, and transfer it to the slice by extensionality.
No affine cover, product isomorphism, or reducedness assumption is required.
-/
theorem dualNumbers_diagonal_comp_eq_of_axes (S : Scheme.{u}) (X : Over S)
    (f g : dualNumbersOver S ⊗ dualNumbersOver S ⟶ X)
    (h₁ : lift (𝟙 (dualNumbersOver S))
        (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S) ≫ f =
      lift (𝟙 (dualNumbersOver S))
        (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S) ≫ g)
    (h₂ : lift (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S)
        (𝟙 (dualNumbersOver S)) ≫ f =
      lift (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S)
        (𝟙 (dualNumbersOver S)) ≫ g) :
    lift (𝟙 (dualNumbersOver S)) (𝟙 (dualNumbersOver S)) ≫ f =
      lift (𝟙 (dualNumbersOver S)) (𝟙 (dualNumbersOver S)) ≫ g := by
  let k := lift (dualNumbersProjεOver S) (dualNumbersProjδOver S)
  have he₁ : dualNumbersιεOver S ≫ k =
      lift (𝟙 (dualNumbersOver S))
        (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [k, Category.assoc, lift_fst, lift_snd]
    · apply Over.OverMorphism.ext
      simp [dualNumbersιεOver, dualNumbersProjεOver]
    · apply Over.OverMorphism.ext
      simp [dualNumbersιεOver, dualNumbersProjδOver, Over.toUnit_left]
  have he₂ : dualNumbersιδOver S ≫ k =
      lift (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S)
        (𝟙 (dualNumbersOver S)) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [k, Category.assoc, lift_fst, lift_snd]
    · apply Over.OverMorphism.ext
      simp [dualNumbersιδOver, dualNumbersProjεOver, Over.toUnit_left]
    · apply Over.OverMorphism.ext
      simp [dualNumbersιδOver, dualNumbersProjδOver, ← Hom.dualNumbers_comp,
        Hom.dualNumbers_id]
  let d : dualNumbersOver S ⟶ dualNumbers₂Over S := Over.homMk (diagonalMap S) (by
    change diagonalMap S ≫ (S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj) =
      S.dualNumbersProj
    rw [← Category.assoc, diagonalMap_proj₁, Category.id_comp])
  have hd : d ≫ k = lift (𝟙 (dualNumbersOver S)) (𝟙 (dualNumbersOver S)) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [k, Category.assoc, lift_fst, lift_snd]
    · apply Over.OverMorphism.ext
      exact diagonalMap_proj₁ S
    · apply Over.OverMorphism.ext
      exact diagonalMap_proj₂ S
  rw [← hd, Category.assoc, Category.assoc]
  apply Over.OverMorphism.ext
  apply iterated_axes S X.left (k.left ≫ f.left) (k.left ≫ g.left)
    (d := diagonalMap S)
  · have h := he₁
    have e : dualNumbersιεOver S ≫ (k ≫ f) = dualNumbersιεOver S ≫ (k ≫ g) := by
      rw [← Category.assoc, ← Category.assoc, h]
      exact h₁
    exact congrArg (fun m => m.left) e
  · have h := he₂
    have e : dualNumbersιδOver S ≫ (k ≫ f) = dualNumbersιδOver S ≫ (k ≫ g) := by
      rw [← Category.assoc, ← Category.assoc, h]
      exact h₂
    exact congrArg (fun m => m.left) e
  · exact diagonalMap_proj₁ S
  · exact diagonalMap_proj₂ S

end AlgebraicGeometry.Scheme
