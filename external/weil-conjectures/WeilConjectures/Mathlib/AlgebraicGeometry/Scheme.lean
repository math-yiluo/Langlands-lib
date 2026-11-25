/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.CommRingCat
public import WeilConjectures.Mathlib.RingTheory.LocalRing.Basic

/-!
# Preimages of opens under a morphism of schemes

Mathlib records that taking preimages of opens commutes with arbitrary suprema
(`AlgebraicGeometry.Scheme.Hom.preimage_iSup`). Infima of opens are only intersections when
indexed by a finite type, and in that case preimages commute with them as well:

- `AlgebraicGeometry.Scheme.Hom.preimage_iInf`.

We also record that a global section whose non-vanishing locus is everything is a unit:

- `AlgebraicGeometry.Scheme.isUnit_of_basicOpen_eq_top`.

and that the zero locus of `insert a s` is the intersection of the zero loci of `a` and `s`:

- `AlgebraicGeometry.Scheme.zeroLocus_insert`.

At a point `g : Spec R ⟶ Y` with values in a field, a global function `a` does not vanish iff the
point lies in `D(a)`:

- `AlgebraicGeometry.Scheme.Hom.appTop_ne_zero_iff_mem_basicOpen`.

# Complements on schemes

* `AlgebraicGeometry.Scheme.basicOpen_prod`,
  `AlgebraicGeometry.Scheme.iInf_basicOpen_eq_basicOpen_prod`: the basic open of a finite
  product of sections is the intersection of the basic opens.
* `AlgebraicGeometry.Scheme.isUnit_of_le_basicOpen`: if `U ≤ X.basicOpen f` for a section
  `f : Γ(X, U)`, then `f` is a unit. This is the converse of `Scheme.basicOpen_of_isUnit`.
* `AlgebraicGeometry.Scheme.Hom.range_appLE_subset_of_comp_eq`: sections in the image of
  `appLE` of a composition are in the image of `appLE` of its first factor.
* `AlgebraicGeometry.Scheme.Hom.appLE_eq_of_eq`: rewriting `appLE` along an equality of
  morphisms.
* `AlgebraicGeometry.Scheme.connectedSpace_iff_isIdempotentElem`: a nonempty scheme is connected
  if and only if its only idempotent global sections are `0` and `1`.
* `AlgebraicGeometry.Scheme.IsSpecOfField`: the scheme is isomorphic to the spectrum of a
  field, with the instance `AlgebraicGeometry.Scheme.isSpecOfField_Spec` for `Spec k`.

# The inverse image of the structure sheaf

For a morphism of schemes `f : X ⟶ S`:

* `AlgebraicGeometry.Scheme.Hom.pullbackPresheaf`: the presheaf inverse image `f⁻¹𝒪_S`, a
  presheaf of commutative rings on `X`.
* `AlgebraicGeometry.Scheme.Hom.pullbackPresheafToPresheaf`: the morphism `f⁻¹𝒪_S ⟶ 𝒪_X`
  adjoint to `f♯ : 𝒪_S ⟶ f_*𝒪_X`.
* `AlgebraicGeometry.Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app`: `f.appLE U V e` factors
  through `(f⁻¹𝒪_S)(V)`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Taking preimages of opens commutes with finite infima. -/
lemma preimage_iInf {ι : Type*} [Finite ι] (U : ι → Y.Opens) :
    f ⁻¹ᵁ ⨅ i, U i = ⨅ i, f ⁻¹ᵁ U i :=
  Opens.ext <| by
    simp only [coe_preimage, Opens.coe_iInf, Set.preimage_iInter]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- A global section that vanishes nowhere is a unit. -/
lemma isUnit_of_basicOpen_eq_top {X : Scheme.{u}} (f : Γ(X, ⊤)) (h : X.basicOpen f = ⊤) :
    IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ ⊤ f fun x _ ↦ ?_
  exact (X.mem_basicOpen_top f x).mp (h.ge trivial)

/-- The zero locus of `insert a s` is the intersection of the zero loci of `a` and of `s`. -/
lemma zeroLocus_insert {X : Scheme.{u}} {U : X.Opens} (a : Γ(X, U)) (s : Set Γ(X, U)) :
    X.zeroLocus (insert a s) = X.zeroLocus {a} ∩ X.zeroLocus s := by
  ext x
  simp

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- A section of a scheme that is invertible at every point of its domain is a unit.
This is the converse of `Scheme.basicOpen_of_isUnit`. -/
theorem isUnit_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens} {f : Γ(X, U)}
    (h : U ≤ X.basicOpen f) : IsUnit f :=
  X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx ↦ (X.mem_basicOpen f x hx).mp (h hx)

/-- The `appLE` of a morphism between the top opens is its `appTop`. -/
lemma Hom.appLE_top_top {T T' : Scheme.{u}} (q : T ⟶ T')
    (h : (⊤ : T.Opens) ≤ q ⁻¹ᵁ ⊤) : q.appLE ⊤ ⊤ h = q.appTop := by
  simp [Scheme.Hom.appLE]

/-- `Spec` of a ring map acts on global sections by the ring map. -/
lemma specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- Multiplicativity of the inverse of `ΓSpecIso`. -/
lemma ΓSpecIso_inv_mul {R : CommRingCat.{u}} (r s : R) :
    (Scheme.ΓSpecIso R).inv r * (Scheme.ΓSpecIso R).inv s = (Scheme.ΓSpecIso R).inv (r * s) :=
  (map_mul _ _ _).symm
/-- If `f ≫ g = h`, then every section in the image of `h.appLE` also lies in the image of
`f.appLE`. -/
lemma Hom.range_appLE_subset_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hcomp : f ≫ g = h) {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) :
    Set.range (h.appLE U W e₃) ⊆ Set.range (f.appLE V W e₂) := by
  subst hcomp
  rintro _ ⟨x, rfl⟩
  exact ⟨g.appLE U V e₁ x, by rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]⟩

/-- A scheme `S` *is the spectrum of a field* if it is isomorphic to `Spec k` for some field
`k`. -/
class IsSpecOfField (S : Scheme.{u}) : Prop where
  exists_iso : ∃ (k : Type u) (_ : Field k), Nonempty (S ≅ Spec (.of k))

/-- The spectrum of a field is the spectrum of a field. -/
instance isSpecOfField_Spec (k : Type u) [Field k] : (Spec (.of k)).IsSpecOfField :=
  ⟨⟨k, inferInstance, ⟨Iso.refl _⟩⟩⟩

/-- Being the spectrum of a field is invariant under isomorphism. -/
lemma IsSpecOfField.of_iso {S T : Scheme.{u}} (e : S ≅ T) [T.IsSpecOfField] :
    S.IsSpecOfField :=
  let ⟨k, _, ⟨e'⟩⟩ := IsSpecOfField.exists_iso (S := T)
  ⟨⟨k, inferInstance, ⟨e ≪≫ e'⟩⟩⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The presheaf inverse image `f⁻¹𝒪_S` of the structure sheaf of `S`, a presheaf of
commutative rings on `X`. -/
noncomputable abbrev pullbackPresheaf : TopCat.Presheaf CommRingCat.{u} X :=
  (TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf

/-- The morphism `f⁻¹𝒪_S ⟶ 𝒪_X` of presheaves of commutative rings on `X`, the transpose of
`f♯ : 𝒪_S ⟶ f_*𝒪_X` under the adjunction `f⁻¹ ⊣ f_*`:
```
  𝒪_S ──f♯──▶ f_* 𝒪_X          (on S)
  ─────────────────────
  f⁻¹𝒪_S ─────▶ 𝒪_X            (on X)
```
-/
noncomputable def pullbackPresheafToPresheaf : f.pullbackPresheaf ⟶ X.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv _ _).symm f.c

/-- `f♯` is the adjunction unit followed by the pushforward of `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
@[reassoc (attr := simp)]
lemma unit_app_comp_pushforward_map_pullbackPresheafToPresheaf :
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app S.presheaf ≫
      (TopCat.Presheaf.pushforward CommRingCat f.base).map f.pullbackPresheafToPresheaf = f.c :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The map `f.appLE U V e : Γ(S, U) ⟶ Γ(X, V)` factors through `(f⁻¹𝒪_S)(V)`. -/
lemma appLE_eq_pullbackPresheafToPresheaf_app (U : S.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
          S.presheaf).app (Opposite.op U) ≫
        f.pullbackPresheaf.map (homOfLE e).op ≫
          f.pullbackPresheafToPresheaf.app (Opposite.op V) := by
  rw [f.pullbackPresheafToPresheaf.naturality, ← Category.assoc]
  have := NatTrans.congr_app f.unit_app_comp_pushforward_map_pullbackPresheafToPresheaf
    (Opposite.op U)
  rw [NatTrans.comp_app] at this
  erw [this]
  rfl

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- The basic open of a finite product of sections is the intersection of the basic opens. -/
lemma Scheme.basicOpen_prod {X : Scheme.{u}} {V : X.Opens} {ι : Type*} (s : Finset ι)
    (g : ι → Γ(X, V)) : X.basicOpen (∏ i ∈ s, g i) = V ⊓ ⨅ i ∈ s, X.basicOpen (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.basicOpen_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.iInf_insert, inf_left_comm,
      inf_eq_right.2 ((inf_le_left).trans (X.basicOpen_le _))]

/-- A nonempty finite intersection of basic opens is the basic open of the product. -/
lemma Scheme.iInf_basicOpen_eq_basicOpen_prod {X : Scheme.{u}} {V : X.Opens} {ι : Type*}
    [Fintype ι] [Nonempty ι] (g : ι → Γ(X, V)) :
    ⨅ i, X.basicOpen (g i) = X.basicOpen (∏ i, g i) := by
  rw [Scheme.basicOpen_prod]
  simp only [Finset.mem_univ, iInf_pos]
  exact (inf_eq_right.2 ((iInf_le _ (Classical.arbitrary ι)).trans (X.basicOpen_le _))).symm

/-- Composition of restriction maps of the structure sheaf, elementwise. -/
lemma Scheme.presheaf_map_homOfLE_map_homOfLE_apply {X : Scheme.{u}} {U V W : X.Opens}
    (h₁ : U ≤ V) (h₂ : V ≤ W) (a : Γ(X, W)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op a) =
      X.presheaf.map (homOfLE (h₁.trans h₂)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The global sections of the spectrum of a field form a field. -/
lemma isField_Γ_Spec {R : CommRingCat.{u}} (hR : IsField R) : IsField Γ(Spec R, ⊤) :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.isField hR

/-- For a point `g : Spec R ⟶ Y` of a scheme with values in a field, a global function `a` of `Y`
does not vanish at the point, `g^♯ a ≠ 0`, if and only if the point lies in `D(a)`. -/
lemma Hom.appTop_ne_zero_iff_mem_basicOpen {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (hR : IsField Γ(Spec R, ⊤)) (g : Spec R ⟶ Y) (a : Γ(Y, ⊤)) (x : Spec R) :
    g.appTop a ≠ 0 ↔ g.base x ∈ Y.basicOpen a := by
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen_top]
  let := hR.toField
  by_cases h : g.appTop a = 0
  · rw [h, Scheme.basicOpen_zero]
    simp
  · rw [Scheme.basicOpen_of_isUnit (X := Spec R) (Ne.isUnit h)]
    simpa using h

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open Opposite

/-- A nonempty scheme is connected if and only if its only idempotent global sections are `0`
and `1`. An idempotent `e` cuts `X` into the two disjoint opens `D(e)` and `D(1 - e)`; conversely
a clopen `U` gives the idempotent which is `1` on `U` and `0` on its complement. -/
theorem connectedSpace_iff_isIdempotentElem (X : Scheme.{u}) [Nonempty X] :
    ConnectedSpace X ↔ ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  classical
  have ext (a b : Γ(X, ⊤))
      (h : ∀ x, X.presheaf.germ ⊤ x trivial a = X.presheaf.germ ⊤ x trivial b) : a = b :=
    TopCat.Presheaf.section_ext X.sheaf ⊤ a b fun x _ ↦ h x
  rw [connectedSpace_iff_clopen]
  refine ⟨fun ⟨_, H⟩ e he ↦ ?_, fun H ↦ ⟨inferInstance, fun S hS ↦ ?_⟩⟩
  · have hgerm (x : X) := IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
      (he.map (X.presheaf.germ ⊤ x trivial).hom)
    have hcompl : (X.basicOpen e : Set X)ᶜ = X.basicOpen (1 - e) := by
      ext x
      simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_basicOpen_top, map_sub, map_one]
      rcases hgerm x with h | h <;> simp [h]
    have hclopen : IsClopen (X.basicOpen e : Set X) :=
      ⟨isOpen_compl_iff.mp (hcompl ▸ (X.basicOpen (1 - e)).isOpen), (X.basicOpen e).isOpen⟩
    refine (H _ hclopen).imp (fun h ↦ ext _ _ fun x ↦ ?_) (fun h ↦ ext _ _ fun x ↦ ?_)
    · have hx : x ∉ X.basicOpen e := by simp [← SetLike.mem_coe, h]
      rw [mem_basicOpen_top] at hx
      rcases hgerm x with h | h
      · simpa using h
      · exact absurd (by simp [h]) hx
    · have hx : x ∈ X.basicOpen e := by simp [← SetLike.mem_coe, h]
      rw [mem_basicOpen_top] at hx
      rcases hgerm x with h | h
      · exact absurd hx (by simp [h])
      · simpa using h
  · let U : X.Opens := ⟨S, hS.isOpen⟩
    let V : X.Opens := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
    have hUV : U ⊔ V = ⊤ := by ext x; simp [U, V]
    have hUV' : U ⊓ V = ⊥ := by ext x; simp [U, V]
    let s : Γ(X, U ⊔ V) := (X.sheaf.objSupIsoProdEqLocus U V).inv ⟨(1, 0),
      TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx ↦ by
        rw [hUV'] at hx; exact absurd hx (by simp)⟩
    let e : Γ(X, ⊤) := X.presheaf.map (eqToHom hUV.symm).op s
    have hsU : X.presheaf.map (homOfLE le_sup_left).op s = 1 :=
      X.sheaf.objSupIsoProdEqLocus_inv_fst U V _
    have hsV : X.presheaf.map (homOfLE le_sup_right).op s = 0 :=
      X.sheaf.objSupIsoProdEqLocus_inv_snd U V _
    have heU : X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op e = 1 := by
      rw [← hsU, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have heV : X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op e = 0 := by
      rw [← hsV, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have hgerm (x : X) : X.presheaf.germ ⊤ x trivial e = if x ∈ S then 1 else 0 := by
      split_ifs with hx
      · rw [← X.presheaf.germ_res (homOfLE le_top : U ⟶ ⊤) x hx, CommRingCat.comp_apply, heU,
          map_one]
      · rw [← X.presheaf.germ_res (homOfLE le_top : V ⟶ ⊤) x hx, CommRingCat.comp_apply, heV,
          map_zero]
    have he : IsIdempotentElem e := ext _ _ fun x ↦ by
      rw [map_mul, hgerm]; split_ifs <;> simp
    refine (H e he).imp (fun h ↦ ?_) (fun h ↦ ?_)
    · refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
      have := hgerm x
      rw [h, map_zero, ite_eq_left hx] at this
      exact zero_ne_one this
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      by_contra hx
      have := hgerm x
      rw [h, map_one, ite_eq_right hx] at this
      exact one_ne_zero this

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

/-- Rewriting `appLE` along an equality of morphisms. -/
lemma appLE_eq_of_eq {T T' : Scheme.{u}} {f g : T ⟶ T'} (hfg : f = g) (U : T'.Opens)
    (V' : T.Opens) (e : V' ≤ f ⁻¹ᵁ U) :
    f.appLE U V' e = g.appLE U V' (hfg ▸ e) := by
  subst hfg
  rfl

end AlgebraicGeometry.Scheme.Hom
