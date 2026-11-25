/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Restricting an equivalence of full subcategories

An equivalence `e : PC.FullSubcategory ≌ QC.FullSubcategory` whose functor is identified with a
functor `F : C ⥤ D`, in the sense that `e.functor ⋙ QC.ι ≅ PC.ι ⋙ F`, restricts to an
equivalence of smaller full subcategories `P ≤ PC` and `Q ≤ QC` which `F` matches on `PC`.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D]

/-- Let `e : PC.FullSubcategory ≌ QC.FullSubcategory` be an equivalence with a commutative
square `α : e.functor ⋙ QC.ι ≅ PC.ι ⋙ F`. If `P ≤ PC`, `Q ≤ QC`, `Q` is closed under
isomorphisms and an object `K` with `PC K` satisfies `P` iff `F.obj K` satisfies `Q`, then
there is an equivalence `d : P.FullSubcategory ≌ Q.FullSubcategory` with
`d.functor ⋙ Q.ι ≅ P.ι ⋙ F`.

Proof: the functor `P.FullSubcategory ⥤ Q.FullSubcategory` induced by `F` is fully faithful,
being identified with the restriction of `e.functor`, and every object of `Q` is the image of
its `e`-preimage, which satisfies `P`. -/
theorem exists_equivalence_of_le
    (P PC : ObjectProperty C) (Q QC : ObjectProperty D)
    (F : C ⥤ D) (e : PC.FullSubcategory ≌ QC.FullSubcategory)
    (α : e.functor ⋙ QC.ι ≅ PC.ι ⋙ F)
    (hP : P ≤ PC) (hQ : Q ≤ QC)
    [Q.IsClosedUnderIsomorphisms]
    (hm : ∀ K, PC K → (P K ↔ Q (F.obj K))) :
    ∃ d : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (d.functor ⋙ Q.ι ≅ P.ι ⋙ F) := by
  let i := ObjectProperty.ιOfLE hP
  let G := Q.lift (P.ι ⋙ F) (fun K ↦ (hm K.obj (hP _ K.property)).mp K.property)
  let β : i ⋙ e.functor ⋙ QC.ι ≅ G ⋙ Q.ι := Functor.isoWhiskerLeft i α
  let h := ((Functor.FullyFaithful.ofFullyFaithful i).comp
    ((Functor.FullyFaithful.ofFullyFaithful e.functor).comp
      QC.fullyFaithfulι)).ofIso β
  let hG := Functor.FullyFaithful.ofCompFaithful h
  let : G.Full := hG.full
  let : G.Faithful := hG.faithful
  have : G.EssSurj := by
    constructor
    intro L
    let L' : QC.FullSubcategory := ⟨L.obj, hQ _ L.property⟩
    let K := e.inverse.obj L'
    let γ : F.obj K.obj ≅ L.obj :=
      (α.app K).symm ≪≫ QC.ι.mapIso (e.counitIso.app L')
    have hK : P K.obj := (hm K.obj K.property).mpr (Q.prop_of_iso γ.symm L.property)
    exact ⟨⟨K.obj, hK⟩, ⟨Q.fullyFaithfulι.preimageIso γ⟩⟩
  let : G.IsEquivalence := {}
  exact ⟨G.asEquivalence, ⟨Iso.refl _⟩⟩

end CategoryTheory.ObjectProperty
