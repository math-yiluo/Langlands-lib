/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist

/-!
# Algebras for an endofunctor which permutes the pieces of a decomposition cyclically

Let `F : C ⥤ C` and `G : D ⥤ D` be endofunctors and let `J₀, …, J_m : C ⥤ D` be functors which
decompose `C`, in the sense that `C ⥤ (Fin (m + 1) → D)`, `X ↦ (J_i X)_i` is an equivalence.
Assume that `F` permutes the pieces cyclically: `J_i ∘ F ≅ J_{i+1}` for `i < m`, and
`J_m ∘ F ≅ G ∘ J₀`. Then an algebra `(A, φ : F A ≅ A)` is determined by its piece `J₀ A` with
the structure isomorphism
```
G (J₀ A) ≅ J_m (F A) --J_m φ--> J_m A ≅ J_{m-1} (F A) --J_{m-1} φ--> J_{m-1} A ≅ ⋯ ≅ J₀ A,
```
and `(A, φ) ↦ (J₀ A, ψ_A)` is an equivalence `IsoAlgebra F ≌ IsoAlgebra G`
(`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition.functor_isEquivalence`).

This is the shape of Weil sheaves on a scheme `V` over a finite field `k₀` whose constant field is
a larger finite field `k'`: the geometric fibre `V ⊗_{k₀} k̄` is the disjoint union of the
`r = [k' : k₀]` conjugates of `V ⊗_{k'} k̄`, permuted cyclically by the Frobenius.
-/

@[expose] public section

noncomputable section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A decomposition of `C` into `m + 1` pieces, each a copy of `D`, which an endofunctor `F` of
`C` permutes cyclically, up to the endofunctor `G` of `D` on the last step:
`J_i ∘ F ≅ J_{i+1}` for `i < m`, `J_m ∘ F ≅ G ∘ J₀`, and `X ↦ (J_i X)_i` is an equivalence
`C ≌ (Fin (m + 1) → D)`. -/
structure CyclicDecomposition (F : C ⥤ C) (G : D ⥤ D) (m : ℕ) where
  /-- The pieces. -/
  J : Fin (m + 1) → C ⥤ D
  /-- `F` moves the piece `i` to the piece `i + 1`. -/
  α : ∀ k : Fin m, F ⋙ J k.castSucc ≅ J k.succ
  /-- `F` moves the last piece to the first one, up to `G`. -/
  β : F ⋙ J (Fin.last m) ≅ J 0 ⋙ G
  /-- The pieces determine the morphisms. -/
  fullyFaithful : (Functor.pi' J).FullyFaithful
  /-- Every family of objects of the pieces comes from an object. -/
  essSurj : (Functor.pi' J).EssSurj

namespace CyclicDecomposition

variable {F : C ⥤ C} {G : D ⥤ D} {m : ℕ} (P : CyclicDecomposition F G m)

/-- The identification `J_i A ≅ J₀ A` of the pieces of an algebra through its structure
isomorphism: `J_{k+1} A ≅ J_k (F A) --J_k φ--> J_k A ≅ ⋯ ≅ J₀ A`. -/
def chain (A : IsoAlgebra F) (i : Fin (m + 1)) : (P.J i).obj A.carrier ≅ (P.J 0).obj A.carrier :=
  Fin.induction (motive := fun i ↦ (P.J i).obj A.carrier ≅ (P.J 0).obj A.carrier) (Iso.refl _)
    (fun k c ↦ ((P.α k).app A.carrier).symm ≪≫ (P.J k.castSucc).mapIso A.str ≪≫ c) i

@[simp]
lemma chain_zero (A : IsoAlgebra F) : P.chain A 0 = Iso.refl _ :=
  rfl

lemma chain_succ (A : IsoAlgebra F) (k : Fin m) :
    P.chain A k.succ =
      ((P.α k).app A.carrier).symm ≪≫ (P.J k.castSucc).mapIso A.str ≪≫ P.chain A k.castSucc :=
  rfl

/-- The pieces of a morphism of algebras are determined by its first piece. -/
lemma chain_hom_naturality {A B : IsoAlgebra F} (f : A ⟶ B) (i : Fin (m + 1)) :
    (P.chain A i).hom ≫ (P.J 0).map f.hom.f = (P.J i).map f.hom.f ≫ (P.chain B i).hom := by
  induction i using Fin.induction with
  | zero => simp
  | succ k ih =>
    have hα := (P.α k).inv.naturality f.hom.f
    have hf := f.hom.h
    simp only [Functor.comp_map] at hα
    simp only [chain_succ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
      Category.assoc, ih]
    rw [reassoc_of% hα, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, str_hom, str_hom,
      hf]

/-- The structure isomorphism `G (J₀ A) ≅ J₀ A` of the first piece of an algebra. -/
def strZero (A : IsoAlgebra F) : G.obj ((P.J 0).obj A.carrier) ≅ (P.J 0).obj A.carrier :=
  (P.β.app A.carrier).symm ≪≫ (P.J (Fin.last m)).mapIso A.str ≪≫ P.chain A (Fin.last m)

/-- The first piece of an algebra, with its induced structure isomorphism. -/
def firstPiece (A : IsoAlgebra F) : IsoAlgebra G :=
  IsoAlgebra.mk ((P.J 0).obj A.carrier) (P.strZero A)

lemma strZero_hom_naturality {A B : IsoAlgebra F} (f : A ⟶ B) :
    G.map ((P.J 0).map f.hom.f) ≫ (P.strZero B).hom =
      (P.strZero A).hom ≫ (P.J 0).map f.hom.f := by
  have hβ := P.β.inv.naturality f.hom.f
  have hf := f.hom.h
  simp only [Functor.comp_map] at hβ
  simp only [strZero, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc, P.chain_hom_naturality f]
  rw [reassoc_of% hβ, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, str_hom, str_hom,
    hf]

/-- **The first piece of an algebra**: `(A, φ) ↦ (J₀ A, ψ_A)`. -/
def functor : IsoAlgebra F ⥤ IsoAlgebra G where
  obj := P.firstPiece
  map f := ObjectProperty.homMk
    { f := (P.J 0).map f.hom.f
      h := P.strZero_hom_naturality f }
  map_id _ := hom_ext ((P.J 0).map_id _)
  map_comp _ _ := hom_ext ((P.J 0).map_comp _ _)

@[simp]
lemma functor_obj_carrier (A : IsoAlgebra F) :
    (P.functor.obj A).carrier = (P.J 0).obj A.carrier :=
  rfl

@[simp]
lemma functor_map_hom_f {A B : IsoAlgebra F} (f : A ⟶ B) :
    (P.functor.map f).hom.f = (P.J 0).map f.hom.f :=
  rfl

/-- The pieces of a morphism of algebras, in terms of its first piece. -/
lemma map_eq {A B : IsoAlgebra F} (f : A ⟶ B) (i : Fin (m + 1)) :
    (P.J i).map f.hom.f = (P.chain A i).hom ≫ (P.J 0).map f.hom.f ≫ (P.chain B i).inv := by
  rw [reassoc_of% P.chain_hom_naturality f i, Iso.hom_inv_id, Category.comp_id]

/-- A morphism of `C` with prescribed pieces. -/
def preimageFamily {X Y : C} (g : ∀ i, (P.J i).obj X ⟶ (P.J i).obj Y) : X ⟶ Y :=
  P.fullyFaithful.preimage (X := X) (Y := Y) g

@[simp]
lemma map_preimageFamily {X Y : C} (g : ∀ i, (P.J i).obj X ⟶ (P.J i).obj Y) (i : Fin (m + 1)) :
    (P.J i).map (P.preimageFamily g) = g i :=
  congrFun (P.fullyFaithful.map_preimage (X := X) (Y := Y) g) i

lemma hom_ext' {X Y : C} {f f' : X ⟶ Y} (h : ∀ i, (P.J i).map f = (P.J i).map f') : f = f' :=
  P.fullyFaithful.map_injective (funext h)

/-- The functor taking the first piece is faithful and full. -/
def functorFullyFaithful : P.functor.FullyFaithful where
  preimage {A B} g := ObjectProperty.homMk
    { f := P.preimageFamily fun i ↦ (P.chain A i).hom ≫ g.hom.f ≫ (P.chain B i).inv
      h := by
        set φ := P.preimageFamily fun i ↦ (P.chain A i).hom ≫ g.hom.f ≫ (P.chain B i).inv
        have hJ (i : Fin (m + 1)) :
            (P.J i).map φ = (P.chain A i).hom ≫ g.hom.f ≫ (P.chain B i).inv :=
          P.map_preimageFamily _ i
        have hg : G.map g.hom.f = (P.strZero A).hom ≫ g.hom.f ≫ (P.strZero B).inv := by
          have h := g.hom.h
          change G.map g.hom.f ≫ (P.strZero B).hom = (P.strZero A).hom ≫ g.hom.f at h
          rw [← reassoc_of% h]
          simp
        refine P.hom_ext' fun i ↦ ?_
        simp only [Functor.map_comp]
        induction i using Fin.lastCases with
        | last =>
          have e : (P.J (Fin.last m)).map (F.map φ) =
              (P.β.app A.carrier).hom ≫ G.map ((P.J 0).map φ) ≫ (P.β.app B.carrier).inv := by
            rw [← cancel_mono (P.β.app B.carrier).hom]
            simpa using P.β.hom.naturality φ
          have h0 : (P.J 0).map φ = g.hom.f := by simpa using hJ 0
          rw [e, h0, hJ, hg]
          simp [strZero]
          simp only [← str_hom, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
            Category.comp_id]
        | cast k =>
          have e : (P.J k.castSucc).map (F.map φ) =
              ((P.α k).app A.carrier).hom ≫ (P.J k.succ).map φ ≫
                ((P.α k).app B.carrier).inv := by
            rw [← cancel_mono ((P.α k).app B.carrier).hom]
            simp
          rw [e, hJ, hJ]
          simp [chain_succ]
          simp only [← str_hom, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
            Category.comp_id] }
  map_preimage {A B} g := hom_ext <| by
    simp only [functor_map_hom_f, ObjectProperty.homMk_hom, map_preimageFamily, chain_zero,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    exact Category.comp_id _
  preimage_map {A B} f := hom_ext <| P.hom_ext' fun i ↦ by
    simp only [ObjectProperty.homMk_hom, map_preimageFamily, functor_map_hom_f]
    exact (P.map_eq f i).symm

section EssSurj

variable (Y : IsoAlgebra G)

/-- An object of `C` all of whose pieces are the carrier of `Y`. -/
def preimageCarrier : C :=
  have := P.essSurj
  (Functor.pi' P.J).objPreimage fun _ ↦ Y.carrier

/-- The pieces of `preimageCarrier Y` are the carrier of `Y`. -/
def preimageCarrierIso (i : Fin (m + 1)) : (P.J i).obj (P.preimageCarrier Y) ≅ Y.carrier :=
  have := P.essSurj
  Pi.isoApp ((Functor.pi' P.J).objObjPreimageIso fun _ ↦ Y.carrier) i

/-- The pieces of the structure isomorphism of the algebra with first piece `Y`. -/
def preimageStrPiece (i : Fin (m + 1)) :
    (P.J i).obj (F.obj (P.preimageCarrier Y)) ≅ (P.J i).obj (P.preimageCarrier Y) :=
  Fin.lastCases (motive := fun i ↦
      (P.J i).obj (F.obj (P.preimageCarrier Y)) ≅ (P.J i).obj (P.preimageCarrier Y))
    (P.β.app _ ≪≫ G.mapIso (P.preimageCarrierIso Y 0) ≪≫ Y.str ≪≫
      (P.preimageCarrierIso Y (Fin.last m)).symm)
    (fun k ↦ (P.α k).app _ ≪≫ P.preimageCarrierIso Y k.succ ≪≫
      (P.preimageCarrierIso Y k.castSucc).symm) i

/-- The structure isomorphism of the algebra with first piece `Y`. -/
def preimageStr : F.obj (P.preimageCarrier Y) ≅ P.preimageCarrier Y :=
  P.fullyFaithful.preimageIso (X := F.obj (P.preimageCarrier Y)) (Y := P.preimageCarrier Y)
    (Pi.isoMk (P.preimageStrPiece Y))

lemma map_preimageStr_hom (i : Fin (m + 1)) :
    (P.J i).map (P.preimageStr Y).hom = (P.preimageStrPiece Y i).hom :=
  congrFun (P.fullyFaithful.map_preimage (X := F.obj (P.preimageCarrier Y))
    (Y := P.preimageCarrier Y) (Pi.isoMk (P.preimageStrPiece Y)).hom) i

/-- The algebra with first piece `Y`. -/
def preimage : IsoAlgebra F :=
  IsoAlgebra.mk (P.preimageCarrier Y) (P.preimageStr Y)

@[simp]
lemma preimage_carrier : (P.preimage Y).carrier = P.preimageCarrier Y :=
  rfl

@[simp]
lemma preimage_str : (P.preimage Y).str = P.preimageStr Y :=
  mk_str _ _

lemma chain_preimage (i : Fin (m + 1)) :
    P.chain (P.preimage Y) i =
      P.preimageCarrierIso Y i ≪≫ (P.preimageCarrierIso Y 0).symm := by
  induction i using Fin.induction with
  | zero => ext; simp
  | succ k ih =>
    ext
    rw [chain_succ, ih]
    have h := P.map_preimageStr_hom Y k.castSucc
    simp only [preimageStrPiece, Fin.lastCases_castSucc] at h
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, preimage_str, h,
      Iso.app_hom, Category.assoc]
    erw [Iso.inv_hom_id_app_assoc]
    simp

/-- The first piece of `preimage Y` is `Y`. -/
def functorObjPreimageIso : P.functor.obj (P.preimage Y) ≅ Y :=
  isoMk (P.preimageCarrierIso Y 0) (by
    change _ = (P.strZero (P.preimage Y)).hom ≫ _
    have h := P.map_preimageStr_hom Y (Fin.last m)
    simp only [preimageStrPiece, Fin.lastCases_last] at h
    simp only [strZero, chain_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
      Functor.mapIso_hom, preimage_str, h, Iso.app_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id, str_hom]
    erw [Iso.inv_hom_id_app_assoc])

instance functor_essSurj : P.functor.EssSurj where
  mem_essImage Y := ⟨_, ⟨P.functorObjPreimageIso Y⟩⟩

end EssSurj

instance functor_full : P.functor.Full := P.functorFullyFaithful.full

instance functor_faithful : P.functor.Faithful := P.functorFullyFaithful.faithful

/-- **Algebras for a cyclically permuting endofunctor**: taking the first piece is an equivalence
`IsoAlgebra F ≌ IsoAlgebra G`. -/
instance functor_isEquivalence : P.functor.IsEquivalence where

end CyclicDecomposition

end CategoryTheory.Endofunctor.IsoAlgebra
