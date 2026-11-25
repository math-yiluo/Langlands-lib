/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCyclic

/-!
# Computing the first piece of an algebra for a cyclic decomposition

Let `P` be a decomposition of `C` into pieces `J₀, …, J_m : C ⥤ D` permuted cyclically by
`F : C ⥤ C` up to `G : D ⥤ D` (`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition`), and
let `(A, φ)` be an algebra for `F`. If all pieces of `A` are identified with one object `Y` of `D`
by isomorphisms `cᵢ : Jᵢ A ≅ Y` compatible with `φ` and the `αₖ`, then the structure isomorphism
of the first piece `J₀ A` is, through `c₀`, a given structure isomorphism `ψ : G Y ≅ Y` as soon as
the compatibility with `β` holds
(`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition.functorObjIsoMk`).
-/

@[expose] public section

noncomputable section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F : C ⥤ C}
  {G : D ⥤ D} {m : ℕ} (P : CyclicDecomposition F G m) (A : IsoAlgebra F) {Y : D}
  (c : ∀ i : Fin (m + 1), (P.J i).obj A.carrier ≅ Y)
  (hc : ∀ k : Fin m, (P.J k.castSucc).map A.str.hom ≫ (c k.castSucc).hom =
    (P.α k).hom.app A.carrier ≫ (c k.succ).hom)

include hc in
/-- If the pieces of `A` are identified with `Y` compatibly with the structure isomorphism, the
chain identification `Jᵢ A ≅ J₀ A` is `cᵢ` followed by `c₀⁻¹`. -/
lemma chain_eq_of_compat (i : Fin (m + 1)) : P.chain A i = c i ≪≫ (c 0).symm := by
  induction i using Fin.induction with
  | zero => ext; simp
  | succ k ih =>
    ext
    rw [chain_succ, ih]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
    rw [reassoc_of% (hc k), Iso.inv_hom_id_app_assoc]

include hc in
/-- **The first piece of an algebra, computed**: if the pieces of `A` are identified with `Y`
compatibly with the structure isomorphism and the `αₖ`, and the last piece compatibly with `β`
and a structure isomorphism `ψ : G Y ≅ Y`, then the first piece of `A` is `(Y, ψ)`. -/
def functorObjIsoMk (ψ : G.obj Y ≅ Y)
    (hβ : (P.J (Fin.last m)).map A.str.hom ≫ (c (Fin.last m)).hom =
      P.β.hom.app A.carrier ≫ G.map (c 0).hom ≫ ψ.hom) :
    P.functor.obj A ≅ IsoAlgebra.mk Y ψ :=
  isoMk (c 0) (by
    change G.map (c 0).hom ≫ (IsoAlgebra.mk Y ψ).str.hom = (P.strZero A).hom ≫ (c 0).hom
    rw [mk_str, strZero, chain_eq_of_compat P A c hc]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact ((Iso.inv_comp_eq (P.β.app A.carrier)).2 hβ).symm)

@[simp]
lemma functorObjIsoMk_hom_hom_f (ψ : G.obj Y ≅ Y)
    (hβ : (P.J (Fin.last m)).map A.str.hom ≫ (c (Fin.last m)).hom =
      P.β.hom.app A.carrier ≫ G.map (c 0).hom ≫ ψ.hom) :
    (P.functorObjIsoMk A c hc ψ hβ).hom.hom.f = (c 0).hom :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition

namespace CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F : C ⥤ C}
  {G : D ⥤ D} {m : ℕ} (P : CyclicDecomposition F G m)

/-- `CyclicDecomposition.functorObjIsoMk` for the algebra `mk X φ`, with the hypotheses stated in
terms of `X` and `φ`. -/
def functorObjMkIsoMk (X : C) (φ : F.obj X ≅ X) {Y : D} (c : ∀ i : Fin (m + 1), (P.J i).obj X ≅ Y)
    (hc : ∀ k : Fin m, (P.J k.castSucc).map φ.hom ≫ (c k.castSucc).hom =
      (P.α k).hom.app X ≫ (c k.succ).hom)
    (ψ : G.obj Y ≅ Y)
    (hβ : (P.J (Fin.last m)).map φ.hom ≫ (c (Fin.last m)).hom =
      P.β.hom.app X ≫ G.map (c 0).hom ≫ ψ.hom) :
    P.functor.obj (IsoAlgebra.mk X φ) ≅ IsoAlgebra.mk Y ψ :=
  P.functorObjIsoMk (IsoAlgebra.mk X φ) c (fun k ↦ by rw [mk_str]; exact hc k) ψ
    (by rw [mk_str]; exact hβ)

end CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition
