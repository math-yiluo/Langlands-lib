/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareOrdinaryTensorHomCompatibility

/-! # The ordinary total tensor square

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0E48.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory MonoidalCategory

namespace SheafOfModules

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

private theorem inverse_square {A : Type*} [Category A] {V W X Z : A}
    (a : V ≅ W) (b : X ≅ Z) (p : V ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ b.hom = a.hom ≫ q) : a.inv ≫ p = q ≫ b.inv := by
  calc
    a.inv ≫ p = a.inv ≫ (p ≫ b.hom) ≫ b.inv := by simp
    _ = a.inv ≫ (a.hom ≫ q) ≫ b.inv := by rw [hp]
    _ = q ≫ b.inv := by simp

-- Keep the four total-complex comparison types explicit.
/-- The ordinary total tensor comparisons commute with the linear square.

Proof: first work with two module sheaves M,N. Precompose each side of the
module tensor square with scalar-extension insertions of generalized pure tensors.
The pure-tensor formula for each edge comparison and the insertion equation
for s show that both paths give the tensor of the two iterated insertions,
followed by the same map of underlying sheaves. Naturality of s.sets with respect
to the generalized sections identifies these maps. Linearity then extends the
identity from inserted generators to arbitrary scalar multiples and finite sums.
The sheafification universal property extends it to all sections, proving equality
of module morphisms. Apply this identity to P.X i and Q.X j. The canonical total
comparison has exactly these maps on the coproduct summands indexed by i+j=n.
Pullbacks preserve these coproducts since they are left adjoints. The coproduct
universal property therefore proves the displayed equality in degree n. The
comparisons preserve i and j, so no factors are exchanged and no extra sign occurs.
Degreewise equality proves the equality of complex morphisms. This argument uses
no flatness: it includes zero rings, nonflat structural maps, and zero complexes.
Source: Stacks, Cohomology on Sites, Tag 07A4 (lemma-pullback-tensor-product),
and the tensor part of Tag 0E48 (remark-compatible-with-diagram).
(blueprint: lem-weil-pbc-ringed-square-ordinary-tensor-compatibility). -/
theorem ringedSquareOrdinaryTensorCompatibility
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ℤ) :
    (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app ((Functor.uncurry.obj
        ((@MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) _
          (monoidalCategory Y.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).obj (P, Q)) ≫
      (h.pullback.mapHomologicalComplex (.up ℤ)).map
      (f.ordinaryTensor.totalIso Y.ring X.ring f.inverseRing
        f.inverse f.algebraic f.ringMap f.pullback f.object_eq
        f.pushforward f.moduleAdjunction P Q).inv ≫
      (h.ordinaryTensor.totalIso X.ring X'.ring h.inverseRing
        h.inverse h.algebraic h.ringMap h.pullback h.object_eq
        h.pushforward h.moduleAdjunction ((f.pullback.mapHomologicalComplex (.up ℤ)).obj P)
        ((f.pullback.mapHomologicalComplex (.up ℤ)).obj Q)).inv =
    (k.pullback.mapHomologicalComplex (.up ℤ)).map
      (g.ordinaryTensor.totalIso Y.ring Y'.ring g.inverseRing
        g.inverse g.algebraic g.ringMap g.pullback g.object_eq
        g.pushforward g.moduleAdjunction P Q).inv ≫
      (k.ordinaryTensor.totalIso Y'.ring X'.ring k.inverseRing
        k.inverse k.algebraic k.ringMap k.pullback k.object_eq
        k.pushforward k.moduleAdjunction ((g.pullback.mapHomologicalComplex (.up ℤ)).obj P)
        ((g.pullback.mapHomologicalComplex (.up ℤ)).obj Q)).inv ≫
      (Functor.uncurry.obj
        ((@MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose X'.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X'.ring)) _
          (monoidalCategory X'.ring)).map₂HomologicalComplex
            (.up ℤ) (.up ℤ) (.up ℤ))).map (CategoryTheory.Prod.mkHom
        ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app Q)) := by
  let F := f.pullback.mapHomologicalComplex (.up ℤ)
  let G := g.pullback.mapHomologicalComplex (.up ℤ)
  let H := h.pullback.mapHomologicalComplex (.up ℤ)
  let K := k.pullback.mapHomologicalComplex (.up ℤ)
  let γ := (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom
  let ef := f.ordinaryTensor.totalIso Y.ring X.ring f.inverseRing
    f.inverse f.algebraic f.ringMap f.pullback f.object_eq
    f.pushforward f.moduleAdjunction P Q
  let eg := g.ordinaryTensor.totalIso Y.ring Y'.ring g.inverseRing
    g.inverse g.algebraic g.ringMap g.pullback g.object_eq
    g.pushforward g.moduleAdjunction P Q
  let eh := h.ordinaryTensor.totalIso X.ring X'.ring h.inverseRing
    h.inverse h.algebraic h.ringMap h.pullback h.object_eq
    h.pushforward h.moduleAdjunction (F.obj P) (F.obj Q)
  let ek := k.ordinaryTensor.totalIso Y'.ring X'.ring k.inverseRing
    k.inverse k.algebraic k.ringMap k.pullback k.object_eq
    k.pushforward k.moduleAdjunction (G.obj P) (G.obj Q)
  let TY := Functor.uncurry.obj
    ((@MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) _
      (monoidalCategory Y.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  let TZ := Functor.uncurry.obj
    ((@MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose X'.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X'.ring)) _
      (monoidalCategory X'.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  let a : TZ.obj (K.obj (G.obj P), K.obj (G.obj Q)) ≅ K.obj (G.obj (TY.obj (P, Q))) :=
    ek ≪≫ K.mapIso eg
  let b : TZ.obj (H.obj (F.obj P), H.obj (F.obj Q)) ≅ H.obj (F.obj (TY.obj (P, Q))) :=
    eh ≪≫ H.mapIso ef
  have hh : TZ.map (CategoryTheory.Prod.mkHom (γ.app P) (γ.app Q)) ≫ b.hom =
      a.hom ≫ γ.app (TY.obj (P, Q)) := by
    exact ringedSquareOrdinaryTensorHomCompatibility s P Q
  have hc := (inverse_square a b
    (TZ.map (CategoryTheory.Prod.mkHom (γ.app P) (γ.app Q)))
    (γ.app (TY.obj (P, Q))) hh).symm
  simpa only [a, b, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using hc

end SheafOfModules
