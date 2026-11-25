/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Rigidity of natural constant-ring sections

Source: the universal-polynomial argument in
lem-sf-constant-inverse-image-scalar-normalization, Step 2.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

private noncomputable abbrev cRing {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : CommRingCat.{u}) := (constantSheaf J CommRingCat.{u}).obj A

private noncomputable abbrev cUnit {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : CommRingCat.{u}) :
    (Functor.const Cᵒᵖ).obj A ⟶ (cRing J A).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj A)

private theorem cUnit_naturality {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {A B : CommRingCat.{u}} (f : A ⟶ B)
    (U : Cᵒᵖ) (a : A) :
    ((constantSheaf J CommRingCat).map f).hom.app U (cUnit J A |>.app U a) =
      (cUnit J B).app U (f a) := by
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)) U) a).symm

private theorem cUnit_restrict {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : CommRingCat.{u}) {U V : Cᵒᵖ}
    (f : U ⟶ V) (a : A) :
    (cRing J A).obj.map f ((cUnit J A).app U a) = (cUnit J A).app V a := by
  exact (ConcreteCategory.congr_hom ((cUnit J A).naturality f) a).symm

private theorem eq_of_distinct_constants_eq {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : CommRingCat.{u}) (U : Cᵒᵖ)
    (a b : A) (hab : a ≠ b) (h : (cUnit J A).app U a = (cUnit J A).app U b)
    (B : CommRingCat.{u}) (s t : (cRing J B).obj.obj U) : s = t := by
  have hc := Presheaf.equalizerSieve_mem J (cUnit J A) a b h
  have hs := (isSheaf_iff_isSheaf_of_type J _).mp
    ((sheafCompose J (forget CommRingCat)).obj (cRing J B)).property
  apply (hs _ hc).isSeparatedFor.ext
  intro V f hf
  exact False.elim (hab hf)

/-- A ring-homomorphic choice of sections of constant rings, natural in every
coefficient ring, is the usual constant-section map.

Source: the universal-polynomial argument in Step 2 of
lem-sf-constant-inverse-image-scalar-normalization.
(auxiliary; not a blueprint node).

Proof: use the lifted integer ring Z and its polynomial ring P=Z[X]. The component
at Z is unique by initiality. Locally the image of X is a polynomial p. Evaluation
at each integer n and naturality show that the constant sections p(n) and n agree.
If p is not X, polynomial extensionality supplies an n with p(n) not n. Local
injectivity of the integer sheafification unit then gives an empty covering sieve,
on which any two sections of any sheaf agree. Thus the image of X equals the
constant X locally, hence globally by separatedness. Naturality under P to A,
X to a, now determines the component at every element of every ring A. -/
theorem constantRingSectionRigidity {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : Cᵒᵖ)
    (α : ∀ A : CommRingCat.{u},
      A ⟶ ((constantSheaf J CommRingCat.{u}).obj A).obj.obj U)
    (hα : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B),
      f ≫ α B = α A ≫ ((constantSheaf J CommRingCat).map f).hom.app U)
    (A : CommRingCat.{u}) :
    α A = (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U := by
  classical
  let Z := CommRingCat.of (ULift.{u} ℤ)
  have : IsDomain Z :=
    Function.Injective.isDomain ULift.ringEquiv.toRingHom ULift.down_injective
  let P := CommRingCat.of (Polynomial Z)
  have hZ : α Z = (cUnit J Z).app U := by
    apply CommRingCat.hom_ext
    ext n
    change α Z (n.down : Z) = (cUnit J Z).app U (n.down : Z)
    simp only [map_intCast]
  have hX : α P Polynomial.X = (cUnit J P).app U Polynomial.X := by
    let s := α P Polynomial.X
    let S := Presheaf.imageSieve (cUnit J P) s
    have hS : S ∈ J U.unop := Presheaf.imageSieve_mem J (cUnit J P) s
    have hs := (isSheaf_iff_isSheaf_of_type J _).mp
      ((sheafCompose J (forget CommRingCat)).obj (cRing J P)).property
    apply (hs S hS).isSeparatedFor.ext
    intro V f hf
    obtain ⟨p, hp⟩ := hf
    change (cRing J P).obj.map f.op s =
      (cRing J P).obj.map f.op ((cUnit J P).app U Polynomial.X)
    rw [cUnit_restrict J P f.op]
    change (cUnit J P).app (op V) p = (cRing J P).obj.map f.op s at hp
    rw [← hp]
    by_cases he : p = Polynomial.X
    · rw [he]
    · obtain ⟨n, hn⟩ : ∃ n : Z, Polynomial.eval n p ≠ n := by
        by_contra hn
        push Not at hn
        exact he (Polynomial.funext (fun n ↦ by simpa using hn n))
      let e : P ⟶ Z := CommRingCat.ofHom (Polynomial.evalRingHom n)
      have heX : e Polynomial.X = n := Polynomial.eval_X
      have hz : ((constantSheaf J CommRingCat).map e).hom.app U s =
          (cUnit J Z).app U n := by
        have h := ConcreteCategory.congr_hom (hα e) Polynomial.X
        change α Z (e Polynomial.X) =
          ((constantSheaf J CommRingCat).map e).hom.app U s at h
        rw [heX, hZ] at h
        exact h.symm
      have hlocal : (cUnit J Z).app (op V) (Polynomial.eval n p) =
          (cUnit J Z).app (op V) n := by
        calc
          _ = ((constantSheaf J CommRingCat).map e).hom.app (op V)
              ((cUnit J P).app (op V) p) := (cUnit_naturality J e (op V) p).symm
          _ = ((constantSheaf J CommRingCat).map e).hom.app (op V)
              ((cRing J P).obj.map f.op s) := congrArg _ hp
          _ = (cRing J Z).obj.map f.op
              (((constantSheaf J CommRingCat).map e).hom.app U s) :=
            ConcreteCategory.congr_hom
              (((constantSheaf J CommRingCat).map e).hom.naturality f.op) s
          _ = _ := by rw [hz, cUnit_restrict]
      exact eq_of_distinct_constants_eq J Z (op V) _ _ hn hlocal P _ _
  apply CommRingCat.hom_ext
  ext a
  let e : P ⟶ A := CommRingCat.ofHom
    (Polynomial.eval₂RingHom
      ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) a)
  have heX : e Polynomial.X = a := Polynomial.eval₂_X _ _
  have h := ConcreteCategory.congr_hom (hα e) Polynomial.X
  change α A (e Polynomial.X) =
    ((constantSheaf J CommRingCat).map e).hom.app U (α P Polynomial.X) at h
  rw [heX, hX, cUnit_naturality, heX] at h
  exact h

end CategoryTheory.ConstantCompletion
