/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import WeilConjectures.AlgebraicGeometry.EtaleEvaluationSeparable

/-!
# Evaluation of unit germs in the separable closure

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Evaluation defines an additive homomorphism on the geometric stalk of units.

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation).

Proof: An etale neighbourhood of a geometric point over a field admits a refinement
by the spectrum of a finite separable extension: choose an affine open around the
image point and then its connected component. Evaluation of global functions at
its lift lands in that extension's embedded copy in the algebraic closure, hence
in the image of the separable closure. The same holds for the inverse of a unit.
The embedding of the separable closure in the algebraic closure is injective, so
there is a unique unit with this evaluated value. Pullback of functions commutes
with evaluation. These maps therefore form a compatible cocone over pointed etale
neighbourhoods and induce a map on the filtered colimit defining the stalk.
Evaluation preserves products, which are addition in the coefficient groups.
Removing the universe lift gives the asserted additive homomorphism and formula.
This constructs no arbitrary witness: the formula uniquely determines every value. -/
theorem exists_etale_units_stalk_evaluation (K : Type u) [Field K] :
    let Ω := AlgebraicClosure K
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∃ f : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf →+
        Field.galoisUnitsTopRep K,
      ∀ (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)),
        algebraMap (SeparableClosure K) Ω
            (Additive.toMul (f (p.toPresheafFiber X x S.gmSheaf.obj z)) :
              (SeparableClosure K)ˣ) =
          (ΓSpecIso (.of Ω)).hom
            (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) := by
  classical
  dsimp only
  let Ω := AlgebraicClosure K
  let S := Spec (.of K)
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let ev (X : S.Etale) (x : p.fiber.obj X) : Γ(X.left, ⊤) →+* Ω :=
    (x.left.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom
  let e (X : S.Etale) (x : p.fiber.obj X) : Γ(X.left, ⊤) →+* SeparableClosure K :=
    { toFun := fun z ↦ ⟨ev X x z, etale_evaluation_isSeparable K X x z⟩
      map_one' := Subtype.ext (map_one (ev X x))
      map_mul' a b := Subtype.ext (map_mul (ev X x) a b)
      map_zero' := Subtype.ext (map_zero (ev X x))
      map_add' a b := Subtype.ext (map_add (ev X x) a b) }
  let φ (X : S.Etale) (x : p.fiber.obj X) :
      S.gmSheaf.obj.obj (op X) ⟶
        AddCommGrpCat.of (ULift.{u + 1} (Additive (SeparableClosure K)ˣ)) :=
    AddCommGrpCat.ofHom
      { toFun := fun z ↦ ULift.up (Additive.ofMul (Units.map (e X x).toMonoidHom
          (Additive.toMul z.down)))
        map_zero' := by apply ULift.ext; simp
        map_add' a b := by apply ULift.ext; simp }
  have hφ : ∀ ⦃X Y : S.Etale⦄ (a : X ⟶ Y) (x : p.fiber.obj X),
      S.gmSheaf.obj.map a.op ≫ φ X x = φ Y (p.fiber.map a x) := by
    intro X Y a x
    apply AddCommGrpCat.ext
    intro z
    apply ULift.ext
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    change ev X x (a.left.appTop ((Additive.toMul z.down : Γ(Y.left, ⊤)ˣ) : Γ(Y.left, ⊤))) =
      ev Y (p.fiber.map a x) ((Additive.toMul z.down : Γ(Y.left, ⊤)ˣ) : Γ(Y.left, ⊤))
    dsimp [ev, p, pointSmallEtale]
    rfl
  let fLift := p.presheafFiberDesc φ hφ
  let f : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf →+
      Field.galoisUnitsTopRep K :=
    { toFun := fun z ↦ (fLift z).down
      map_zero' := by simp
      map_add' a b := by simp }
  refine ⟨f, ?_⟩
  intro X x z
  have hf := congrArg ULift.down <| ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberDesc φ hφ X x) z
  change algebraMap (SeparableClosure K) Ω
      (Additive.toMul (fLift (p.toPresheafFiber X x S.gmSheaf.obj z)).down :
        (SeparableClosure K)ˣ) = _
  exact congrArg (fun t : Additive (SeparableClosure K)ˣ ↦
    algebraMap (SeparableClosure K) Ω (Additive.toMul t : (SeparableClosure K)ˣ)) hf

end AlgebraicGeometry.Scheme
