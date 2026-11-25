/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Constant global sections of ring objects of presheaves and sheaves

For a presheaf of rings `P` and a ring `R`, a natural family of ring homomorphisms
`φ X : R →+* P.obj X` gives a ring homomorphism from `R` to the global sections `𝟙 ⟶ P` of the
ring object `P ⋙ forget₂ RingCat Ab` (`CategoryTheory.Functor.ringHomΓCompForget₂`), and
likewise for sheaves of rings after sheafification
(`CategoryTheory.Sheaf.ringHomΓSheafCompose`).

For the condensed ring `ℚ̲̄_ℓ`, the constant maps `S → ℚ̄_ℓ` give the ring homomorphism
`ℚ̄_ℓ →+* Γ ℚ̲̄_ℓ` (`Profinite.PadicAlgCl.constRingHom`).
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Functor

variable (P : C ⥤ RingCat.{w}) {R : Type*} [Ring R]

/-- A natural family of ring homomorphisms `φ X : R →+* P.obj X` as a ring homomorphism from `R`
to the global sections `𝟙 ⟶ P ⋙ forget₂ RingCat Ab` of the ring object: `r` is sent to the
global section whose component at `X` is `n ↦ n • φ X r`. -/
noncomputable def ringHomΓCompForget₂ (φ : ∀ X, R →+* P.obj X)
    (hφ : ∀ {X Y : C} (f : X ⟶ Y) (r : R), P.map f (φ X r) = φ Y r) :
    R →+* Γ (P ⋙ forget₂ RingCat.{w} Ab.{w}) where
  toFun r := Γ.ofHom
    { app X := AddCommGrpCat.ofHom
        ((AddMonoidHom.mulRight (φ X r)).comp ((Int.castAddHom (P.obj X)).comp
          AddEquiv.ulift.toAddMonoidHom))
      naturality X Y f := by
        ext n
        change (n.down : P.obj Y) * φ Y r = P.map f ((n.down : P.obj X) * φ X r)
        rw [_root_.map_mul, map_intCast, hφ] }
  map_one' := by
    ext X n
    change (n.down : P.obj X) * φ X 1 = (n.down : P.obj X)
    rw [_root_.map_one, _root_.mul_one]
  map_mul' r s := by
    ext X n
    change (n.down : P.obj X) * φ X (r * s) = (1 : ℤ) * φ X r * ((n.down : P.obj X) * φ X s)
    rw [_root_.map_mul, Int.cast_one, _root_.one_mul, ← _root_.mul_assoc, ← _root_.mul_assoc,
      Int.cast_comm]
  map_zero' := by
    ext X n
    change (n.down : P.obj X) * φ X 0 = 0
    rw [_root_.map_zero, mul_zero]
  map_add' r s := by
    ext X n
    change (n.down : P.obj X) * φ X (r + s) =
      (n.down : P.obj X) * φ X r + (n.down : P.obj X) * φ X s
    rw [_root_.map_add, mul_add]

end Functor

namespace Sheaf

attribute [local instance] Sheaf.monoidalCategory

variable (J : GrothendieckTopology C) [HasSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})] (S : Sheaf J RingCat.{w}) {R : Type*} [Ring R]

/-- A natural family of ring homomorphisms `φ X : R →+* S(X)` into the sections of a sheaf of
rings `S` as a ring homomorphism from `R` to the global sections `𝟙 ⟶ S` of the underlying ring
object of abelian sheaves: the global sections of the presheaf of rings
(`Functor.ringHomΓCompForget₂`), sheafified. -/
noncomputable def ringHomΓSheafCompose (φ : ∀ X, R →+* S.obj.obj X)
    (hφ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R), S.obj.map f (φ X r) = φ Y r) :
    R →+* Γ ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) :=
  (Γ.map (sheafifyRingPresheafIso J S).hom).comp
    ((Γ.mapFunctor (presheafToSheaf J Ab.{w})).comp (S.obj.ringHomΓCompForget₂ φ hφ))

end Sheaf

end CategoryTheory

namespace Profinite.PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The constant maps `S → ℚ̄_ℓ`, as sections of the condensed ring `ℚ̲̄_ℓ` over `S`. -/
noncomputable def constSectionRingHom (S : Profinite.{u}ᵒᵖ) :
    PadicAlgCl ℓ →+* (padicAlgClRingPresheaf.{u} ℓ).obj S :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((ContinuousMap.C (α := S.unop) (A := PadicAlgCl ℓ)).codRestrict
      (_root_.PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop) fun a ↦
        ⟨IntermediateField.adjoin ℚ_[ℓ] {a},
          IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a),
          fun _ ↦ IntermediateField.mem_adjoin_simple_self ℚ_[ℓ] a⟩)

/-- The constant global sections of the condensed ring `ℚ̲̄_ℓ`: the ring homomorphism
`ℚ̄_ℓ →+* Γ ℚ̲̄_ℓ` sending `a` to the global section `1 ↦ a`. -/
noncomputable def constRingHom : PadicAlgCl ℓ →+* Γ (padicAlgClRingObj.{u} ℓ) :=
  Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u}) (padicAlgClCondensedRing ℓ)
    (constSectionRingHom ℓ) fun _ _ ↦ rfl

end Profinite.PadicAlgCl
