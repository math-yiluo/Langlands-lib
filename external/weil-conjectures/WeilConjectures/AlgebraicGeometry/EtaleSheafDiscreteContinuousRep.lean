/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison
public import WeilConjectures.RepresentationTheory.DiscreteModule.DiscreteContinuousRep

/-!
# Abelian étale sheaves on a field as discrete continuous representations

This file repackages the equivalence `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteModule`
between abelian étale sheaves on `Spec K` and discrete `Gal(Ks/K)`-modules, for a separable
closure `Ks` of `K`, with values in the category `Rep.DiscreteContinuousRep ℤ Gal(Ks/K)` of
discrete continuous integral representations, and compares its underlying abelian group with
the stalk at a geometric point `Spec Ω ⟶ Spec K` through `Ks`.

## Main definitions and statements

- `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRep`: the equivalence.
- `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRepForgetIso`: its underlying
  abelian group is the stalk at `Spec Ω ⟶ Spec K`.
- `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRepForgetIso_ρ`: under this
  identification `σ ∈ Gal(Ks/K)` acts on germs by changing the geometric lift by an
  automorphism of `Ω` extending `σ`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks] [IsSepClosed Ks]
  [Algebra.IsSeparable K Ks]

/-- Abelian étale sheaves on `Spec K` are equivalent to discrete continuous integral
representations of `Gal(Ks/K)`: the equivalence `etaleSheafEquivDiscreteModule` composed with
`DiscreteModule.discreteContinuousRepEquivalence`. -/
noncomputable def etaleSheafEquivDiscreteContinuousRep :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ Gal(Ks/K) :=
  (etaleSheafEquivDiscreteModule K Ks).trans
    (DiscreteModule.discreteContinuousRepEquivalence.{u + 1} Gal(Ks/K))

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsScalarTower K Ks Ω]
  [IsSepClosed Ω]

/-- The underlying abelian group of the discrete representation attached to an abelian étale
sheaf on `Spec K` is its stalk at the geometric point `Spec Ω ⟶ Spec K`. -/
noncomputable def etaleSheafEquivDiscreteContinuousRepForgetIso :
    (etaleSheafEquivDiscreteContinuousRep K Ks).functor ⋙ ObjectProperty.ι _ ⋙
        Rep.RepToAction ℤ Gal(Ks/K) ⋙ Action.forget (ModuleCat.{u + 1} ℤ) Gal(Ks/K) ⋙
          forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  Functor.isoWhiskerLeft (etaleSheafEquivDiscreteModule K Ks).functor
      (DiscreteModule.toDiscreteContinuousRepCompForgetIso.{u + 1} Gal(Ks/K)) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl) ≪≫
    galoisPointSheafFiberIso K Ks Ω

/-- Under `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRepForgetIso`, the
element `σ ∈ Gal(Ks/K)` acts on the germ of `z` at a lift `x` of the geometric point
`Spec Ω ⟶ Spec K` as the germ of `z` at `Spec τ ≫ x`, for any automorphism `τ` of `Ω`
extending `σ`. -/
lemma etaleSheafEquivDiscreteContinuousRepForgetIso_ρ
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (σ : Gal(Ks/K))
    (τ : Ω ≃ₐ[K] Ω)
    (hτ : (algebraMap Ks Ω).comp σ.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω))
    (X : (Spec (.of K)).Etale)
    (x x' : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
    (z : F.obj.obj (op X)) :
    (etaleSheafEquivDiscreteContinuousRepForgetIso K Ks Ω).hom.app F
        (((etaleSheafEquivDiscreteContinuousRep K Ks).functor.obj F).obj.ρ σ
          ((etaleSheafEquivDiscreteContinuousRepForgetIso K Ks Ω).inv.app F
            ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
              X x F.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z :=
  galoisPointSheafFiberIso_presheafFiberAct K Ks Ω F σ τ hτ X x x' hx z

end AlgebraicGeometry.Scheme
