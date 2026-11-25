/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Fixed-scalar encoding after a coefficient isomorphism

The functor is termwise restriction along the inverse coefficient isomorphism,
followed by the normalized section-action encoding. All of its data are constructed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

/-- Restrict scalars along the inverse ring isomorphism and use the fixed-scalar
section-action encoding. Source: blueprint finite-coefficient identification, steps 1
and 8; Stacks Tags 03D3 and 09C8
(blueprint: def-sfb-finite-coefficient-operation-encoding). -/
def coefficientEncoding (e : Mon.mk R ≅ Mon.mk (coefficient A)) (T : Scheme.{u})
    (E : Encoding A T) : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T)) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.inv.hom T)).mapDerivedCategory ⋙ E.fixedDerived.functor

/-- The constructed encoding is an equivalence, since both factors are exact equivalences.
Source: scalar restriction along an isomorphism and normalized section-action encoding
(blueprint: def-sfb-finite-coefficient-operation-encoding). -/
instance coefficientEncoding_isEquivalence
    (e : Mon.mk R ≅ Mon.mk (coefficient A)) (T : Scheme.{u}) (E : Encoding A T) :
    (coefficientEncoding A e T E).IsEquivalence := by
  have : IsIso e.inv.hom := by
    change IsIso ((Mon.forget _).map e.inv)
    infer_instance
  have : IsIso (coefficientMap e.inv.hom T) := by
    dsimp [coefficientMap]
    infer_instance
  have : (Mod.comap (coefficientMap e.inv.hom T)).IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso
      (coefficientMap e.inv.hom T)).functor.IsEquivalence)
  have := Functor.isEquivalence_mapDerivedCategory
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (coefficientMap e.inv.hom T))
  change ((Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.inv.hom T)).mapDerivedCategory ⋙ E.fixedDerived.functor).IsEquivalence
  infer_instance

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
