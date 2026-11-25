/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisUnit

/-! # Scalar-basis decompositions for the finite-subextension-valued algebraic closure

Source: Colimit/Compatibility.lean, finite-basis unit calculation, and the finite-support
coefficient model of Condensed/FiniteSubextension.lean.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Keep the chosen derived adjunction folded while checking the scalar unit maps.
attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  AlgebraicGeometry.ProEtale.upperStarFromPoint AlgebraicGeometry.ProEtale.upperStar

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The scalar-basis proposition, with the complete coefficient and derived-unit formula.
This definition only names the original proposition: it has no mathematical data or proof.
Naming it avoids repeated inspection of concrete derived-functor applications during theorem
index export. Its body is exposed, so existing consumers can eliminate its existentials. -/
def CondensedQbarDerivedScalarBasis : Prop :=
    ∃ (I : Type (u + 1))
      (τ : ∀ Z : Scheme.{u}, I → CatCenter (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)))),
      (∀ (Z : Scheme.{u}) (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
        [HasCoproduct (fun _ : I ↦ M)],
        IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
          (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app M ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).mapDerivedCategory.map
              ((τ Z i).app ((Mod.extendScalars (coefficientMap
                (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).leftDerivedFunctor.obj M)))) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I)
        (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))),
        R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map ((τ X i).app M) =
          (τ Y i).app (R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M))

/-- A single algebraic basis gives compatible scalar endomorphisms on every scheme.
Source: Compatibility.lean, finiteFreePushData and derivedPushHom_of_finiteFree;
FiniteSubextension.lean, the finite-subextension-valued coefficient colimit.
(auxiliary; not a blueprint node)

Proof: choose an E-basis of the algebraic closure. A section of the specified coefficient
presheaf lies in a finite intermediate field. Its image therefore lies in a finite-dimensional
E-subspace and has only finitely many basis coordinates; each coordinate is continuous by
finite-dimensional topological linear algebra. This gives the coproduct decomposition of the
restricted regular module, whose summand maps send 1 to the chosen basis elements. Finite
covers preserve finite support, so the same decomposition holds after sheafification.
The monoidal left adjoint from the point preserves it. Tensor this decomposition with each
module: its summand maps are the extension unit followed by basis scalar multiplication.
Exact coproducts and exact coefficient extension descend this natural isomorphism termwise
to the unbounded derived category. The descended scalar multiplications are central.
Their pullback compatibility follows from the monoidal unit map and the coefficient square.
Transpose that equality along derived pullback/direct image: pushforward carries each scalar
to the same scalar. Thus the same basis works on every scheme and for every morphism.
No preservation of infinite coproducts by direct image is used here. -/
theorem condensedQbar_derived_scalar_basis :
    CondensedQbarDerivedScalarBasis ℓ E := by
  let h := exists_condensedQbar_scalar_basis_unit ℓ E
  rcases h with ⟨I, b, hb, hunit⟩
  refine ⟨I, fun Z i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b Z i)), ?_, ?_⟩
  · intro Z M hM
    simpa only [Mod.qbar_scalarUnitLeg_eq] using hunit Z M
  · intro X Y f i M
    exact qbar_lowerStar_derivedScalarEndo_of_eq f (b X i) (b Y i) (hb f i) M

end AlgebraicGeometry.ProEtale.CondensedRing
