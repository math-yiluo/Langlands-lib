/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.AffinePrincipalSheafComplexTransport
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift

/-! A finite-free witness for the local principal-open pseudo-coherence comparison.
(blueprint: lem-pc-affine-pseudo-coherent-principal-sheaf-model)
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite-free module complex whose associated sheaf is the principal-open model.
Source: Stacks Project, Tag 08E7, converse proof, local-model comparison.
(blueprint: lem-pc-affine-pseudo-coherent-principal-sheaf-model).

Proof:
Restrict P and the given derived isomorphism along D(f) ≤ U. Open restriction is
exact, hence computes derived restriction termwise and preserves zero objects.
It preserves free sheaves of each finite rank. Identify D(f) with Spec(A_f),
transporting sheaves of modules along this scheme isomorphism and the equivalence
between the localized open site and the open subscheme. These equivalences are
exact and induce equivalences between the chosen derived categories, independently
of their morphism universes. For each degree at or below the supplied bound choose
an identification of the transported term with a finite free sheaf. Take E in that
degree to be the free A_f-module of the same rank. In degrees above the bound take
the zero module and use the zero-object identification instead. The tilde/Gamma
adjunction identifies these associated sheaves with the transported terms of P.
Full faithfulness of tilde lifts every differential; its faithfulness proves the
square-zero equations and gives an isomorphism of associated-sheaf complexes.
Thus E is strictly bounded above and all its terms are finite and free.
The principal-open sections formula for tilde identifies restriction of tilde N
with tilde(A_f tensor_A N), naturally in N: on each smaller principal open both
sections are the same further localization, with the same localization maps.
Apply this natural comparison to M and its differentials. Compose its derived
isomorphism with the restriction of hiso and with the inverse of the associated
sheaf identification of E to obtain the displayed sheaf-derived isomorphism.
If D(f) is empty, A_f is the zero ring, all modules and sheaves in question are
zero, and E can be the zero complex. Rank zero, f a unit, and arbitrary integer
upper bounds require no extra hypotheses. No module-derived isomorphism is
asserted here; reflection through the affine derived equivalence is a separate
step in the importing theorem. -/
theorem affine_pseudoCoherent_principal_sheaf_model (A : Type u) [CommRing A]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A)
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings (Spec (.of A)).toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hiso : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M)) ≅
      DerivedCategory.Q.obj P)) :
    ∃ E : CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ,
      ∃ b : ℤ, E.IsStrictlyLE b ∧
        (∀ j : ℤ, Module.Free (Localization.Away f) (E.X j) ∧
          Module.Finite (Localization.Away f) (E.X j)) ∧
        Nonempty (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Localization.Away f))
            (SheafOfModules.{u}
              (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))
            _ _ _ _ (tilde.functor (.of (Localization.Away f)))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj E) ≅
          DerivedCategory.Q.obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Localization.Away f))
              (SheafOfModules.{u}
                (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))
              _ _ _ _ (tilde.functor (.of (Localization.Away f)))
              ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
                ((Functor.mapHomologicalComplex
                  (ModuleCat.extendScalars (algebraMap A (Localization.Away f)))
                  (ComplexShape.up ℤ)).obj M))) := by
  obtain ⟨C, hCbound, hCfree, ⟨eC⟩⟩ :=
    affine_principal_sheaf_complex_transport A M f U hf P hb hfree hiso
  obtain ⟨E, b, hEbound, hEfree, ⟨eE⟩⟩ :=
    affine_finiteFree_sheaf_complex_lift (Localization.Away f) C hCbound hCfree
  exact ⟨E, b, hEbound, hEfree, ⟨DerivedCategory.Q.mapIso eE ≪≫ eC⟩⟩

end AlgebraicGeometry
