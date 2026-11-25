/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientExchangeTransport

/-!
# Finite-level pro-etale proper base change

Source: blueprint, proper base change, finite-level pro-etale theorem; Stacks Project
Tag 09C8, the finite-coefficient step in Tag 09C9
(blueprint: proposition-proper-direct-image-constructible-complexes--5).

## Main statements

- `AlgebraicGeometry.Scheme.finiteLevelProEtaleBaseChange`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The canonical inverse image of the finite constant coefficient sheaf.
Source: Stacks Tag 098T (blueprint: proposition-proper-direct-image-constructible-complexes--5). -/
noncomputable def finiteCoefficientRingIso {U V : Scheme.{u}} (h : U ⟶ V) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj (finiteOriginFunctionRing V Λ) ≅
      finiteOriginFunctionRing U Λ :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso
      (finiteOriginConstantIso V Λ).symm ≪≫
    (letI : ∀ n : ℕᵒᵖ,
        Finite (((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ)).obj n) :=
      fun _ ↦ inferInstanceAs (Finite Λ)
    @asIso _ _ _ _ ((proEtaleConstantComparison h).app (CommRingCat.of Λ))
      ((proEtale_profinite_coefficient_inverse_image
        ((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ))).1 U V h (Opposite.op 0))) ≪≫
    finiteOriginConstantIso U Λ

private theorem finiteCoefficientRingIso_comp {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    proEtaleRingCompositeCoefficients h k (finiteOriginFunctionRing V Λ)
        (finiteOriginFunctionRing W Λ) (finiteOriginFunctionRing Z Λ)
        (finiteCoefficientRingIso Λ k) (finiteCoefficientRingIso Λ h) =
      finiteCoefficientRingIso Λ (h ≫ k) := by
  let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ)
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun _ ↦ inferInstanceAs (Finite Λ)
  have hc := (proEtale_profinite_coefficient_inverse_image Q).2.2.2.2.2.2.2.2.2.1
    Z W V h k (Opposite.op 0)
  dsimp [Q, proEtaleCoefficientTower] at hc
  apply Iso.ext
  dsimp [proEtaleRingCompositeCoefficients, finiteCoefficientRingIso]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (proEtaleSheafInverseImage h CommRingCat.{u + 1})
    (finiteOriginConstantIso W Λ).hom (finiteOriginConstantIso W Λ).inv]
  simp only [Iso.hom_inv_id]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (proEtaleRingInverseImageComp h k).hom.naturality
    (finiteOriginConstantIso V Λ).inv
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [hc]
  simp only [Category.assoc]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

include sq in
/-- Finite coefficient identifications agree around the chosen square.
Source: Stacks Tags 098T and 07A7 (blueprint:
proposition-proper-direct-image-constructible-complexes--5). Proof: finite constant comparisons
commute with composition by the finite-level coherence of profinite-coefficient-inverse-image. Apply
it to both paths of sq and identify their composite scheme maps by sq.w. -/
theorem finiteCoefficientRingIso_coherent :
    HEq (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing X' Λ)
      (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g'))
    (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ)
      (finiteCoefficientRingIso Λ g) (finiteCoefficientRingIso Λ f')) := by
  rw [finiteCoefficientRingIso_comp, finiteCoefficientRingIso_comp]
  exact (show ∀ {a b : X' ⟶ Y}, a = b →
    HEq (finiteCoefficientRingIso Λ a) (finiteCoefficientRingIso Λ b) from
      fun w ↦ by cases w; rfl) sq.toCommSq.w

/-- The existing ambient exchange specialized to the canonical finite coefficients.
Source: Stacks Tag 07A7 (blueprint: proposition-proper-direct-image-constructible-complexes--5). -/
noncomputable abbrev finiteCoefficientExchange :=
  proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing Y Λ)
    (finiteOriginFunctionRing X' Λ) (finiteOriginFunctionRing Y' Λ)
    (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g)
    (finiteCoefficientRingIso Λ g') (finiteCoefficientRingIso Λ f')
    (finiteCoefficientRingIso_coherent Λ sq)

/-- Finite-coefficient proper exchange is invertible for an object with the retained
bounded-below etale-origin witness. The exchange itself is defined independently of
that witness, so replacing it by an isomorphic witness gives the same arrow.
Source: blueprint finite-level pro-etale theorem; Stacks Tags 09C8 and 09C9
(blueprint: proposition-proper-direct-image-constructible-complexes--5).
Proof: the normalized ringed pullbacks along constant coefficient identifications are
exact inverse images, so the ambient mate is the displayed inverse-image exchange.
The bounded-below etale witness has torsion cohomology since Λ is finite. Apply
theorem-proper-base-change-classical-pro to its etale complex. The fully faithful comparison
theorem-bounded-below-cohomology-comparison transports this isomorphism. The canonical comparison
lemma-naturality-pasting-comparison--3 identifies the transported morphism with
the ringed ambient exchange. Conjugate it using the witness isomorphism. Naturality
of exchange shows that isomorphic witnesses give the same intrinsic morphism. No
bound uniform in a coefficient level is used. -/
theorem finiteLevelProEtaleBaseChange [IsProper f]
    (K : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (_W : FiniteEtaleOriginWitness X Λ K) :
    IsIso ((finiteCoefficientExchange Λ sq).app K) := by
  let a := (finiteOriginConstantIso Y' Λ).hom
  letI : (proEtaleRingRestrictScalars a).Additive := inferInstance
  letI : PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).1
  letI : PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).2.1
  letI : (proEtaleRingRestrictScalars a).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties a).2.2
  letI : (proEtaleRingRestrictScalars a).mapDerivedCategory.ReflectsIsomorphisms :=
    { reflects := fun f _ ↦ by
        rw [DerivedCategory.isIso_iff]
        intro n
        have : IsIso ((proEtaleRingRestrictScalars a).map
            ((DerivedCategory.homologyFunctor _ n).map f)) :=
          (NatIso.isIso_map_iff
            ((proEtaleRingRestrictScalars a).mapDerivedCategoryHomologyFunctorIso n) f).2
              (by rw [Functor.comp_map]; infer_instance)
        exact isIso_of_reflects_iso _ (proEtaleRingRestrictScalars a) }
  have hmap := finiteOriginToConstant_map_ambientExchange_isIso Λ sq
    (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g)
    (finiteCoefficientRingIso Λ g') (finiteCoefficientRingIso Λ f')
    (finiteCoefficientRingIso_coherent Λ sq) K _W
  exact isIso_of_reflects_iso _ (finiteOriginToConstant Y' Λ)

end AlgebraicGeometry.Scheme
