/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.AlgebraicGaloisConstruction
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalFiniteGaloisDiagram
import Mathlib.RepresentationTheory.Rep.Basic

/-! # Adic data from a finite Galois correspondence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Construction witnesses for the three coefficient stages, including normalization.
Source: Weil II (1.1.1) b)-d), (1.1.6); Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: new-c5-galois-adic-data-from-finite).

At the integral stage the representation is the limit of the finite stalk actions
specified by `c.γ`, and its projections agree with `τI`. At the field stages the displayed
linear equivalences identify every pure tensor and intertwine the actions. Thus these
hypotheses determine the actions through the fibre comparisons; an independently twisted
equivalence cannot satisfy them. -/
structure GaloisAdicCanonicalConstruction
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop where
  /-- The integral representation and its normalized comparison arise as an inverse limit
  in the representation category of the finite-level stalk actions. -/
  inverseLimit :
    ∀ (E : Padic.FiniteCoefficientFields l Q) (F : LisseIntegralSheaf l E.val Y),
      ∃ V : ℕᵒᵖ ⥤ Rep.{u + 1} (Padic.coefficientExtensionIntegers l E.val) G,
      ∃ α : V ⋙ forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E.val) G)
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) ≅
        F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber,
      ∃ C : Cone V, ∃ e : C.pt ≅ ((d.eI E).functor.obj F).obj,
        Nonempty (IsLimit C) ∧
        (∀ n : ℕ,
          (forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E.val) G)
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))).map
              (e.inv ≫ C.π.app (op n)) ≫ α.hom.app (op n) =
          (d.τI E).hom.app F ≫
            limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)) ∧
        ∀ n : ℕ,
          ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
            (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))),
          ∃ κ : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
              (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))).obj
                (F.obj.obj (op n))) ≃
            (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
              (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E.val)
                (F.obj.obj (op n)))),
            (∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U)
                (z : (F.obj.obj (op n)).obj.obj (op U)),
              κ ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩
                (F.obj.obj (op n)).obj z) =
              (pointSmallEtale y).toPresheafFiber U x
                (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E.val)
                  (F.obj.obj (op n))).obj z) ∧
            ∀ (g : G) (z : (V.obj (op n)).V),
              κ ((α.hom.app (op n)) ((V.obj (op n)).ρ g z)) =
              (c.γ g).asIso.hom.app (galoisUnderlyingFLC
                (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n)) h)
                  (κ ((α.hom.app (op n)) z))
  /-- Rationalization of each integral model, normalized on every pure tensor. -/
  localization :
    ∀ (E : Padic.FiniteCoefficientFields l Q) (F : LisseRationalSheaf l E.val Y),
      ∃ η : (TensorProduct (Padic.coefficientExtensionIntegers l E.val) E.val
          ((d.eI E).functor.obj F.integral).obj.V) ≃ₗ[E.val]
            ((d.eR E).functor.obj F).obj.V,
        (∀ (g : G) (a : E.val) (z : ((d.eI E).functor.obj F.integral).obj.V),
          η (TensorProduct.tmul _ a (((d.eI E).functor.obj F.integral).obj.ρ g z)) =
            ((d.eR E).functor.obj F).obj.ρ g (η (TensorProduct.tmul _ a z))) ∧
        ∀ (a : E.val) (z : ((d.eI E).functor.obj F.integral).obj.V),
          eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F)
            ((d.τR E).hom.app F (η (TensorProduct.tmul _ a z))) =
              TensorProduct.tmul _ a ((d.τI E).hom.app F.integral z)
  /-- Every finite coefficient model enters the algebraic stage by normalized scalar
  extension, with the action determined on all pure tensors. -/
  colimit :
    ∀ (E : Padic.FiniteCoefficientFields l Q) (F : LisseRationalSheaf l E.val Y),
      ∃ η : (TensorProduct E.val Q ((d.eR E).functor.obj F).obj.V) ≃ₗ[Q]
          (d.eA.functor.obj (lisseAlgebraicOfModel l Y Q E F)).obj.V,
        (∀ (g : G) (a : Q) (z : ((d.eR E).functor.obj F).obj.V),
          η (TensorProduct.tmul _ a (((d.eR E).functor.obj F).obj.ρ g z)) =
            (d.eA.functor.obj (lisseAlgebraicOfModel l Y Q E F)).obj.ρ g
              (η (TensorProduct.tmul _ a z))) ∧
        ∀ (a : Q) (z : ((d.eR E).functor.obj F).obj.V),
          eqToHom (lisseAlgebraicFiber_ofModel l Y y Q E F)
            (eqToHom (lisseAlgebraicFiberFunctor_obj l Y y Q
              (lisseAlgebraicOfModel l Y Q E F))
                (d.τA.hom.app _ (η (TensorProduct.tmul _ a z)))) =
            TensorProduct.tmul _ a
              (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F)
                ((d.τR E).hom.app F z))

end AlgebraicGeometry.Scheme
