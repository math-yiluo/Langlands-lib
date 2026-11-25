/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData

/-! # The fixed integral bases respect ordinary successor balancing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem quotientFunctorEq (W : Scheme.{u}) (n : ℕ) :
    Mod.extendScalars
      (AdicCompletion.quotient l E W (n + 1) ≫ AdicCompletion.transition l E W n) =
        Mod.extendScalars (AdicCompletion.quotient l E W n) := by
  congr 1
  exact AdicCompletion.quotient_transition l E W n

private theorem complex_balancing
    {C₀ C₁ C₂ : Type*} [Category C₀] [Preadditive C₀]
    [Category C₁] [Preadditive C₁] [Category C₂] [Preadditive C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) (K : CochainComplex C₀ ℤ) (i : ℤ)
    {M₁ : C₁} {M₂ : C₂}
    (a : F.obj (K.X i) ≅ M₁) (b : G.obj M₁ ≅ M₂)
    (c : H.obj (K.X i) ≅ M₂)
    (h : G.map a.hom ≫ b.hom = e.hom.app (K.X i) ≫ c.hom) :
    G.map a.hom ≫ b.hom =
      ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).app K).hom.f i ≫ c.hom := h

private theorem module_actual (W : Scheme.{u}) (n : ℕ)
    (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (AdicCompletion.ring l E W)) (r : ℕ)
    (e : M ≅ Mod.finiteFree (AdicCompletion.ring l E W) r) :
    let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
    let B := Φ.mapBiproduct (fun _ : Fin r ↦
      Mod.regular (AdicCompletion.finiteRing l E W (n + 1))) ≪≫
        biproduct.mapIso (fun _ : Fin r ↦
          Mod.regularExtensionIso (AdicCompletion.transition l E W n))
    Φ.map (Mod.regularFreeExtensionIso (AdicCompletion.quotient l E W (n + 1)) e).hom ≫
        B.hom =
      ((Mod.extendScalarsComp (AdicCompletion.quotient l E W (n + 1))
        (AdicCompletion.transition l E W n)).symm ≪≫
          eqToIso (quotientFunctorEq l E W n)).hom.app M ≫
        (Mod.regularFreeExtensionIso (AdicCompletion.quotient l E W n) e).hom := by
  exact Mod.regularFreeExtensionIso_balancing
    (AdicCompletion.quotient l E W (n + 1)) (AdicCompletion.transition l E W n)
    (AdicCompletion.quotient_transition l E W n) (quotientFunctorEq l E W n) e

private theorem complex_actual (W : Scheme.{u}) (n : ℕ)
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (AdicCompletion.ring l E W)) ℤ)
    (i : ℤ) (r : ℕ)
    (e : K.X i ≅ Mod.finiteFree (AdicCompletion.ring l E W) r) :
    let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
    let B := Φ.mapBiproduct (fun _ : Fin r ↦
      Mod.regular (AdicCompletion.finiteRing l E W (n + 1))) ≪≫
        biproduct.mapIso (fun _ : Fin r ↦
          Mod.regularExtensionIso (AdicCompletion.transition l E W n))
    Φ.map (Mod.regularFreeExtensionIso (AdicCompletion.quotient l E W (n + 1)) e).hom ≫
        B.hom =
      ((Functor.mapHomologicalComplexCompIso
        ((Mod.extendScalarsComp (AdicCompletion.quotient l E W (n + 1))
          (AdicCompletion.transition l E W n)).symm ≪≫
            eqToIso (quotientFunctorEq l E W n)) (.up ℤ)).app K).hom.f i ≫
        (Mod.regularFreeExtensionIso (AdicCompletion.quotient l E W n) e).hom := by
  apply complex_balancing
  exact module_actual l E W n (K.X i) r e

private def integralComplexNamed (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ) :
    CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (AdicCompletion.ring l E W)) ℤ :=
  internalPerfectIntegralComplex l E W P

private def integralIsoNamed (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (i : ℤ) :
    (integralComplexNamed l E W P).X i ≅
      Mod.finiteFree (AdicCompletion.ring l E W) (Module.finrank (A l E) (P.X i)) :=
  integralIso l E W P hfree i

-- Transport the square before taking concrete degree components. This keeps the
-- scalar comparison in the category in which it was constructed.
private theorem square_transfer
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (G : C ⥤ D) [G.Additive]
    {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (hK : K = K') (hL : L = L') (i : ℤ) {M : C} {N : D}
    (α : (G.mapHomologicalComplex (.up ℤ)).obj K ≅ L)
    (α' : (G.mapHomologicalComplex (.up ℤ)).obj K' ≅ L')
    (eK : K.X i ≅ M) (eK' : K'.X i ≅ M)
    (eL : L.X i ≅ N) (eL' : L'.X i ≅ N) (B : G.obj M ≅ N)
    (hα : HEq α α') (heK : HEq eK eK') (heL : HEq eL eL')
    (h : G.map eK'.hom ≫ B.hom = α'.hom.f i ≫ eL'.hom) :
    G.map eK.hom ≫ B.hom = α.hom.f i ≫ eL.hom := by
  cases hK
  cases hL
  cases eq_of_heq hα
  cases eq_of_heq heK
  cases eq_of_heq heL
  exact h

/-- Fixed quotient bases commute with the specified ordinary successor balancing map. -/
theorem quotientIso_successor (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (i : ℤ) :
    let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
    let r := Module.finrank (A l E) (P.X i)
    let B := Φ.mapBiproduct (fun _ : Fin r ↦
      Mod.regular (AdicCompletion.finiteRing l E W (n + 1))) ≪≫
        biproduct.mapIso (fun _ : Fin r ↦
          Mod.regularExtensionIso (AdicCompletion.transition l E W n))
    Φ.map (quotientIso l E W P hfree (n + 1) i).hom ≫ B.hom =
      (internalPerfectOrdinaryReductionStep l E W P n).hom.f i ≫
        (quotientIso l E W P hfree n i).hom := by
  let G := Mod.extendScalars (AdicCompletion.transition l E W n)
  let K := integralComplexNamed l E W P
  let e := integralIsoNamed l E W P hfree i
  let F := Mod.extendScalars (AdicCompletion.quotient l E W (n + 1))
  let H := Mod.extendScalars (AdicCompletion.quotient l E W n)
  let β := (Functor.mapHomologicalComplexCompIso
    ((Mod.extendScalarsComp (AdicCompletion.quotient l E W (n + 1))
      (AdicCompletion.transition l E W n)).symm ≪≫
        eqToIso (quotientFunctorEq l E W n)) (.up ℤ)).app K
  exact square_transfer G
    (K := internalPerfectOrdinaryReduction l E W P (n + 1))
    (K' := (F.mapHomologicalComplex (.up ℤ)).obj K)
    (L := internalPerfectOrdinaryReduction l E W P n)
    (L' := (H.mapHomologicalComplex (.up ℤ)).obj K)
    rfl rfl i (internalPerfectOrdinaryReductionStep l E W P n) β
    (quotientIso l E W P hfree (n + 1) i)
    (Mod.regularFreeExtensionIso (AdicCompletion.quotient l E W (n + 1)) e)
    (quotientIso l E W P hfree n i)
    (Mod.regularFreeExtensionIso (AdicCompletion.quotient l E W n) e)
    (G.mapBiproduct (fun _ : Fin (Module.finrank (A l E) (P.X i)) ↦
      Mod.regular (AdicCompletion.finiteRing l E W (n + 1))) ≪≫
        biproduct.mapIso (fun _ : Fin (Module.finrank (A l E) (P.X i)) ↦
          Mod.regularExtensionIso (AdicCompletion.transition l E W n)))
    (by rfl) (by rfl) (by rfl)
    (complex_actual l E W n K i (Module.finrank (A l E) (P.X i)) e)

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
