/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Signed Hom differential in the fixed integral matrix coordinates
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- One matrix entry of a map between two integral terms in the chosen bases. -/
def mapEntry (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (i j : ℤ) (f : P.X i ⟶ P.X j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j))) : A l E :=
  (basis l E P hfree j).repr (f ((basis l E P hfree i) s)) t

/-- Composition in these coordinates is finite matrix multiplication. -/
theorem mapEntry_comp (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (i j k : ℤ) (f : P.X i ⟶ P.X j) (g : P.X j ⟶ P.X k)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X k))) :
    mapEntry l E P hfree i k (f ≫ g) s t =
      ∑ r : Fin (Module.finrank (A l E) (P.X j)),
        mapEntry l E P hfree i j f s r * mapEntry l E P hfree j k g r t := by
  classical
  have h := congrArg (fun M ↦ M t s) (LinearMap.toMatrix_comp
    (basis l E P hfree i) (basis l E P hfree j) (basis l E P hfree k) g.hom f.hom)
  simpa [mapEntry, LinearMap.toMatrix_apply, Matrix.mul_apply, mul_comm] using h

/-- The signed Hom differential is the signed sum of the two finite matrix products. -/
theorem integralEntry_differential
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (q i j : ℤ) (hij : i + (q + 1) = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j)))
    (z : (CochainComplex.moduleHomComplex P P).X q) :
    integralEntry l E P hfree (q + 1) i j hij s t
        ((CochainComplex.moduleHomComplex P P).d q (q + 1) z) =
      (∑ r : Fin (Module.finrank (A l E) (P.X (i + q))),
        integralEntry l E P hfree q i (i + q) rfl s r z *
          mapEntry l E P hfree (i + q) j (P.d (i + q) j) r t) +
      (q + 1).negOnePow •
        (∑ r : Fin (Module.finrank (A l E) (P.X (i + 1))),
          mapEntry l E P hfree i (i + 1) (P.d i (i + 1)) s r *
            integralEntry l E P hfree q (i + 1) j (by omega) r t z) := by
  change mapEntry l E P hfree i j
    ((CochainComplex.HomComplex.δ q (q + 1) z).v i j hij) s t = _
  rw [CochainComplex.HomComplex.δ_v q (q + 1) rfl z i j hij (i + q) (i + 1)
    (by omega) rfl]
  change (basis l E P hfree j).repr
      ((P.d (i + q) j) ((z.v i (i + q) rfl) ((basis l E P hfree i) s)) +
        (q + 1).negOnePow •
          (z.v (i + 1) j (by omega)) ((P.d i (i + 1)) ((basis l E P hfree i) s))) t = _
  simp only [map_add, Finsupp.add_apply, Units.smul_def, map_zsmul, Finsupp.smul_apply]
  change mapEntry l E P hfree i j (z.v i (i + q) rfl ≫ P.d (i + q) j) s t +
    ((q + 1).negOnePow : ℤ) •
      mapEntry l E P hfree i j (P.d i (i + 1) ≫ z.v (i + 1) j (by omega)) s t = _
  rw [mapEntry_comp, mapEntry_comp]
  rfl

/-- The actual categorical scalar quotient has the same signed entry differential. -/
theorem quotientEntry_differential
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q i j : ℤ) (hij : i + (q + 1) = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j)))
    (z : (Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
      (CochainComplex.moduleHomComplex P P) (n + 1)).X q) :
    quotientEntry l E P hfree n (q + 1) i j hij s t
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).d q (q + 1) z) =
      (∑ r : Fin (Module.finrank (A l E) (P.X (i + q))),
        quotientEntry l E P hfree n q i (i + q) rfl s r z *
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
            (mapEntry l E P hfree (i + q) j (P.d (i + q) j) r t)) +
      (q + 1).negOnePow •
        (∑ r : Fin (Module.finrank (A l E) (P.X (i + 1))),
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
              (mapEntry l E P hfree i (i + 1) (P.d i (i + 1)) s r) *
            quotientEntry l E P hfree n q (i + 1) j (by omega) r t z) := by
  let Q := CochainComplex.moduleHomComplex P P
  let φ := Padic.coefficientExtensionUniformizer l E ^ (n + 1) • 𝟙 Q
  let K := Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E) Q (n + 1)
  let π : Q ⟶ K := cokernel.π φ
  have hπ : Function.Surjective (π.f q) := (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, rfl⟩ := hπ z
  have hd := ConcreteCategory.congr_hom (π.comm q (q + 1)) x
  change K.d q (q + 1) (π.f q x) = π.f (q + 1) (Q.d q (q + 1) x) at hd
  rw [hd]
  have hp (d i j : ℤ) (hij : i + d = j)
      (s : Fin (Module.finrank (A l E) (P.X i)))
      (t : Fin (Module.finrank (A l E) (P.X j))) (x : Q.X d) :
      quotientEntry l E P hfree n d i j hij s t (π.f d x) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          (integralEntry l E P hfree d i j hij s t x) := by
    exact congrArg (fun f ↦ f x) (quotientEntry_projection l E P hfree n d i j hij s t)
  simp_rw [hp]
  have h := congrArg (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    (integralEntry_differential l E P hfree q i j hij s t x)
  simpa only [map_add, map_sum, map_mul, Units.smul_def, map_zsmul] using h

/-- The quotient differential entry formula holds for locally constant families. -/
theorem locallyConstant_quotientEntry_differential (T : Type v) [TopologicalSpace T]
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q i j : ℤ) (hij : i + (q + 1) = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j)))
    (z : LocallyConstant T
      ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
        (CochainComplex.moduleHomComplex P P) (n + 1)).X q)) :
    (z.map ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
      (CochainComplex.moduleHomComplex P P) (n + 1)).d q (q + 1))).map
        (quotientEntry l E P hfree n (q + 1) i j hij s t) =
      (∑ r : Fin (Module.finrank (A l E) (P.X (i + q))),
        z.map (quotientEntry l E P hfree n q i (i + q) rfl s r) *
          LocallyConstant.const T
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
              (mapEntry l E P hfree (i + q) j (P.d (i + q) j) r t))) +
      (q + 1).negOnePow •
        (∑ r : Fin (Module.finrank (A l E) (P.X (i + 1))),
          LocallyConstant.const T
              (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
                (mapEntry l E P hfree i (i + 1) (P.d i (i + 1)) s r)) *
            z.map (quotientEntry l E P hfree n q (i + 1) j (by omega) r t)) := by
  apply LocallyConstant.ext
  intro x
  let B := Padic.coefficientExtensionRing l E (n + 1)
  change _ = (LocallyConstant.evalRingHom (Y := B) x) _ +
    (q + 1).negOnePow • (LocallyConstant.evalRingHom (Y := B) x) _
  rw [map_sum, map_sum]
  exact quotientEntry_differential l E P hfree n q i j hij s t (z x)

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
