/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.Algebra.Homology.FilteredFreeResolution
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Filtered free resolutions in a larger carrier universe

Source: Stacks Project, Remark 15.60.11 (Tag 09PB) and Lemma 22.20.4 (Tag 09KP).
(blueprint: lem-pc-large-filtered-free-resolution).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The filtered free resolution construction with carriers in `Type (max u v)`.
Source: Stacks Project, Remark 15.60.11 (Tag 09PB), Lemma 22.20.4 (Tag 09KP).
(blueprint: lem-pc-large-filtered-free-resolution).

Proof: let `B = ULift.{v} A`, a ring in the carrier universe. Restrict the scalar
structure of `M` along `B ≃+* A`. Apply `exists_filtered_free_resolution` over `B`.
Transport its complex, augmentation, filtration, inclusions and steps through the
inverse equivalence of module categories, degree by degree. An equivalence of abelian
categories preserves quasi-isomorphisms, zero objects, monomorphisms, cokernels and
coproducts. Transport the splitting maps through this functor as well. Its underlying
module carriers are unchanged, so elementwise exhaustion is preserved. The transported
rank-one `B`-module is `ULift.{v} A` with its usual `A`-action. The transported quotient
isomorphisms give the final clause. Empty bases and the zero complex cause no exception. -/
theorem exists_large_filtered_free_resolution {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (q : P ⟶ M),
      QuasiIso q ∧
      ∃ (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
        (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1)),
        IsZero (F 0) ∧
        (∀ n, Mono (ι n)) ∧
        (∀ n, step n ≫ ι (n + 1) = ι n) ∧
        (∀ (k : ℤ) (x : P.X k), ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x) ∧
        (∀ (n : ℕ) (k : ℤ),
          ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
            (step n).f k ≫ r = 𝟙 ((F n).X k)) ∧
        (∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
          Nonempty (cokernel (step n) ≅
            ∐ (fun i : I =>
              (HomologicalComplex.single (ModuleCat.{max u v} A) (ComplexShape.up ℤ) (degree i)).obj
                (ModuleCat.of A (ULift.{v} A))))) := by
  classical
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{v} A ≃+* A)
  let EC := E.mapHomologicalComplex (ComplexShape.up ℤ)
  let G := EC.inverse
  let : G.IsEquivalence := EC.isEquivalence_inverse
  obtain ⟨P, q, hq, F, ι, step, hzero, hmono, hcompat, hexhaustive, hsplit, hquot⟩ :=
    exists_filtered_free_resolution (EC.functor.obj M)
  let : QuasiIso q := hq
  refine ⟨G.obj P, G.map q ≫ EC.unitIso.inv.app M, ?_,
    (fun n ↦ G.obj (F n)), (fun n ↦ G.map (ι n)), (fun n ↦ G.map (step n)),
    G.map_isZero hzero, ?_, ?_, ?_, ?_, ?_⟩
  · have : QuasiIso (G.map q) := by
      change QuasiIso ((E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map q)
      infer_instance
    infer_instance
  · intro n
    let : Mono (ι n) := hmono n
    infer_instance
  · intro n
    rw [← G.map_comp, hcompat]
  · intro k x
    exact hexhaustive k x
  · intro n k
    obtain ⟨r, hr⟩ := hsplit n k
    refine ⟨E.inverse.map r, ?_⟩
    change E.inverse.map ((step n).f k) ≫ E.inverse.map r = _
    rw [← E.inverse.map_comp, hr, E.inverse.map_id]
    rfl
  · intro n
    obtain ⟨I, degree, he⟩ := hquot n
    refine ⟨I, degree, ⟨?_⟩⟩
    let B (i : I) :=
      (HomologicalComplex.single (ModuleCat.{max u v} (ULift.{v} A))
        (ComplexShape.up ℤ) (degree i)).obj (ModuleCat.of (ULift.{v} A) (ULift.{v} A))
    refine (PreservesCokernel.iso G (step n)).symm ≪≫ G.mapIso he.some ≪≫
      (asIso (sigmaComparison G B)).symm ≪≫ Sigma.mapIso (fun i ↦ ?_)
    exact (HomologicalComplex.singleMapHomologicalComplex E.inverse
      (ComplexShape.up ℤ) (degree i)).app _

end CochainComplex
