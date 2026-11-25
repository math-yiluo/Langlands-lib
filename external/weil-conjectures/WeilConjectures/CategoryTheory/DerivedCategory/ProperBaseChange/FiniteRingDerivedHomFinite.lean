/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

import WeilConjectures.RingTheory.FiniteConeFreeModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Finiteness of derived maps over a finite ring -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private theorem finite_chain_maps
    (B : Type u) [CommRing B]
    (P G : CochainComplex (ModuleCat.{u} B) ℤ)
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hPfin : ∀ n : ℤ, Finite (P.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Finite (P ⟶ G) := by
  classical
  obtain ⟨a, b, hG⟩ := hG
  have (n : ℤ) : Finite (P.X n ⟶ G.X n) := by
    have := hPfin n
    have := hGfin n
    exact Finite.of_injective (fun f : P.X n ⟶ G.X n ↦ f.hom.toFun)
      (fun _ _ h ↦ ModuleCat.hom_ext (LinearMap.ext (congrFun h)))
  let S := Finset.Icc a b
  let ev : (P ⟶ G) → (∀ n : S, P.X n ⟶ G.X n) := fun f n ↦ f.f n
  apply Finite.of_injective ev
  intro f g h
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n ∈ S
  · exact congrFun h ⟨n, hn⟩
  · exact (hG n (by simpa only [S, Finset.mem_Icc, not_and_or, not_le] using hn)).eq_of_tgt _ _

private theorem derived_maps_surjective
    (B : Type u) [CommRing B]
    (P G : CochainComplex (ModuleCat.{u} B) ℤ)
    [P.IsKProjective] : Function.Surjective
      (DerivedCategory.Q.map : (P ⟶ G) → _) := by
  intro f
  obtain ⟨h, hh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj G)).surjective
      ((DerivedCategory.quotientCompQhIso _).hom.app P ≫ f ≫
        (DerivedCategory.quotientCompQhIso _).inv.app G)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective h
  refine ⟨g, ?_⟩
  have hn := (DerivedCategory.quotientCompQhIso _).hom.naturality g
  dsimp at hn
  rw [hh] at hn
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app P)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn.symm

/-- Derived morphisms between bounded complexes of finite modules over a finite ring form
  a finite set.

Source: Stacks Project, Tags 064U and 09BE; finite-module Hom argument in
`lem-weil-pbc-finite-ring-derived-local-constancy`, steps 2 and 6.
(blueprint: lem-weil-pbc-finite-ring-derived-hom-finite)

Proof: Each cone of a finite free complex mapping to E has finite terms, hence finite
cohomology. Apply the finite-cone free-model theorem to obtain a bounded-above finite
free resolution P of E. Such a complex is K-projective, so every derived map P to G is
represented by a chain map. Only the finitely many degrees in the support of G matter,
and every degreewise map belongs to a finite set of functions between finite sets.
Thus the set of chain maps is finite, and so is its quotient of derived maps. The
quasi-isomorphism P to E transports this finiteness to the required Hom set. Zero
complexes and empty support intervals are included in the same argument. -/
theorem finite_derived_hom_of_bounded_finite
    (B : Type u) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (hGfin : ∀ n : ℤ, Finite (G.X n)) :
    Finite (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G) := by
  classical
  obtain ⟨a, b, hE⟩ := hE
  have hvan : ∀ n : ℤ, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
        (DerivedCategory.Q.obj E)) := by
    intro n hn
    have hz := hE n (Or.inr hn)
    have hh : IsZero (E.homology n) := (E.sc n).isZero_homology_of_isZero_X₂ hz
    exact hh.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) n).app E)
  have finite_homology (C : CochainComplex (ModuleCat.{u} B) ℤ)
      (hf : ∀ n, Finite (C.X n)) (n : ℤ) :
      Finite ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
        (DerivedCategory.Q.obj C)) := by
    have := hf n
    have : Finite (C.cycles n) := Finite.of_injective (C.iCycles n)
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
    have : Finite (C.homology n) := Finite.of_surjective (C.homologyπ n)
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    have : Finite ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
      (ComplexShape.up ℤ) n).obj C) := ‹Finite (C.homology n)›
    exact Finite.of_surjective
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) n).inv.app C)
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have hcone : ∀ (F : CochainComplex (ModuleCat.{u} B) ℤ) (l r : ℤ),
      F.IsStrictlyGE l → F.IsStrictlyLE r →
      (∀ n : ℤ, Module.Free B (F.X n) ∧ Module.Finite B (F.X n)) →
      ∀ (f : F ⟶ E) (n : ℤ),
        (∀ i : ℤ, n < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
            (DerivedCategory.Q.obj (CochainComplex.mappingCone f)))) →
        Module.Finite B
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
            (DerivedCategory.Q.obj (CochainComplex.mappingCone f))) := by
    intro F l r _ _ hF f n _
    have hf (i : ℤ) : Finite ((CochainComplex.mappingCone f).X i) := by
      have := hEfin i
      have : Module.Finite B (F.X (i + 1)) := (hF (i + 1)).2
      have : Finite (F.X (i + 1)) := Module.finite_of_finite B
      let e : (CochainComplex.mappingCone f).X i ≅ F.X (i + 1) ⊞ E.X i :=
        HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl
      have : Finite ↑(F.X (i + 1) ⊞ E.X i : ModuleCat B) := by
        exact Finite.of_equiv (F.X (i + 1) × E.X i)
          (ModuleCat.biprodIsoProd _ _).toLinearEquiv.symm.toEquiv
      exact Finite.of_equiv _ e.toLinearEquiv.symm.toEquiv
    have := finite_homology (CochainComplex.mappingCone f) hf n
    exact Module.Finite.of_finite
  obtain ⟨P, hP, hPfree, f, hf⟩ :=
    DerivedCategory.exists_finiteFree_model_of_finite_cones B E b hvan hcone
  have : P.IsStrictlyLE b := hP
  have (n : ℤ) : Projective (P.X n) := by
    have : Module.Free B (P.X n) := (hPfree n).1
    infer_instance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  have hPfin (n : ℤ) : Finite (P.X n) := by
    have : Module.Finite B (P.X n) := (hPfree n).2
    exact Module.finite_of_finite B
  have : Finite (P ⟶ G) := finite_chain_maps B P G hG hPfin hGfin
  have : Finite (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj G) :=
    Finite.of_surjective _ (derived_maps_surjective B P G)
  have : QuasiIso f := hf
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} B) f).mpr hf
  exact Finite.of_equiv _
    (Iso.homCongr (asIso (DerivedCategory.Q.map f)) (Iso.refl _))

end DerivedCategory
