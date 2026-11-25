/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Trace
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The trace on perfect complexes is the alternating sum of the traces

Let `R` be a commutative ring. A bounded complex `P` of finitely generated free `R`-modules
is a dualizable object of the derived category `D(R)`, and the categorical trace
`CategoryTheory.MonoidalCategory.trace` of a chain endomorphism `v` of `P` is an
endomorphism of the unit object, i.e. an element of `R`. This file states that it is the
alternating sum `∑ i, (-1) ^ i * Tr_R (v ^ i ∣ P ^ i)` of the ordinary module traces of the
components of `v`.

## Main results

- `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`: the alternating sum
  formula, for the Koszul braiding `DerivedCategory.braidedCategory'` of the derived tensor
  product.
- `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace_of_braiding_hom_μ`: the
  same for any braiding for which `Qh` is braided on K-flat complexes.

## Implementation notes

Three things are hypotheses rather than instances.

* `Abelian.HasFunctorialFlatResolution (ModuleCat R)` is assumed only so that the monoidal
  structure on `DerivedCategory (ModuleCat R)` is available, and is *the* derived tensor
  product `- ⊗ᴸ_R -` supplied by
  `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`, rather than an
  arbitrary one. Without it the statement would be about an unspecified tensor product.
* Perfectness of `P` is rendered as an object `K` of `D(R)` with `[HasRightDual K]` together
  with an isomorphism `e : K ≅ Q.obj P` intertwining `w` and `Q.map v`, since this project
  has no `Perf R` and does not prove that a bounded complex of finitely generated free
  modules is dualizable. The categorical trace is conjugation invariant, so the choice of
  `e` does not matter.
* The components of `P` are assumed `Module.Free`, not merely `Module.Projective`:
  Mathlib's `LinearMap.trace R M` is defined to be `0` unless `M` has a finite basis, so
  over a ring with a non-free finitely generated projective module the projective form of
  the statement is false.

The right hand side is an element of `R`, read in `End (𝟙_ D(R))` through the canonical
`R`-algebra structure that `R`-linearity of `D(R)` puts on it; no choice of an isomorphism
`End (𝟙_ D(R)) ≃ R` is needed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

open Functor.LaxMonoidal

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]

/-- The image of a scalar `r : R`, as an endomorphism of the unit of `ModuleCat R`, under the
functor `ModuleCat R ⥤ D(R)` placing a module in degree `0` is `r`, as an endomorphism of the
unit of `D(R)`. -/
lemma ε_Qh_comp_map_single_map_algebraMap_comp_inv (r : R) :
    ε Qh ≫ Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map
          ((algebraMap R (End (𝟙_ (ModuleCat.{u} R))) r)).asHom)) ≫ inv (ε Qh) =
      (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R)))) r).asHom := by
  have : (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).Linear R :=
    inferInstanceAs ((CochainComplex.singleFunctor _ 0).Linear R)
  have hF := Functor.map_smul (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0 ⋙
    HomotopyCategory.quotient _ (.up ℤ) ⋙ Qh) r (𝟙 (𝟙_ (ModuleCat.{u} R)))
  rw [CategoryTheory.Functor.map_id] at hF
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    End.smul_asHom, End.smul_asHom, End.one_asHom, End.one_asHom]
  erw [hF]
  rw [Linear.smul_comp, Linear.comp_smul]
  erw [Category.id_comp]
  erw [Category.id_comp, IsIso.inv_id]

/-- Blueprint `proposition-properties-trace`, via `proposition-properties-trace--4`: for a
commutative ring `R`, a bounded complex `P` of finitely generated free `R`-modules and a chain
endomorphism `v : P ⟶ P`, the categorical trace of `v` on the object of `D(R)` represented by `P` is
the alternating sum of the ordinary `R`-module traces of the components of `v`:

`tr_R (v ∣ P) = ∑ i, (-1) ^ i * Tr_R (v ^ i ∣ P ^ i)`,

provided the braiding of `D(R)` is the Koszul one in the sense that the lax monoidal structure
of `Qh : K(R) ⥤ D(R)` intertwines the Koszul braiding of K-flat complexes with the braiding
of `D(R)`. This holds for the braiding `DerivedCategory.braidedCategory'` of the derived tensor
product (`DerivedCategory.braiding_hom_μ_Qh`). -/
theorem trace_eq_algebraMap_sum_negOnePow_linearMapTrace_of_braiding_hom_μ
    [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]
    (hβ : ∀ X Y : HomotopyCategory (ModuleCat.{u} R) (.up ℤ),
      (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X →
        (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat Y →
          (β_ (Qh.obj X) (Qh.obj Y)).hom ≫ μ Qh Y X = μ Qh X Y ≫ Qh.map (β_ X Y).hom)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i))
    (hfree : ∀ i, Module.Free R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (K : DerivedCategory (ModuleCat.{u} R)) [HasRightDual K] (w : K ⟶ K)
    (e : K ≅ Q.obj P) (hw : w ≫ e.hom = e.hom ≫ Q.map v) :
    MonoidalCategory.trace w =
      (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R))))
        (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v.f i).hom)).asHom := by
  obtain ⟨a, ha⟩ := s.bddBelow
  obtain ⟨b, hb⟩ := s.bddAbove
  have : P.IsStrictlyGE a :=
    (P.isStrictlyGE_iff a).2 fun i hi ↦ hs i fun h ↦ (not_le.2 hi) (ha h)
  have : P.IsStrictlyLE b :=
    (P.isStrictlyLE_iff b).2 fun i hi ↦ hs i fun h ↦ (not_le.2 hi) (hb h)
  let _ (n : ℤ) : HasRightDual (P.X n) := ModuleCat.hasRightDualOfFree (P.X n)
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let φ : K ≅ Qh.obj (H.obj P) := e ≪≫ ((quotientCompQhIso _).app P).symm
  let _ : ExactPairing (Qh.obj (H.obj P)) Kᘁ := exactPairingCongrLeft φ.symm
  let _ : HasRightDual (Qh.obj (H.obj P)) := ⟨Kᘁ⟩
  rw [trace_eq_of_iso φ w (Qh.map (H.map v)) ?_, trace_Qh_map_quotient_map hβ P a b v]
  · let _ := CochainComplex.hasRightDual P a b
    have hT : MonoidalCategory.trace v = (HomologicalComplex.single _ (.up ℤ) 0).map
        (algebraMap R (End (𝟙_ (ModuleCat.{u} R)))
          (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v.f i).hom)).asHom := by
      refine HomologicalComplex.from_single_hom_ext ?_
      rw [CochainComplex.trace_f_zero_eq P a b v, HomologicalComplex.single_map_f_self]
      congr 2
      have key (i : ℤ) : (i.negOnePow : ℤ) • MonoidalCategory.trace (v.f i) =
          (algebraMap R (End (𝟙_ (ModuleCat.{u} R)))
            ((i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v.f i).hom)).asHom := by
        rw [ModuleCat.trace_eq_algebraMap_linearMapTrace, map_zsmul, End.zsmul_asHom]
      rw [map_sum, End.sum_asHom]
      refine (Finset.sum_subset (fun i hi ↦ Finset.mem_Icc.2 ⟨ha hi, hb hi⟩)
        fun i _ hi ↦ ?_).symm.trans (Finset.sum_congr rfl fun i _ ↦ key i)
      rw [key i, (hs i hi).eq_of_src (v.f i) 0, ModuleCat.hom_zero, map_zero, smul_zero, map_zero,
        End.zero_asHom]
    rw [hT, ε_Qh_comp_map_single_map_algebraMap_comp_inv]
  · rw [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, reassoc_of% hw, Category.assoc,
      (quotientCompQhIso _).inv.naturality v]
    rfl


/-- Blueprint `proposition-properties-trace`, via `proposition-properties-trace--4`: for the
braiding `DerivedCategory.braidedCategory'` of the derived tensor product on `D(R)` (the Koszul
braiding of complexes, descended along K-flat resolutions), the categorical trace of a chain
endomorphism `v` of a bounded complex `P` of finitely generated free `R`-modules is the alternating
sum of the traces of its components:

`tr_R (v ∣ P) = ∑ i, (-1) ^ i * Tr_R (v ^ i ∣ P ^ i)`. -/
theorem trace_eq_algebraMap_sum_negOnePow_linearMapTrace
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i))
    (hfree : ∀ i, Module.Free R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (K : DerivedCategory (ModuleCat.{u} R)) [HasRightDual K] (w : K ⟶ K)
    (e : K ≅ Q.obj P) (hw : w ≫ e.hom = e.hom ≫ Q.map v) :
    letI := braidedCategory' (ModuleCat.{u} R)
    MonoidalCategory.trace w =
      (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R))))
        (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v.f i).hom)).asHom :=
  letI := braidedCategory' (ModuleCat.{u} R)
  trace_eq_algebraMap_sum_negOnePow_linearMapTrace_of_braiding_hom_μ
    (fun X Y _ _ ↦ braiding_hom_μ_Qh X Y) P v s hs hfree hfin K w e hw

end DerivedCategory
