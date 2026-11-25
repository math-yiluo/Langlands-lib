/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart
import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreFlatCriterion
import WeilConjectures.RingTheory.OpenFlatLocus

/-! # Affine fibre Cohen-Macaulay locus

Source: Stacks Project, Tags 00RI, 00RH, 00N8.
(blueprint: lem-sbc-affine-fibre-cohen-macaulay-locus-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem isOpen_flat_stalks_spec
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    [LocallyOfFinitePresentation (Spec.map f)] :
    IsOpen {z : Spec S | ((Spec.map f).stalkMap z).hom.Flat} := by
  have hf : f.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance
  algebraize [f.hom]
  have : Algebra.FinitePresentation R S := hf
  have heq (z : PrimeSpectrum S) :
      ((Spec.map f).stalkMap z).hom.Flat ↔ Module.Flat R (Localization.AtPrime z.asIdeal) := by
    rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso f z)]
    algebraize [Localization.localRingHom (z.comap f.hom).asIdeal z.asIdeal f.hom rfl]
    have : IsScalarTower R (Localization.AtPrime (z.comap f.hom).asIdeal)
        (Localization.AtPrime z.asIdeal) :=
      .of_algebraMap_eq fun r ↦ (Localization.localRingHom_to_map _ _ _ rfl r).symm
    change Module.Flat (Localization.AtPrime (z.comap f.hom).asIdeal)
      (Localization.AtPrime z.asIdeal) ↔ _
    exact Module.flat_iff_of_isLocalization
      (Localization.AtPrime (z.comap f.hom).asIdeal) (z.comap f.hom).asIdeal.primeCompl
      (Localization.AtPrime z.asIdeal)
  have hflat (z : PrimeSpectrum S) :
      Module.Flat R (Localization.AtPrime z.asIdeal) ↔
        Module.Flat R (LocalizedModule z.asIdeal.primeCompl S) := by
    let e := (IsLocalizedModule.iso z.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime z.asIdeal))).restrictScalars R
    exact ⟨fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e, fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e.symm⟩
  change IsOpen {z : PrimeSpectrum S | ((Spec.map f).stalkMap z).hom.Flat}
  simpa only [heq, hflat] using
    (Module.isOpen_setOf_flat_localizedModule (R := R) (S := S) (M := S))

private theorem isOpen_flat_stalks_affine
    {E L : Scheme.{u}} (p : E ⟶ L) [IsAffine E] [IsAffine L]
    [LocallyOfFinitePresentation p] :
    IsOpen {z : E | (p.stalkMap z).hom.Flat} := by
  let p' := E.isoSpec.inv ≫ p ≫ L.isoSpec.hom
  have h' : IsOpen {z : Spec Γ(E, ⊤) | (p'.stalkMap z).hom.Flat} := by
    have : LocallyOfFinitePresentation (Spec.map (Spec.preimage p')) := by
      rw [Spec.map_preimage]
      dsimp [p']
      infer_instance
    rw [← Spec.map_preimage p']
    exact isOpen_flat_stalks_spec _
  convert h'.preimage E.isoSpec.hom.continuous using 1
  ext z
  change (p.stalkMap z).hom.Flat ↔
    ((E.isoSpec.inv ≫ p ≫ L.isoSpec.hom).stalkMap (E.isoSpec.hom z)).hom.Flat
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_left_isIso]
  have he : E.isoSpec.inv (E.isoSpec.hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [he]

/-- The fibre depth-equals-dimension locus for a flat finitely presented map
between affine schemes is open.

Source: Stacks Project, Tag 00RI, via Tag 00RH; Tag 00N8.
Proof: Identify X and T with spectra of their global section rings B and A.
Flatness and local finite presentation give a flat finitely presented map A → B.
The fibre stalk at q is the local ring B_q ⊗_A κ(p), where p is the inverse image
of q. It is Noetherian, since B is finitely presented over A and κ(p) is a field.
Its self-module is Cohen-Macaulay precisely when its depth equals its dimension.
For completeness, the affine openness argument of Tag 00RH is as follows. At a
Cohen-Macaulay fibre point of relative dimension d, localize B away from q to get
a quasi-finite map A[t₁,…,t_d] → B (Tag 00QE). On the fibre at p its localization
at q is flat by the Cohen-Macaulay criterion for quasi-finite maps over polynomial
rings (Tag 00RE). Since B is flat over A, the fibrewise flatness criterion
(Tag 00R7) implies flatness over the polynomial ring at q. Openness of flatness
(Tag 00RC) gives a further principal neighborhood where this polynomial map is
flat. At every point of that neighborhood its fibre over A is a flat
quasi-finite algebra over a polynomial ring over a field, and Tag 00RE makes the
local fibre ring Cohen-Macaulay. Thus each point of the locus has a principal
open neighborhood contained in the locus. The union of these neighborhoods is
open, and transport along the affine scheme isomorphisms gives the result.
There are no points when B is the zero ring; the locus is then empty.
(blueprint: lem-sbc-affine-fibre-cohen-macaulay-locus-open) -/
theorem isOpen_fibre_depth_eq_ringKrullDim_of_isAffine
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen {y : X |
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, n, e, hfp, hqf, he, hdim⟩ :=
    exists_quasiFinite_polynomial_chart f y
  let := hU
  let := hfp
  let := hqf
  have hopen := isOpen_flat_stalks_affine e
  refine ⟨U.ι '' {x | (e.stalkMap x).hom.Flat}, ?_,
    U.ι.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ((polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension f U n e he x).mp hx).1
  · refine ⟨⟨y, hyU⟩, ?_, rfl⟩
    exact (polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension
      f U n e he ⟨y, hyU⟩).mpr ⟨hy, hdim⟩

end AlgebraicGeometry
