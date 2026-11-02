import Langlands.AlgebraicGeometry.LinearSystem.SourceEquivariance
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Coordinate action induced by pullback of a finite section basis -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) {L : LineBundle X}
  (f : X ⟶ X) (w : f ≫ p = p)
  (b : ((LineBundle.pullback f).obj L).obj ≅ L.obj)

/-- Pullback followed by the specified bundle isomorphism, as a linear
endomorphism of the actual sections over the base field. -/
def sectionTransport :
    (relativeGlobalSections p).obj L.obj →ₗ[K]
      (relativeGlobalSections p).obj L.obj where
  toFun := fun s ↦ b.hom.app ⊤ (pullbackSection f L.obj s)
  map_add' s t := by
    change b.hom.app ⊤ (pullbackSection f L.obj (s + t)) = _
    rw [pullbackSection_add, map_add]
  map_smul' a s := by
    change b.hom.app ⊤ (pullbackSection f L.obj
      (Scheme.Modules.scalarsFromBase p a • (show GlobalSections L.obj from s))) =
        Scheme.Modules.scalarsFromBase p a • b.hom.app ⊤ (pullbackSection f L.obj s)
    rw [pullbackSection_smul]
    have ha : f.appTop (Scheme.Modules.scalarsFromBase p a) =
        Scheme.Modules.scalarsFromBase p a := by
      have h := congrArg (fun h : K →+* Γ(X, ⊤) ↦ h a) (scalarsFromBase_comp f p)
      simpa only [w, RingHom.comp_apply] using h.symm
    rw [ha, Scheme.Modules.Hom.app_smul]

@[simp]
lemma sectionTransport_apply (s : (relativeGlobalSections p).obj L.obj) :
    sectionTransport p f w b s = b.hom.app ⊤ (pullbackSection f L.obj s) := rfl

/-- Pullback along an actual scheme isomorphism and bundle transport reflect
zero of an actual section. -/
lemma sectionTransport_eq_zero_iff [IsIso f]
    (s : (relativeGlobalSections p).obj L.obj) :
    sectionTransport p f w b s = 0 ↔ s = 0 := by
  change b.hom.app ⊤ (pullbackSection f L.obj s) = 0 ↔ s = 0
  rw [← sectionHom_eq_zero_iff, sectionHom_naturality,
    comp_eq_zero_iff_of_mono, sectionHom_eq_zero_iff]
  exact pullbackSection_iso_eq_zero_iff f L.obj s

/-- Actual section transport is injective for a scheme isomorphism. -/
lemma sectionTransport_injective [IsIso f] :
    Function.Injective (sectionTransport p f w b) :=
  LinearMap.ker_eq_bot.mp <| LinearMap.ker_eq_bot'.mpr
    (fun s hs ↦ (sectionTransport_eq_zero_iff p f w b s).mp hs)

variable {n : ℕ}
  (basis : Module.Basis (Fin (n + 1)) K ((relativeGlobalSections p).obj L.obj))

/-- The actual section transport is an equivalence when a finite basis is
specified. -/
def sectionTransportEquiv [IsIso f] :
    (relativeGlobalSections p).obj L.obj ≃ₗ[K]
      (relativeGlobalSections p).obj L.obj := by
  letI := basis.finiteDimensional_of_finite
  exact LinearEquiv.ofInjectiveEndo (sectionTransport p f w b)
    (sectionTransport_injective p f w b)

@[simp]
lemma sectionTransportEquiv_apply [IsIso f]
    (s : (relativeGlobalSections p).obj L.obj) :
    sectionTransportEquiv p f w b basis s = sectionTransport p f w b s := rfl

/-- The coordinate equivalence is obtained by dualizing section transport and
using the dual basis. This gives the transpose coefficient convention required
by the projective linear action. -/
def sectionCoordinateEquiv [IsIso f] :
    (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K) :=
  basis.dualBasis.equivFun.symm |>.trans
    (sectionTransportEquiv p f w b basis).dualMap |>.trans basis.dualBasis.equivFun

/-- Each coordinate matrix entry is the corresponding coefficient of the
transported section. -/
lemma sectionCoordinateEquiv_single [IsIso f] (i j : Fin (n + 1)) :
    sectionCoordinateEquiv p f w b basis (Pi.single j 1) i =
      basis.repr (sectionTransport p f w b (basis i)) j := by
  have hj : basis.dualBasis.equivFun.symm (Pi.single j 1) = basis.dualBasis j := by
    apply basis.dualBasis.equivFun.injective
    ext k
    simp [Pi.single_apply]
  simp only [sectionCoordinateEquiv, LinearEquiv.trans_apply, hj,
    Module.Basis.dualBasis_equivFun, LinearEquiv.dualMap_apply,
    sectionTransportEquiv_apply, Module.Basis.dualBasis_apply]

/-- Pullback carries the full ordered basis of sections to the coordinate
change constructed from its actual action on sections. -/
lemma transportedPullbackSections_basis [IsIso f] :
    transportedPullbackSections (L := L) (fun i ↦ basis i) f b =
      linearChangeSections (L := L) p (fun i ↦ basis i)
        (sectionCoordinateEquiv p f w b basis).toLinearMap := by
  funext i
  change sectionTransport p f w b (basis i) =
    ∑ j, Scheme.Modules.scalarsFromBase p
      (sectionCoordinateEquiv p f w b basis (Pi.single j 1) i) •
        (show GlobalSections L.obj from basis j)
  simp only [sectionCoordinateEquiv_single]
  exact (basis.sum_repr (sectionTransport p f w b (basis i))).symm

/-- The actual projective morphism defined by a generating finite basis is
equivariant for the coordinate equivalence constructed from bundle pullback. -/
lemma linearSystemMap_basis_equivariant [IsIso f]
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (basis i)) :
    f ≫ linearSystemMap p hs = linearSystemMap p hs ≫
      linearAction K n (sectionCoordinateEquiv p f w b basis) :=
  linearSystemMap_equivariant (L := L) (fun i ↦ basis i) p f w b
    (sectionCoordinateEquiv p f w b basis)
    (transportedPullbackSections_basis p f w b basis) hs

end Langlands.AlgebraicGeometry.LinearSystem
