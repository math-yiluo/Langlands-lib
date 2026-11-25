/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierClass
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDiagonalClassDetection
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicClassRestriction
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteResidueFunctor
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionSiteComparison
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonExt
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import all Mathlib.Logic.Small.Defs

/-! # Finite Cartier classes detect endomorphisms of their roots line

Source: diagonal coefficient changes (3), supported positive Kummer normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mapExactFunctor
  DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

private theorem reduced_eq_canonical
    (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit ((l ^ r : ℕ) : Γ(Z, ⊤))) :
    cartierResidueReducedPro l (Fact.out : l.Prime) r i hI hZ =
      geoCartierCanonicalClass (cartierResidueRing.{u} l r) (l ^ r)
        (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ := by
  let A := cartierResidueRing.{u} l r
  let : Finite A := cartierResidue_finite l (Fact.out : l.Prime) r
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hu⟩ :=
    cartier_reduction_site_comparison l (Fact.out : l.Prime) r hr A
      (cartierResidue_cast l r) i hI hZ
  symm
  apply hu
  refine ⟨Etale.geoCartierEtaleClass A (l ^ r)
    (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ, ?_, ?_⟩
  · exact (Etale.geoCartierEtaleClass_spec A (l ^ r)
      (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ).1
  · exact geoCartierCanonicalClass_comparison A (l ^ r)
      (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ

private theorem canonical_postcomp_injective
    (Y : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hW : IsUnit (N : Γ(diagonalSurface Y, ⊤))) :
    Function.Injective (fun f : geoCartierLine A N hA (diagonalSurface Y) ⟶
        geoCartierLine A N hA (diagonalSurface Y) ↦
      (geoCartierCanonicalClass A N hN hA (diagonalImmersion Y)
        (diagonalImmersion_cartier Y) hW).comp (Ext.mk₀ f) (add_zero 2)) := by
  let V := comparisonUpperStar (ModuleCat.{u + 1} A) (diagonalSurface Y)
  let L := Scheme.finiteEtaleTateLine (diagonalSurface Y) N A hA
  intro f k heq
  let f₀ : L ⟶ L := V.preimage f
  let k₀ : L ⟶ L := V.preimage k
  have hf : V.map f₀ = f := V.map_preimage f
  have hk : V.map k₀ = k := V.map_preimage k
  have hfk : f₀ = k₀ := by
    apply Etale.finiteEtaleDiagonalClass_postcomp_injective Y N hN A hA
      (diagonalImmersion_cartier Y) hW
    apply (comparison_mapExt_bijective (ModuleCat.{u + 1} A) (diagonalSurface Y)
      _ _ 2).injective
    dsimp only
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, hf, hk]
    rw [← geoCartierCanonicalClass_comparison A N hN hA (diagonalImmersion Y)
      (diagonalImmersion_cartier Y) hW]
    simpa only [Ext.comp_assoc_of_third_deg_zero] using
      congrArg (fun z ↦ (Ext.mk₀ (geoCartierSourceComparison A (diagonalImmersion Y))).comp
        z (zero_add 2)) heq
  exact hf.symm.trans ((congrArg V.map hfk).trans hk)

/-- Postcomposition of the positive finite Cartier class detects ordinary
endomorphisms of its finite roots line, after restriction of finite scalars.
Source: diagonal coefficient changes (3), and the arbitrary-base finite P1
integral normalization of the supported diagonal class.
(blueprint: lem-diagonal-finite-cartier-endomorphism-detection).

Proof: fullness of finite scalar restriction lifts the endomorphisms to the
finite module category. Translate the assumed equality into equality of the
restricted Ext composites; supported cyclic class restriction detects their
equality. The uniqueness clause of the Cartier reduction/site comparison
identifies the residue reduction with the canonical comparison class. Full
faithfulness of site comparison lifts the finite pro-etale line endomorphisms
to the etale line. Precomposition by the supported source mate and injectivity
of the comparison map on Ext give equality of the etale class composites.
Apply finiteEtaleDiagonalClass_postcomp_injective and map the resulting
ordinary equality through comparison and scalar restriction. Only the
supported-source Ext map is used injectively; no faithfulness of a functor
on arbitrary derived arrows is asserted. -/
theorem finiteCartierClass_endomorphism_injective
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤))) (n : ℕ) :
    let L := (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y))
    Function.Injective (fun f : L ⟶ L ↦
      (finiteCartierClass l Y hY n).hom ≫
        ((DerivedCategory.singleFunctor _ 0).map f)⟦(2 : ℤ)⟧') := by
  dsimp only
  let U := diagonalFiniteToPadic l n (diagonalSurface Y)
  let L := geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
    (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
  let δ := cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
    (diagonalImmersion Y) (diagonalImmersion_cartier Y)
    (diagonalSurface_power_unit l Y hY n)
  let := (finiteResidueRestriction_full_faithful l n (diagonalSurface Y)).1
  intro f k heq
  let f₀ : L ⟶ L := U.preimage f
  let k₀ : L ⟶ L := U.preimage k
  have hf : U.map f₀ = f := U.map_preimage f
  have hk : U.map k₀ = k := U.map_preimage k
  have hδ : δ.comp (Ext.mk₀ f₀) (add_zero 2) =
      δ.comp (Ext.mk₀ k₀) (add_zero 2) := by
    apply DiagonalCoefficients.diagonalCyclicClass_restrict_injective l Y n
    apply Ext.ext
    simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_hom,
      Ext.mk₀_hom, ShiftedHom.comp_mk₀, hf, hk, finiteCartierClass,
      diagonalExactFunctorExtImage, Nat.cast_ofNat, δ, U] using heq
  have hfk : f₀ = k₀ := by
    apply canonical_postcomp_injective Y (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (diagonalResidue.{u} l n)
      (cartierResidue_cast l (n + 1)) (diagonalSurface_power_unit l Y hY n)
    simpa only [δ, reduced_eq_canonical l (n + 1) (Nat.succ_pos n)] using hδ
  exact hf.symm.trans ((congrArg U.map hfk).trans hk)

end AlgebraicGeometry.ProEtale.DiagonalTrace
