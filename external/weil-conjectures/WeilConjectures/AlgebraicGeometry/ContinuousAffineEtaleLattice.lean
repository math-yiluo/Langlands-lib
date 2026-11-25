/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices

/-! # An integral lattice near a point of a continuous local system

Source: Bhatt--Scholze, Proposition 6.8.4(6).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
private lemma etale_cover_point (X : Scheme.{u}) {I : Type (u + 1)}
    (Y : I → X.Etale) (hY : X.smallEtaleTopology.CoversTop Y) (x : X) :
    ∃ i, x ∈ Set.range (Y i).hom := by
  let T : X.Etale := .mk (𝟙 X)
  obtain ⟨U, hOver, hEtale, hU⟩ := (Scheme.mem_smallGrothendieckTopology _ _).mp (hY T)
  let := hOver
  obtain ⟨i, y, hy⟩ := U.exists_eq x
  obtain ⟨j, ⟨b⟩⟩ := hU _ _ ⟨i⟩
  refine ⟨j, b.left y, ?_⟩
  have hb : b.left ≫ (Y j).hom = U.f i ≫ T.hom := by
    exact b.w.trans (CategoryTheory.comp_over (U.f i) X).symm
  exact (Scheme.Hom.comp_apply b.left (Y j).hom y).symm.trans
    ((congrArg (fun f : U.X i ⟶ X ↦ f y) hb).trans hy)

/-- An integral lattice exists on some affine etale neighbourhood of each point.

Source: Bhatt--Scholze, Proposition 6.8.4(6).
(auxiliary; not a blueprint node)

Proof in words. Apply the explicit continuous field module equivalence to P.
The lattice-compatibility theorem supplies finite local freeness of its image.
Apply exists_lisse_lattice_etale_local to obtain an etale covering with specified
integral lattices and rationalization isomorphisms. A covering sieve at the
terminal object contains an etale scheme cover, so some member contains x in its
image. Apply the compatibility theorem to that member and its supplied lattice;
the inverse integral equivalence is an explicit construction of the internal
lattice. Choose an affine open of this member containing a point above x, and
pull back this lattice to the affine open. Pullback preserves finite free
modules; pull back the free cover and bind its composite to obtain the required
raw pro-etale trivialization. The coefficient pullback comparison and composition
isomorphism identify the rationalization with the composite pullback of P.
No simultaneous finite selection or disjoint-union assembly is asserted. -/
theorem continuousLisse_affine_etale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) (x : X) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X), IsAffine U ∧ Etale p ∧ x ∈ Set.range p ∧
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) U),
      (IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) M) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) := by
  classical
  have hlocal : ∃ (Y : Scheme.{u}) (q : Y ⟶ X), Etale q ∧ x ∈ Set.range q ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) Y),
        IsLocallyFree (condensedRingObj (integralCoeff ℓ E) Y) M ∧
        Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y)).obj M ≅
          (upperStar (Profinite.continuousMapRingObj E) q).obj P) := by
    let L := (continuousFieldModuleEquivalence ℓ E X).functor.obj P
    obtain ⟨hL, htransport⟩ := continuousModuleEncoding_lattice_compatibility ℓ E X P hP
    obtain ⟨I, Y, hY, hM⟩ := exists_lisse_lattice_etale_local ℓ E X L hL
    obtain ⟨i, hi⟩ := etale_cover_point X Y hY x
    obtain ⟨M, hM, e⟩ := hM i
    obtain ⟨hf, he⟩ := htransport (Y i).left (Y i).hom M hM e
    exact ⟨(Y i).left, (Y i).hom, inferInstance, hi,
      (continuousIntegerModuleEquivalence ℓ E (Y i).left).inverse.obj M, hf, he⟩
  obtain ⟨Y, q, hq, ⟨y, hy⟩, M, hM, ⟨e⟩⟩ := hlocal
  let : Etale q := hq
  let A := Y.affineCover
  let i := A.idx y
  obtain ⟨z, hz⟩ := A.covers y
  let f := A.f i
  let N := (upperStar (integralCoeff ℓ E) f).obj M
  refine ⟨A.X i, f ≫ q, inferInstance, inferInstance, ⟨z, ?_⟩, N,
    IsLocallyFree.upperStar _ f hM, ⟨?_⟩⟩
  · rw [Scheme.Hom.comp_apply, hz, hy]
  · exact (pullIso (integralScalarMap ℓ E) f).app M ≪≫
      (upperStar (Profinite.continuousMapRingObj E) f).mapIso e ≪≫
      ((upperStarComp (Profinite.continuousMapRingObj E) f q).app P).symm

end AlgebraicGeometry.ProEtale.CondensedRing
