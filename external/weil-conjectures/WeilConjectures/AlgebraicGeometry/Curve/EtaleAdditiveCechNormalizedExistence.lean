/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAugmentationHomology
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechResolutionTransfer
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalData

/-! # Existence of normalized additive étale Čech edges
Source: Stacks Project, Tags 03P2, 01EQ and 01FD. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The additive étale Čech edge equivalence has its augmentation normalization.
This concerns one scheme, with no endomorphism or inverse-image assertion.

Source: Stacks Project, Tag 03P2, separated-case affine-cover proof; Tag 01EQ,
construction of the two augmentations; Tag 01FD, augmented double-complex diagram.
(blueprint: lem-pbc-etale-additive-cech-normalized-existence)

Proof: Use additiveCechOpenInclusion as the Zariski-to-étale functor; forgetting it
is X.restrictFunctor, so it preserves covers and finite intersections. On every
intersection the unit tensor section coordinates identify the additive sheaf
with lifted ordinary structural functions. Affine étale quasi-coherent
acyclicity makes the coefficient augmentation beta a quasi-isomorphism. The
restriction augmentation alpha is a quasi-isomorphism by injective Čech
acyclicity, applied to each resolution term and the finite total diagonals.
Lower the finite products in the coefficient complex and use the identity
scalar restriction for X.toSpecGamma. Hence its homology is the ordinary
cechOver homology. Identify global resolution homology with Sheaf.H through
exists_resolutionSection_canonical_comparison. Define a as the coefficient
augmentation homology inverse after the global augmentation and this normalized
global identification inverse. This is an additive equivalence. For another
resolution, an augmentation-preserving lift of the identity commutes with both
augmentations and with the extMk identification. Cancel its invertible total
homology map. This proves the displayed normalization on every resolution and
every supplied canonical comparison. In degree zero both augmentations restrict
a glued section to the same tuple sections. Empty intersections have zero
sections; an empty covering forces X empty and the two complexes are zero. -/
theorem exists_etaleAdditiveCech_normalized
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (n : ℕ) :
    ∃ a : Sheaf.H X.etaleAdditiveSheaf n ≃+
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n,
      IsEtaleAdditiveCechNormalized U n a := by
  classical
  let J := injectiveResolution X.etaleAdditiveSheaf
  obtain ⟨cJ⟩ := Etale.exists_resolutionSection_canonical_comparison X.etaleAdditiveSheaf J
  obtain ⟨p, q, _, _, hp, hq⟩ :=
    exists_additiveCech_augmentation_homology X U hU hcover J n
  let a := ((cJ.globalEquiv n).symm.trans p).trans q.symm
  refine ⟨a, ?_⟩
  intro I cI s z tα tβ hα hβ ht
  obtain ⟨f, t, hf, htβ, hc⟩ := exists_additiveCech_resolution_transfer U I J cI cJ n
  let s' := HomologicalComplex.cyclesMap f n s
  let tα' := HomologicalComplex.cyclesMap t n tα
  let tβ' := HomologicalComplex.cyclesMap t n tβ
  have hiα : (additiveCechTotal U J).iCycles n tα' =
      additiveCechAlpha U J n ((additiveCechGlobal J).iCycles n s') := by
    change ((HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal U J).iCycles n) tα) = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, hα]
    rw [← ConcreteCategory.comp_apply, hf, ConcreteCategory.comp_apply]
    congr 1
    change _ = (HomologicalComplex.cyclesMap f n ≫ (additiveCechGlobal J).iCycles n) s
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  have hiβ : (additiveCechTotal U J).iCycles n tβ' = additiveCechBeta U J n
      ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) := by
    change ((HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal U J).iCycles n) tβ) = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, hβ, htβ]
  have ht' : (additiveCechTotal U J).homologyπ n tα' =
      (additiveCechTotal U J).homologyπ n tβ' := by
    change (HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal U J).homologyπ n) tα =
      (HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal U J).homologyπ n) tβ
    rw [← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ht]
  have hs' : (additiveCechGlobal J).homologyπ n s' =
      HomologicalComplex.homologyMap f n ((additiveCechGlobal I).homologyπ n s) := by
    change (HomologicalComplex.cyclesMap f n ≫ (additiveCechGlobal J).homologyπ n) s = _
    rw [← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  have he : cJ.globalEquiv n ((additiveCechGlobal J).homologyπ n s') =
      cI.globalEquiv n ((additiveCechGlobal I).homologyπ n s) := by
    rw [hs', hc]
  change q.symm (p ((cJ.globalEquiv n).symm
    (cI.globalEquiv n ((additiveCechGlobal I).homologyπ n s)))) = _
  rw [← he, AddEquiv.symm_apply_apply, hp s' tα' hiα, ht', ← hq z tβ' hiβ,
    AddEquiv.symm_apply_apply]

end AlgebraicGeometry.Scheme.Modules
