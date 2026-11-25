/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData

/-! # The restriction transpose of the geometric scalar mate -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The geometric scalar mate is conjugate to exact restriction/direct image.
Source: Stacks 07A4, 0G7E and 0D6J; Zheng, Lemma 5.16.
(blueprint: lem-pur-scalar-mate-restriction-transpose).
Proof: take the inverse scalar-adjunction mate of the exact
restriction/pullback square. Its representative is the reverse ordinary scalar
pullback comparison: apply the scalar-unit equations to cochain complexes and
the exact geometric factorization. Flat K-flat representatives and localization
identify its inverse with scalarPullbackIso. The iterated-mate identity then
identifies the scalar transpose of scalarMate with the conjugate of the inverse
restriction/pullback comparison. The opposite iterated mate is
scalarRestrictionDirectImageMap, by its defining geometric mate equation.
Conjugation of an isomorphism preserves inverses, giving the two equations.
The resulting delta is unique because its inverse is prescribed. The argument
works for every ring map, including identity maps and the zero ring. -/
theorem scalarMate_restrictionTranspose
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (g : V ⟶ W) :
    ∃ δ : Sheaf.derivedRestrictScalars V.smallEtaleTopology φ ⋙
        (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor ≅
      (lowerStar (ModuleCat.{u + 1} B) g).rightDerivedFunctor ⋙
        Sheaf.derivedRestrictScalars W.smallEtaleTopology φ,
      δ.inv = scalarRestrictionDirectImageMap φ g ∧
      (mateEquiv
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
        (.mk _ _ _ _ (scalarMate φ g))) = δ.hom := by
  let a := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
  let b := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let an := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g
  let am := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g
  let δ := conjugateIsoEquiv (an.comp b) (a.comp am) (scalarPullbackIso φ g)
  have hs : ((mateEquiv a b).symm
      (.mk _ _ _ _ (scalarRestrictionPullbackIso φ g).hom)) =
      (scalarPullbackIso φ g).inv := by
    have hh := congrArg Iso.inv (scalarPullback_eq φ g)
    simpa only [ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_inv, asIso_hom,
      ProEtale.scalarPullbackReverseEtale, a, b] using hh
  refine ⟨δ, ?_, ?_⟩
  · have hh := iterated_mateEquiv_conjugateEquiv a b an am
      ((mateEquiv a b).symm (.mk _ _ _ _ (scalarRestrictionPullbackIso φ g).hom))
    rw [Equiv.apply_symm_apply] at hh
    change scalarRestrictionDirectImageMap φ g =
      conjugateEquiv (a.comp am) (an.comp b)
        (((mateEquiv a b).symm
          (.mk _ _ _ _ (scalarRestrictionPullbackIso φ g).hom))) at hh
    rw [hs] at hh
    exact hh.symm
  · exact iterated_mateEquiv_conjugateEquiv an am a b
      (.mk _ _ _ _ (scalarPullbackIso φ g).hom)

end AlgebraicGeometry.Etale
