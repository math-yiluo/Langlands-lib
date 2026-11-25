/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AffineSpectrumStalkCondition
import WeilConjectures.AlgebraicGeometry.AffineSpectrumBaseChangeComparison
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Spectrum coordinates for a single-complex affine square

Source: Stacks Project, Tags 0DJ8 and 0DJ9, affine coordinate reduction.
(blueprint: lem-pc-single-complex-affine-spectrum-coordinates).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transport an affine square to the spectra of its global section rings.
This statement concerns coordinate transport, not invertibility of the comparison.
The two displayed isomorphisms identify its endpoints and the final equation
identifies the actual morphism, including its given coefficient map.
Source: Stacks Project, Tag 0DJ8, affine reduction in the proof; Tag 0DJ9,
affine-open paragraph. Canonical transport details expanded by C1.
(blueprint: lem-pc-single-complex-affine-spectrum-coordinates).

Proof: For each of the four affine schemes use its canonical isomorphism to the
spectrum of its global section ring. Naturality of toSpecGamma identifies each
arrow with Spec.map of its map on global sections. Transport the pullback cone
along these four isomorphisms, identifying the supplied sq0. Take K0 and K0'
to be pullbacks of K
and K' along the inverse canonical isomorphisms. Derived pullback composition
and the identity comparison give the coefficient map phi0 and identify both
coefficient objects with the originals. Pullback preserves quasi-coherent
cohomology. The induced isomorphisms on local rings commute with the four stalk
maps and with tensor pullback; exact stalks commute with cohomology. Thus the
localized tensor comparisons for phi and phi0 are conjugate. Every K-flat
coordinate presentation represents that same canonical comparison, so this gives
both directions of the displayed stalk-condition equivalence. The equivalence
of derived categories along S'.toSpecGamma and the pullback/direct-image
composition comparisons give eL and eR. The counit definition of base change,
naturality of the adjunction counits, and coherence of pullback composition give
the displayed equality. These are equivalences and identities even for the zero
ring/empty scheme and unbounded objects; no flatness or boundedness is used. -/
theorem exists_singleComplexAffineSpectrumCoordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K') :
    let f0 := Spec.map f.appTop
    let f0' := Spec.map f'.appTop
    let g0 := Spec.map g.appTop
    let g0' := Spec.map g'.appTop
    ∃ (K0 : schemeDerivedCategory (Spec Γ(X, ⊤)))
      (K0' : schemeDerivedCategory (Spec Γ(X', ⊤)))
      (φ0 : (derivedPullback g0').obj K0 ⟶ K0'),
      schemeDerivedQCohProperty (Spec Γ(X, ⊤)) K0 ∧
      schemeDerivedQCohProperty (Spec Γ(X', ⊤)) K0' ∧
      (SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ ↔
        SingleComplexBaseChange.StalkCondition f0 f0' g0 g0' sq0 K0 K0' φ0) ∧
      ∃ (eL : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj K) ≅
          (derivedPullback S'.toSpecΓ).obj
            ((derivedPullback g0).obj ((schemeDerivedDirectImage f0).obj K0)))
        (eR : (schemeDerivedDirectImage f').obj K' ≅
          (derivedPullback S'.toSpecΓ).obj ((schemeDerivedDirectImage f0').obj K0')),
        schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
            (schemeDerivedDirectImage f').map φ =
          eL.hom ≫ (derivedPullback S'.toSpecΓ).map
            (schemeDerivedBaseChangeMap f0 f0' g0 g0' sq0.w K0 ≫
              (schemeDerivedDirectImage f0').map φ0) ≫ eR.inv := by
  dsimp
  let K0 := affineSpectrumDerivedObject X K
  let K0' := affineSpectrumDerivedObject X' K'
  let φ0 := affineSpectrumDerivedMorphism g' K K' φ
  have hK0 : schemeDerivedQCohProperty (Spec Γ(X, ⊤)) K0 :=
    (derivedPullback_tensor_preserve_QCoh X.isoSpec.inv).1 K hK
  have hK0' : schemeDerivedQCohProperty (Spec Γ(X', ⊤)) K0' :=
    (derivedPullback_tensor_preserve_QCoh X'.isoSpec.inv).1 K' hK'
  have hst := affineSpectrumCoordinates_stalkCondition f f' g g' sq sq0 K K' φ
  obtain ⟨eL, eR, heq⟩ :=
    affineSpectrumCoordinates_comparison f f' g g' sq sq0 K K' φ
  exact ⟨K0, K0', φ0, hK0, hK0', hst, eL, eR, heq⟩

end AlgebraicGeometry
