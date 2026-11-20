import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesInjectivity
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction

/-! # Real-place injectivity from the simply connected arithmetic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Injectivity at the real places follows from the finite-Galois arithmetic
kernel for simply connected groups. -/
def SimplyConnectedRealPlacesKernelReductionStatement : Prop :=
  NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u} →
    SimplyConnectedRealPlacesInjectivityStatement.{u}

theorem simplyConnectedRealPlacesInjectivity_of_galoisHasseKernel :
    SimplyConnectedRealPlacesKernelReductionStatement.{u} := by
  intro hsc F _ _ G hG L _ _ _ _ ξ ζ hreal
  have hlocal := simplyConnectedRealToAllPlacesComparison F G hG L ξ ζ hreal
  obtain ⟨E, hfin, hgal, ⟨φ⟩⟩ := exists_finite_galois_algHom F L
  let : Algebra L E := φ.toRingHom.toAlgebra
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc L E
  let s := ringTestMap F φ
  let : Surjective s.left := hs
  let : Flat s.left := hf
  let : QuasiCompact s.left := hq
  apply (ξ.cohomologous_refine_iff ζ s).mp
  let ξ' := ξ.refine s
  let ζ' := ζ.refine s
  have hlocal' : ξ'.LocallyCohomologous ζ' := hlocal.refine s
  let p := algebraBaseMap F E
  obtain ⟨hs', hf', _⟩ := fieldExtension_fpqc F E
  have hGE := isSimplyConnectedFieldExtension F E G hG
  let : IsAffineHom ((baseChange p).obj G).X.hom :=
    hGE.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine (ringTest F E).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of E)))
  have hA : IsAffine ((baseChange p).obj G).X.left :=
    isAffine_of_isAffineHom ((baseChange p).obj G).X.hom
  let D := ξ'.innerTwist hA hf' hs'
  let e := ξ'.innerTwistIso hA hf' hs'
  have hD : IsSimplyConnected D.obj :=
    (isSimplyConnected_fieldExtension_iff (K := E) D.obj).mp
      ((isSimplyConnected_iff_of_iso e).mpr hGE)
  exact (D.cohomologous_iff_difference_isTrivial ζ').mpr
    (hsc F D.obj hD E (D.difference ζ') (D.difference_locallyTrivial hlocal'))

end Langlands.GroupScheme
