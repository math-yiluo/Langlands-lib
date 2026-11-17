import Langlands.GroupScheme.RelativeLevi.SplitFaceBaseComparison
import Langlands.GroupScheme.RelativeLevi.SplitRootSignDetection
import Langlands.GroupScheme.RelativeLevi.DynamicRadicalIdentification
import Langlands.GroupScheme.RelativeLevi.DynamicProof

/-! # Canonical face terms for different dynamic presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam fam' : J → (Ga R ⟶ G)} {wt wt' : I → ℤ}
  (C : SplitParabolicFaceChart t P fam wt)
  (C' : SplitParabolicFaceChart t P fam' wt')
  (hU : Dynamic.unipotent (AffineRegularBorel.cocharacter t wt) =
    Dynamic.unipotent (AffineRegularBorel.cocharacter t wt'))
  (hfam : ∀ a, IsRootParametrization t (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization t (P.root a) (fam' a))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

include hU hfam in
/-- Equality of actual contracting functors fixes every root's positive sign. -/
theorem coPairing_pos_iff_of_sameContracting (a : J) :
    0 < coPairing (P.root a) wt ↔ 0 < coPairing (P.root a) wt' :=
  coPairing_pos_iff_of_unipotent_eq (fun a Z x c => (hfam a).equivariant Z x c)
    wt wt' hU a (hfam a)

include hU hfam in
/-- Opposite root labels turn equality of positive root signs into equality
of their exact zero-root faces. -/
theorem coPairing_zero_iff_of_sameContracting [P.IsReduced] (a : J) :
    coPairing (P.root a) wt = 0 ↔ coPairing (P.root a) wt' = 0 := by
  let := P.indexNeg
  have hp := coPairing_pos_iff_of_sameContracting hU hfam a
  have hn := coPairing_pos_iff_of_sameContracting hU hfam (-a)
  have hr : P.root (-a) = - P.root a := by
    change P.root (P.reflectionPerm a a) = _
    simp
  have he (v : I → ℤ) : coPairing (P.root (-a)) v = -coPairing (P.root a) v := by
    change coPairingLinear v (P.root (-a)) = _
    rw [hr, map_neg]
    rfl
  rw [he wt, he wt'] at hn
  omega

/-- Reinterpret the same actual chart and UNSCALED weight data for another
cocharacter with the same actual contracting functor. -/
def reparameterize [P.IsReduced] : SplitParabolicFaceChart t P fam wt' := by
  classical
  let cv := P.flip.toPerfPair.symm (coPairingLinear wt')
  have hcv (a : J) : P.root' a cv = coPairing (P.root a) wt' := by
    change (P.flip.toPerfPair cv) (P.root a) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hface : faceHeight C.base C.faceCoweight = faceHeight C.base cv := by
    apply faceHeight_eq_of_simple_zero_iff
    intro a _
    rw [C.coweight_eq, hcv]
    exact coPairing_zero_iff_of_sameContracting hU hfam a
  have hdom : ∀ a ∈ C.base.support, 0 ≤ P.root' a cv := by
    intro a ha
    have hn := C.dominant a ha
    rw [C.coweight_eq] at hn
    rw [hcv]
    have hp := coPairing_pos_iff_of_sameContracting hU hfam a
    have hz := coPairing_zero_iff_of_sameContracting hU hfam a
    omega
  exact {
    cocharacter := C.cocharacter
    regular := C.regular
    base := C.base
    faceCoweight := cv
    coweight_eq := hcv
    dominant := hdom
    chart := C.chart
    index := C.index
    root_comp := C.root_comp
    weights := C.weights
    weight_eq := fun k => (C.weight_eq k).trans (LinearMap.congr_fun hface _)
    represented := by rw [← hU]; exact C.represented
  }

variable (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) t)
  (hP : IsFibrewiseRootDatumOf I G t P)

include hG hmax hP hU hfam hfam' in
/-- For one actual torus, equal contracting functors make every canonical
face-filtration ambient range independent of the original cocharacter. -/
theorem range_inclusion_comp_sameContracting (d : ℕ) :
    SubgroupFunctor.range (C.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t C.cocharacter)) =
    SubgroupFunctor.range (C'.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t C'.cocharacter)) := by
  let : P.IsReduced := hP.isReduced
  exact (C.reparameterize hU hfam).range_inclusion_comp_sameTorus C' hG hmax hP hfam hfam' d

/-- Every actual canonical face term is ambient-compatibly isomorphic for
two cocharacters with the same contracting functor in the fixed torus. -/
def sameContractingTermIso (d : ℕ) :
    C.weights.groupScheme d ≅ C'.weights.groupScheme d := by
  let : P.IsReduced := hP.isReduced
  exact (C.reparameterize hU hfam).sameTorusTermIso C' hG hmax hP hfam hfam' d

/-- Reparameterization does not alter any of the original ambient term maps. -/
theorem sameContractingTermIso_hom_comp (d : ℕ) :
    (C.sameContractingTermIso C' hU hfam hfam' hG hmax hP d).hom ≫
      (C'.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t C'.cocharacter)) =
      C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t C.cocharacter) := by
  let : P.IsReduced := hP.isReduced
  exact (C.reparameterize hU hfam).sameTorusTermIso_hom_comp C' hG hmax hP hfam hfam' d

end Langlands.GroupScheme.SplitParabolicFaceChart

namespace Langlands.GroupScheme.RelativeLevi

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I]
  {G Pgrp U : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {wt wt' : I → ℤ} {iP : Pgrp ⟶ G} (r : U ⟶ Pgrp)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Two dynamic presentations of the same supplied parabolic and radical
have exactly the same contracting functor on all scheme tests. -/
theorem unipotent_eq_of_same_relativeRadical (hG : IsReductive G)
    (hPar : (Dynamic.parabolic (AffineRegularBorel.cocharacter t wt)).IsRepresentedBy iP)
    (hPar' : (Dynamic.parabolic (AffineRegularBorel.cocharacter t wt')).IsRepresentedBy iP)
    (hr : IsRelativeUnipotentRadical r) :
    Dynamic.unipotent (AffineRegularBorel.cocharacter t wt) =
      Dynamic.unipotent (AffineRegularBorel.cocharacter t wt') :=
  (isRepresentedBy_unipotent_of_relativeRadical dynamicRelativeLevi hG
    (AffineRegularBorel.cocharacter t wt) hPar r hr).2.symm.trans
      (isRepresentedBy_unipotent_of_relativeRadical dynamicRelativeLevi hG
        (AffineRegularBorel.cocharacter t wt') hPar' r hr).2

variable [Nontrivial R] [Fintype J]
  {D : RootDatum J (I → ℤ) (I → ℤ)}
  {fam fam' : J → (Ga R ⟶ G)}
  (C : SplitParabolicFaceChart t D fam wt)
  (C' : SplitParabolicFaceChart t D fam' wt')
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) t)
  (hD : IsFibrewiseRootDatumOf I G t D)
  (hfam : ∀ a, IsRootParametrization t (D.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization t (D.root a) (fam' a))
  (hPar : (Dynamic.parabolic (AffineRegularBorel.cocharacter t wt)).IsRepresentedBy iP)
  (hPar' : (Dynamic.parabolic (AffineRegularBorel.cocharacter t wt')).IsRepresentedBy iP)
  (hr : IsRelativeUnipotentRadical r)

/-- All canonical local terms for two dynamic presentations of one supplied
parabolic and radical, in the fixed torus, are ambient-compatibly isomorphic. -/
def sameRelativeRadicalTermIso (d : ℕ) :
    C.weights.groupScheme d ≅ C'.weights.groupScheme d :=
  C.sameContractingTermIso C'
    (unipotent_eq_of_same_relativeRadical r hG hPar hPar' hr)
    hfam hfam' hG hmax hD d

/-- The actual same-radical term comparison preserves its ambient maps. -/
theorem sameRelativeRadicalTermIso_hom_comp (d : ℕ) :
    (sameRelativeRadicalTermIso r C C' hG hmax hD hfam hfam' hPar hPar' hr d).hom ≫
      (C'.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t C'.cocharacter)) =
      C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t C.cocharacter) :=
  C.sameContractingTermIso_hom_comp C'
    (unipotent_eq_of_same_relativeRadical r hG hPar hPar' hr)
    hfam hfam' hG hmax hD d

end Langlands.GroupScheme.RelativeLevi
