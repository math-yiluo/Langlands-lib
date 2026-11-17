import Langlands.GroupScheme.Reductive.GlobalPinningIsomorphism
import Langlands.GroupScheme.Reductive.GlobalBasedRootDatumComparison
import Langlands.LinearAlgebra.RootDatumBaseExists

/-! # Torus and Borel isomorphisms from coherent actual root frames -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

section Groups

variable {S : Scheme.{u}} [Nonempty S]
    {I J I' J' : Type u} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {G H : GroupScheme S} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)
    (hH : IsReductive H) (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (hQ : IsGlobalCoordinateRootDatumOf I' H t' Q)
    (F : AffineRootFrames t P) (hF : AffineRootFrames.IsCoherent t P F)
    (F' : AffineRootFrames t' Q) (hF' : AffineRootFrames.IsCoherent t' Q F')
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hloc : ∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒱.I₀, Nonempty ((baseChange (𝒱.f a)).obj G ≅
        (baseChange (𝒱.f a)).obj H))

/-- Étale-local group isomorphism fixes the missing full based-datum
identification before applying global pinned descent. -/
def basedIsoOfEtaleLocalIsoOfCoherentFrames (b : P.Base) (c : Q.Base) :
    BasedCoordinateIso t t' P Q b c := by
  let := hP.2.1
  let := hQ.2.1
  let e := basedGlobalCoordinateRootDatumEquivOfEtaleLocalIso
    hG hH ht' hmax hmax' hP hQ b c hloc
  let θ := e.val.symm
  have hθ : ∀ a : J', a ∈ c.support ↔ θ.indexEquiv a ∈ b.support := by
    intro a
    change a ∈ c.support ↔ e.val.indexEquiv.symm a ∈ b.support
    simpa only [Equiv.apply_symm_apply] using (e.property (e.val.indexEquiv.symm a)).symm
  exact basedIsoOfCoherentFrames t t' P Q hG ht hmax hP hH ht' hmax' hQ
    F hF F' hF' b c θ hθ hAffine

/-- An actual torus-preserving global isomorphism from coherent root
frames and étale-local group isomorphism. No Borel is supplied. -/
def torusIsoOfEtaleLocalIsoOfCoherentFrames :
    {e : G ≅ H // SubgroupFunctor.range (t ≫ e.hom) = SubgroupFunctor.range t'} := by
  let := hP.2.1
  let := hQ.2.1
  let b := Langlands.LinearAlgebra.RootDatumBase.base P
  let c := Langlands.LinearAlgebra.RootDatumBase.base Q
  let d := basedIsoOfEtaleLocalIsoOfCoherentFrames t t' P Q hG ht hmax hP
    hH ht' hmax' hQ F hF F' hF' hAffine hloc b c
  exact ⟨d.groupIso, d.range_torus_comp⟩

end Groups

/-- One actual global isomorphism preserving the original torus and
Borel subgroup functors simultaneously. -/
structure TorusBorelIsoData
    {S : Scheme.{u}} {I I' : Type u} [Fintype I] [Fintype I']
    {G H B B' : GroupScheme S}
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ H)
    (i : B ⟶ G) (i' : B' ⟶ H) where
  iso : G ≅ H
  torus_range : SubgroupFunctor.range (t ≫ iso.hom) = SubgroupFunctor.range t'
  borel_range : SubgroupFunctor.range (i ≫ iso.hom) = SubgroupFunctor.range i'

section Borels

variable {S : Scheme.{u}} [ConnectedSpace S]
    {I J I' J' : Type u} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {G H : GroupScheme S} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)
    (hH : IsReductive H) (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (hQ : IsGlobalCoordinateRootDatumOf I' H t' Q)
    (F : AffineRootFrames t P) (hF : AffineRootFrames.IsCoherent t P F)
    (F' : AffineRootFrames t' Q) (hF' : AffineRootFrames.IsCoherent t' Q F')
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hloc : ∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒱.I₀, Nonempty ((baseChange (𝒱.f a)).obj G ≅
        (baseChange (𝒱.f a)).obj H))
    {B B' : GroupScheme S} (i : B ⟶ G) (i' : B' ⟶ H)
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hti' : SubgroupFunctor.range t' ≤ SubgroupFunctor.range i')

/-- Choose one global isomorphism preserving supplied split maximal tori
and containing Borels, from coherent root frames and the affine theorem. -/
def torusBorelIsoOfEtaleLocalIsoOfCoherentFrames : TorusBorelIsoData t t' i i' := by
  let := hP.2.1
  let := hQ.2.1
  let db := basedBorelOfConnected P hG t hmax hP i hi hti
  let dc := basedBorelOfConnected Q hH t' hmax' hQ i' hi' hti'
  let d := basedIsoOfEtaleLocalIsoOfCoherentFrames t t' P Q hG ht hmax hP
    hH ht' hmax' hQ F hF F' hF' hAffine hloc db.val dc.val
  have hb : (Dynamic.parabolic (BasedBorelTransport.cocharacter t P db.val)).IsRepresentedBy i :=
    ⟨hi.isRelativeParabolicSubgroup.mono, db.property⟩
  have hc : (Dynamic.parabolic (BasedBorelTransport.cocharacter t' Q dc.val)).IsRepresentedBy i' :=
    ⟨hi'.isRelativeParabolicSubgroup.mono, dc.property⟩
  exact ⟨d.groupIso, d.range_torus_comp, d.range_parabolic_comp hb hc⟩

end Borels

end CoordinateRootDatum

end Langlands.GroupScheme
