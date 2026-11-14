import Langlands.GroupScheme.RelativeLevi.LeviCoverDescent
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalGluing

/-! # Gluing local Levi decompositions over an etale cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

/-- Matching local Levi factors and relative radicals in an affine ambient
group descend to an actual global Levi representative. -/
def leviRepresentativeEtale {S : Scheme.{u}} {P : GroupScheme S}
    [IsAffineHom P.X.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (L U : ∀ i, GroupScheme (𝒰.X i))
    (l : ∀ i, L i ⟶ (baseChange (𝒰.f i)).obj P)
    (r : ∀ i, U i ⟶ (baseChange (𝒰.f i)).obj P)
    (hl : ∀ i, IsClosedSubgroup (l i))
    (hSmooth : ∀ i, Smooth (L i).X.hom)
    (hr : ∀ i, IsRelativeUnipotentRadical (r i))
    (hMul : ∀ i, IsIso (subgroupMultiplication (l i) (r i)))
    (hL : SubgroupFunctor.CoverDescent.IsMatching 𝒰
      (fun i => SubgroupFunctor.range (l i)))
    (hU : SubgroupFunctor.CoverDescent.IsMatching 𝒰
      (fun i => SubgroupFunctor.range (r i))) :
    LeviRepresentative
      (SubgroupFunctor.CoverDescent.subgroup 𝒰 (fun i => SubgroupFunctor.range (l i))) := by
  let R := radicalRepresentativeEtale 𝒰 U r hr hU
  have hrep (i : 𝒰.I₀) : (SubgroupFunctor.range (l i)).IsRepresentedBy (l i) := by
    let : IsClosedImmersion (l i).hom.hom.left := hl i
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  apply leviRepresentativeOfEtaleCover 𝒰 R.val.hom R.property
    (fun i => SubgroupFunctor.range (l i)) hL L U l r hrep hl
    (fun i => (hr i).isClosedSubgroup) hSmooth hMul
  intro i
  rw [SubgroupFunctor.range_baseChangeHom, R.val.represents.2,
    SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰 _ hU i]

end Langlands.GroupScheme.RelativeLevi
