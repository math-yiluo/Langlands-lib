import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # A normal subgroup's maximal torus inside a chosen ambient maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual compatible inclusions of a maximal torus of `H` into both `H`
and the specified ambient torus. -/
structure CompatibleNormalMaximalTorus (h : H ⟶ G) (t : T.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  subgroupHom : torus.toGrp ⟶ H
  torusHom : torus ⟶ T
  isMaximalTorus : IsMaximalTorus subgroupHom
  isClosedSubgroup : IsClosedSubgroup (CommGroupScheme.groupHom torusHom)
  comp_eq : CommGroupScheme.groupHom torusHom ≫ t = subgroupHom ≫ h

section Construction

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hconj : MaximalToriAreConjugate G)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)

include hconj hh hn ht

/-- Extend a maximal torus of the normal subgroup, conjugate the extension
onto `t`, and restrict conjugation to the original normal subgroup. -/
theorem exists_compatibleNormalMaximalTorus_of_conjugacy :
    Nonempty (CompatibleNormalMaximalTorus h t) := by
  let : IsAffineHom H.X.hom := hh.isAffineHom
  let : LocallyOfFiniteType H.X.hom := hh.locallyOfFiniteType
  obtain ⟨S, s, hs⟩ := exists_isMaximalTorus H
  obtain ⟨M, m, hm, a, ha⟩ :=
    exists_maximalTorus_extension_of_finiteType G (s ≫ h) hs.1 (hs.2.1.comp hh)
  obtain ⟨g, e, he⟩ := hconj M T m t hm ht
  let c := hh.isRepresentedBy_range.conjugateIso hn g
  let sH : S.toGrp ⟶ H := s ≫ c.hom
  let sT : S.toGrp ⟶ T.toGrp := a ≫ e.hom
  have hsH : IsMaximalTorus sH := hs.comp_iso c
  have hsq : sT ≫ t = sH ≫ h := by
    simp only [sT, sH, c, Category.assoc,
      SubgroupFunctor.IsRepresentedBy.conjugateIso_hom_comp]
    rw [← he, ← Category.assoc a m, ha, Category.assoc]
  have hsT : IsClosedSubgroup sT :=
    IsClosedSubgroup.of_comp ht.2.1 (hsq ▸ hsH.2.1.comp hh)
  exact ⟨⟨S, sH, Additive.ofMul sT, hsH, hsT, hsq⟩⟩

/-- A chosen compatible maximal torus, with the original subgroup inclusion
and chosen ambient torus retained in its exact commuting square. -/
def compatibleNormalMaximalTorusOfConjugacy :
    CompatibleNormalMaximalTorus h t :=
  Classical.choice
    (exists_compatibleNormalMaximalTorus_of_conjugacy hconj h hh hn t ht)

end Construction

/-- Over an algebraically closed field, the compatible maximal torus of the
normal subgroup is split. No conjugacy premise is needed for this consequence
of an already supplied compatible torus. -/
theorem CompatibleNormalMaximalTorus.isSplitSubtorus [IsAlgClosed k]
    {h : H ⟶ G} {t : T.toGrp ⟶ G} (d : CompatibleNormalMaximalTorus h t) :
    IsSplitSubtorus d.subgroupHom :=
  ⟨d.isMaximalTorus.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting,
    d.isMaximalTorus.2.1⟩

end Langlands.GroupScheme
