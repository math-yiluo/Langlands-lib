import Langlands.GroupScheme.GenericSubgroupClosureFactorization
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Generic-fibre determination of a closed split-torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- A flat group maps into a closed subgroup if its fraction-field fibre does. -/
theorem range_le_of_fractionField
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A D G : GroupScheme (Spec (CommRingCat.of R))} [Flat A.X.hom]
    (a : A ⟶ G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (h : range ((GroupScheme.baseChange (Spec.algebraMap R K)).map a) ≤
      range ((GroupScheme.baseChange (Spec.algebraMap R K)).map d)) :
    range a ≤ range d := by
  let b := Spec.algebraMap R K
  let B := GroupScheme.baseChange b
  let V := (Over.map b).obj (B.obj A).X
  let p : V ⟶ A.X := GenericSubgroupClosure.genericProjection (K := K) A
  have : IsSchemeTheoreticallyDominant p.left :=
    GenericSubgroupClosure.isSchemeTheoreticallyDominant_genericProjection A
  have : IsClosedImmersion d.hom.hom.left := hd
  have hid : (B.map a).hom.hom ∈ (range (B.map a)).carrier (B.obj A).X :=
    mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨v, hv⟩ := mem_range.mp (h _ hid)
  let v' : V ⟶ D.X := baseChangePointsEquiv b D (B.obj A).X v
  have he : p ≫ a.hom.hom = v' ≫ d.hom.hom := by
    have hh := congrArg (baseChangePointsEquiv b G (B.obj A).X) hv
    rw [baseChangePointsEquiv_comp] at hh
    have hp := baseChangePointsEquiv_comp b a (B.obj A).X (𝟙 _)
    simpa only [Category.id_comp, p, GenericSubgroupClosure.genericProjection]
      using (hh.trans hp).symm
  obtain ⟨s, hs⟩ := exists_over_factor_of_schematic_precomp
    d.hom.hom p a.hom.hom v' he
  intro U x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  exact mem_range.mpr ⟨y ≫ s, by rw [Category.assoc, hs]⟩

end SubgroupFunctor

section Centralizer

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hgeneric :
      torusCentralizer (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
          ((baseChange (Spec.algebraMap R K)).map t) =
        SubgroupFunctor.range ((baseChange (Spec.algebraMap R K)).map t))

include hT ht hgeneric

/-- A generically self-centralizing closed split torus in a smooth affine group
over a domain is its whole centralizer over the original base. -/
theorem splitTorusCentralizer_eq_range_of_fractionField :
    torusCentralizer t = SubgroupFunctor.range t := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, c, _, hC, hc⟩ :=
    splitTorusCentralizer_hasSmoothClosedRepresentative_overRing t hT inferInstance
  let : Smooth C.X.hom := hC
  have hck := (hc.baseChange (Spec.algebraMap R K)).2
  rw [← torusCentralizer_baseChange, hgeneric] at hck
  have hle : SubgroupFunctor.range c ≤ SubgroupFunctor.range t :=
    SubgroupFunctor.range_le_of_fractionField K c t ht hck.le
  exact le_antisymm (hc.2.symm ▸ hle) (range_le_torusCentralizer t)

/-- The closed torus is canonically isomorphic to any representative of its
centralizer, determined by self-centralization over the fraction field. -/
def splitTorusCentralizerIsoOfFractionField
    {C : GroupScheme (Spec (CommRingCat.of R))} {c : C ⟶ G}
    (hc : (torusCentralizer t).IsRepresentedBy c) : T.toGrp ≅ C := by
  let : IsClosedImmersion t.hom.hom.left := ht
  have htRep : (torusCentralizer t).IsRepresentedBy t :=
    ⟨Over.mono_of_mono_left _,
      (splitTorusCentralizer_eq_range_of_fractionField hT t ht hgeneric).symm⟩
  exact htRep.isoOfIsRepresentedBy hc

@[reassoc (attr := simp)]
theorem splitTorusCentralizerIsoOfFractionField_hom_comp
    {C : GroupScheme (Spec (CommRingCat.of R))} {c : C ⟶ G}
    (hc : (torusCentralizer t).IsRepresentedBy c) :
    (splitTorusCentralizerIsoOfFractionField hT t ht hgeneric hc).hom ≫ c = t :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

omit hgeneric in
/-- The generic-fibre hypothesis is supplied by a maximal torus in a connected
reductive generic fibre. No connectedness of the other fibres is assumed. -/
theorem splitTorusCentralizer_eq_range_of_genericMaximal
    (hG : IsConnectedReductive ((baseChange (Spec.algebraMap R K)).obj G))
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
      ((baseChange (Spec.algebraMap R K)).map t)) :
    torusCentralizer t = SubgroupFunctor.range t := by
  apply splitTorusCentralizer_eq_range_of_fractionField (K := K) hT t ht
  exact maximalTorusCentralizer K _ hG _ _ hmax

end Centralizer

end Langlands.GroupScheme
