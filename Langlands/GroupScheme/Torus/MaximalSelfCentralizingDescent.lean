import Langlands.GroupScheme.Torus.RelativeMaximalSelfCentralizing
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.SubgroupFunctor.FppfLocality
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Self-centralization of relative maximal tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- A fibrewise maximal closed split torus in a reductive group is its
whole centralizer over an arbitrary base. -/
theorem splitTorusCentralizer_eq_range_of_fibrewiseMaximal
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) :
    torusCentralizer (T := T) t = SubgroupFunctor.range t := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  apply le_antisymm ?_ (range_le_torusCentralizer (T := T) t)
  apply (SubgroupFunctor.le_range_iff_baseChange_openCover S.affineOpenCover.openCover t).mpr
  intro k
  let b := S.affineOpenCover.f k
  have hk := splitTorusCentralizer_eq_range_of_fibrewiseMaximal_overRing
    (R := S.affineOpenCover.X k)
    (T := (CommGroupScheme.baseChange b).obj T)
    (hG.baseChange (S.affineOpenCover.f k))
    (hT.baseChange (S.affineOpenCover.f k))
    ((baseChange (S.affineOpenCover.f k)).map t)
    (ht.baseChange (S.affineOpenCover.f k))
    (hmax.baseChange (T := T) b)
  exact ((torusCentralizer_baseChange b (T := T) t).symm.trans
    (hk.trans (SubgroupFunctor.range_baseChangeHom b t))).le

/-- Every relative maximal torus of a reductive group scheme equals its
all-test-scheme centralizer. -/
theorem relativeTorusCentralizer_eq_range_of_fibrewiseMaximal
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) :
    torusCentralizer (T := T) t = SubgroupFunctor.range t := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  obtain ⟨𝒰, h𝒰⟩ := hT
  have (k : 𝒰.I₀) : Etale (𝒰.f k) := 𝒰.map_prop k
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply le_antisymm ?_ (range_le_torusCentralizer (T := T) t)
  apply (SubgroupFunctor.le_range_iff_baseChange_fppfCover 𝒱 t).mpr
  intro k
  let b := 𝒰.f k
  have hk := splitTorusCentralizer_eq_range_of_fibrewiseMaximal
    (T := (CommGroupScheme.baseChange b).obj T)
    (hG.baseChange (𝒰.f k)) (h𝒰 k) ((baseChange (𝒰.f k)).map t)
    (ht.baseChange b) (hmax.baseChange (T := T) b)
  exact ((torusCentralizer_baseChange b (T := T) t).symm.trans
    (hk.trans (SubgroupFunctor.range_baseChangeHom b t))).le

/-- The centre is contained in each relative maximal torus of a reductive
 group scheme, as a subgroup functor on all test schemes. -/
theorem center_le_range_relativeMaximalTorus
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) :
    center G ≤ SubgroupFunctor.range t := by
  rw [← relativeTorusCentralizer_eq_range_of_fibrewiseMaximal hG hT t ht hmax]
  exact center_le_torusCentralizer (T := T) t

/-- A central homomorphism factors canonically through any relative maximal
 torus of a reductive group scheme. -/
def relativeMaximalTorusCentralFactor
    {S : Scheme.{u}} {G Z : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (z : Z ⟶ G) (hz : IsCentral z) :
    Z ⟶ T.toGrp := by
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  exact (show (SubgroupFunctor.range t).IsRepresentedBy t from
    ⟨inferInstance, rfl⟩).factorHom z
    (((isCentral_iff_range_le_center z).mp hz).trans
      (center_le_range_relativeMaximalTorus hG hT t ht hmax))

@[reassoc (attr := simp)]
theorem relativeMaximalTorusCentralFactor_comp
    {S : Scheme.{u}} {G Z : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (z : Z ⟶ G) (hz : IsCentral z) :
    relativeMaximalTorusCentralFactor hG hT t ht hmax z hz ≫ t = z := by
  unfold relativeMaximalTorusCentralFactor
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

end Langlands.GroupScheme
