import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.GroupScheme.SubgroupFunctor.ClosedCoverDescent

/-! # Effective descent of Levi representatives with a supplied radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}}

/-- Compatible changes of source commute with subgroup multiplication. -/
theorem subgroupMultiplication_comp {L U L' U' P : GroupScheme S}
    (l : L ⟶ P) (r : U ⟶ P) (l' : L' ⟶ P) (r' : U' ⟶ P)
    (a : L ⟶ L') (b : U ⟶ U') (ha : a ≫ l' = l) (hb : b ≫ r' = r) :
    (a.hom.hom ⊗ₘ b.hom.hom) ≫ subgroupMultiplication l' r' =
      subgroupMultiplication l r := by
  have ha' : a.hom.hom ≫ l'.hom.hom = l.hom.hom :=
    congrArg (fun f => f.hom.hom) ha
  have hb' : b.hom.hom ≫ r'.hom.hom = r.hom.hom :=
    congrArg (fun f => f.hom.hom) hb
  simp only [subgroupMultiplication, MonObj.comp_mul, tensorHom_fst_assoc,
    tensorHom_snd_assoc, ha', hb']

/-- Actual compatible isomorphisms of two multiplication factors preserve
isomorphy of subgroup multiplication. -/
theorem subgroupMultiplication_isIso_of_iso {L U L' U' P : GroupScheme S}
    (l : L ⟶ P) (r : U ⟶ P) (l' : L' ⟶ P) (r' : U' ⟶ P)
    (a : L ≅ L') (b : U ≅ U') (ha : a.hom ≫ l' = l) (hb : b.hom ≫ r' = r)
    [IsIso (subgroupMultiplication l' r')] : IsIso (subgroupMultiplication l r) := by
  have haIso : IsIso a.hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget (Over S)).map a.hom))
  have hbIso : IsIso b.hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget (Over S)).map b.hom))
  let := haIso
  let := hbIso
  rw [← subgroupMultiplication_comp l r l' r' a.hom b.hom ha hb]
  infer_instance

/-- Two closed subgroup maps with equal all-test ranges have canonically
isomorphic source group schemes, compatibly with the inclusions. -/
def subgroupIsoOfRangeEq {L L' P : GroupScheme S} (l : L ⟶ P) (l' : L' ⟶ P)
    (hl : IsClosedSubgroup l) (hl' : IsClosedSubgroup l')
    (h : SubgroupFunctor.range l = SubgroupFunctor.range l') : L ≅ L' := by
  let : IsClosedImmersion l.hom.hom.left := hl
  let : IsClosedImmersion l'.hom.hom.left := hl'
  let : Mono l.hom.hom := Over.mono_of_mono_left l.hom.hom
  let : Mono l'.hom.hom := Over.mono_of_mono_left l'.hom.hom
  have hrep : (SubgroupFunctor.range l).IsRepresentedBy l := ⟨inferInstance, rfl⟩
  have hrep' : (SubgroupFunctor.range l).IsRepresentedBy l' := ⟨inferInstance, h.symm⟩
  exact hrep.isoOfIsRepresentedBy hrep'

@[reassoc]
theorem subgroupIsoOfRangeEq_hom_comp {L L' P : GroupScheme S}
    (l : L ⟶ P) (l' : L' ⟶ P) (hl : IsClosedSubgroup l) (hl' : IsClosedSubgroup l')
    (h : SubgroupFunctor.range l = SubgroupFunctor.range l') :
    (subgroupIsoOfRangeEq l l' hl hl' h).hom ≫ l' = l := by
  apply SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp

/-- Smoothness depends only on the represented closed subgroup functor. -/
theorem smooth_of_range_eq {L L' P : GroupScheme S} (l : L ⟶ P) (l' : L' ⟶ P)
    (hl : IsClosedSubgroup l) (hl' : IsClosedSubgroup l')
    (h : SubgroupFunctor.range l = SubgroupFunctor.range l')
    (hSmooth : Smooth L'.X.hom) : Smooth L.X.hom := by
  let e := (Grp.forget (Over S)).mapIso (subgroupIsoOfRangeEq l l' hl hl' h)
  let e' := (Over.forget S).mapIso e
  have he : e'.hom ≫ L'.X.hom = L.X.hom := Over.w e.hom
  let : Smooth L'.X.hom := hSmooth
  rw [← he]
  infer_instance

/-- Isomorphy of multiplication depends only on the all-test ranges of its
two closed factors. -/
theorem subgroupMultiplication_isIso_of_range_eq {L U L' U' P : GroupScheme S}
    (l : L ⟶ P) (r : U ⟶ P) (l' : L' ⟶ P) (r' : U' ⟶ P)
    (hl : IsClosedSubgroup l) (hr : IsClosedSubgroup r)
    (hl' : IsClosedSubgroup l') (hr' : IsClosedSubgroup r')
    (hL : SubgroupFunctor.range l = SubgroupFunctor.range l')
    (hU : SubgroupFunctor.range r = SubgroupFunctor.range r')
    [IsIso (subgroupMultiplication l' r')] : IsIso (subgroupMultiplication l r) :=
  subgroupMultiplication_isIso_of_iso l r l' r'
    (subgroupIsoOfRangeEq l l' hl hl' hL) (subgroupIsoOfRangeEq r r' hr hr' hU)
    (subgroupIsoOfRangeEq_hom_comp l l' hl hl' hL)
    (subgroupIsoOfRangeEq_hom_comp r r' hr hr' hU)

/-- A global closed subgroup is Levi if its pullbacks and those of a supplied
global radical have the ranges of local smooth closed multiplication factors. -/
theorem isRelativeLeviSubgroup_of_local_ranges
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {L U P : GroupScheme S} (l : L ⟶ P) (r : U ⟶ P)
    (hl : IsClosedSubgroup l) (hr : IsRelativeUnipotentRadical r)
    (Lloc Uloc : ∀ i, GroupScheme (𝒰.X i))
    (lloc : ∀ i, Lloc i ⟶ (baseChange (𝒰.f i)).obj P)
    (rloc : ∀ i, Uloc i ⟶ (baseChange (𝒰.f i)).obj P)
    (hloc : ∀ i, IsClosedSubgroup (lloc i))
    (hrloc : ∀ i, IsClosedSubgroup (rloc i))
    (hSmooth : ∀ i, Smooth (Lloc i).X.hom)
    (hMul : ∀ i, IsIso (subgroupMultiplication (lloc i) (rloc i)))
    (hL : ∀ i, SubgroupFunctor.range ((baseChange (𝒰.f i)).map l) =
      SubgroupFunctor.range (lloc i))
    (hU : ∀ i, SubgroupFunctor.range ((baseChange (𝒰.f i)).map r) =
      SubgroupFunctor.range (rloc i)) : IsRelativeLeviSubgroup l := by
  apply isRelativeLeviSubgroup_of_etaleCover 𝒰 l r hl hr
  · intro i
    exact smooth_of_range_eq _ _ (hl.baseChange (𝒰.f i)) (hloc i) (hL i) (hSmooth i)
  · intro i
    let := hMul i
    exact subgroupMultiplication_isIso_of_range_eq _ _ _ _
      (hl.baseChange (𝒰.f i)) (hr.isClosedSubgroup.baseChange (𝒰.f i))
      (hloc i) (hrloc i) (hL i) (hU i)

/-- An actual closed group scheme representing an all-test subgroup and equipped
with the existing relative Levi property. -/
structure LeviRepresentative {P : GroupScheme S} (F : SubgroupFunctor P)
    extends SubgroupFunctor.ClosedRepresentative F where
  isLevi : IsRelativeLeviSubgroup hom

/-- Matching local smooth closed multiplication factors descend to an actual
Levi representative when their radical ranges agree with a supplied global
relative unipotent radical. -/
def leviRepresentativeOfEtaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {U P : GroupScheme S} (r : U ⟶ P) (hr : IsRelativeUnipotentRadical r)
    (F : ∀ i, SubgroupFunctor ((baseChange (𝒰.f i)).obj P))
    (hF : SubgroupFunctor.CoverDescent.IsMatching 𝒰 F)
    (Lloc Uloc : ∀ i, GroupScheme (𝒰.X i))
    (lloc : ∀ i, Lloc i ⟶ (baseChange (𝒰.f i)).obj P)
    (rloc : ∀ i, Uloc i ⟶ (baseChange (𝒰.f i)).obj P)
    (hrep : ∀ i, (F i).IsRepresentedBy (lloc i))
    (hloc : ∀ i, IsClosedSubgroup (lloc i))
    (hrloc : ∀ i, IsClosedSubgroup (rloc i))
    (hSmooth : ∀ i, Smooth (Lloc i).X.hom)
    (hMul : ∀ i, IsIso (subgroupMultiplication (lloc i) (rloc i)))
    (hU : ∀ i, SubgroupFunctor.range ((baseChange (𝒰.f i)).map r) =
      SubgroupFunctor.range (rloc i)) :
    LeviRepresentative (SubgroupFunctor.CoverDescent.subgroup 𝒰 F) := by
  let c := SubgroupFunctor.CoverDescent.closedRepresentativeEtale 𝒰 F hF
    (fun i => ⟨Lloc i, lloc i, hrep i, hloc i⟩)
  refine { toClosedRepresentative := c, isLevi := ?_ }
  apply isRelativeLeviSubgroup_of_local_ranges 𝒰 c.hom r c.closed hr
    Lloc Uloc lloc rloc hloc hrloc hSmooth hMul
  · intro i
    rw [SubgroupFunctor.range_baseChangeHom, c.represents.2,
      SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰 F hF i]
    exact (hrep i).2.symm
  · exact hU

end Langlands.GroupScheme.RelativeLevi
