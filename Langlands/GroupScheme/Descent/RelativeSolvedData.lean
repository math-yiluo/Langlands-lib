import Langlands.GroupScheme.Descent.EtaleReflection
import Langlands.GroupScheme.Descent.EtaleHomDescent
import Langlands.GroupScheme.Descent.RelativeQuasiSplitDatum

/-! # Relative quasi-split data from compatible actual descent solutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An actual relatively quasi-split group with a specified Borel and a
closed fibrewise maximal relative torus contained in it. -/
structure RelativeQuasiSplitTorusData {S : Scheme.{u}} (G : GroupScheme S) where
  reductive : IsReductive G
  borel : RelativeBorelData G
  torus : CommGroupScheme S
  torusInclusion : torus.toGrp ⟶ G
  torusIsTorus : RelativeTorus.IsTorus torus.toGrp
  torusClosed : IsClosedSubgroup torusInclusion
  torusMaximal : IsFibrewiseMaximalTorus torusInclusion
  torus_le_borel : SubgroupFunctor.range torusInclusion ≤
    SubgroupFunctor.range borel.inclusion

/-- The specified Borel witnesses relative quasi-splitness. -/
theorem RelativeQuasiSplitTorusData.quasiSplit {S : Scheme.{u}} {G : GroupScheme S}
    (d : RelativeQuasiSplitTorusData G) : IsRelativeQuasiSplit G :=
  ⟨d.reductive, d.borel.obj, d.borel.inclusion, d.borel.isBorel⟩

namespace Descent.Solution

section Commutativity

variable {S U : Scheme.{u}} {p : U ⟶ S} [Etale p] [Surjective p]
  {T : CommGroupScheme U} {F : Datum p T.toGrp} (r : Solution F)

/-- Recover the commutative group structure on any actual torus-data solution. -/
def commGroupSchemeOfEtale : CommGroupScheme S where
  toGrp := r.obj
  comm := isCommMonObj_of_baseChange_of_etale p r.obj
    (Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono r.iso.hom.hom.hom)

end Commutativity

section Assembly

variable {S U : Scheme.{u}} {p : U ⟶ S} [Etale p] [Surjective p]
  {G B : GroupScheme U} {T : CommGroupScheme U}
  {D : Datum p G} {E : Datum p B} {F : Datum p T.toGrp}
  {i : B ⟶ G} {t : T.toGrp ⟶ G}

/-- Compatible actual ambient, Borel and torus solutions construct relative
quasi-split data over any base, without a quasi-compact-cover assumption. -/
def relativeQuasiSplitTorusData
    (s : Solution D) (b : Solution E) (r : Solution F)
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i)
    (hiClosed : IsClosedSubgroup i) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hBi : Compatible E D i) (hTt : Compatible F D t)
    (hincl : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    RelativeQuasiSplitTorusData s.obj := by
  let T₀ := r.commGroupSchemeOfEtale
  let j := b.descendHomOfEtale s i hBi
  let t₀ := r.descendHomOfEtale s t hTt
  have hjrec : (GroupScheme.baseChange p).map j =
      b.iso.hom ≫ i ≫ s.iso.inv := by
    rw [← Category.assoc, ← baseChange_descendHomOfEtale,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have htrec : (GroupScheme.baseChange p).map t₀ =
      r.iso.hom ≫ t ≫ s.iso.inv := by
    rw [← Category.assoc, ← baseChange_descendHomOfEtale,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hjClosed : IsClosedSubgroup j := by
    apply IsClosedSubgroup.of_baseChange_of_etale p
    rw [hjrec, ← Category.assoc]
    exact ((IsClosedSubgroup.of_iso b.iso).comp hiClosed).comp_iso s.iso.symm
  have htClosed : IsClosedSubgroup t₀ := by
    apply IsClosedSubgroup.of_baseChange_of_etale p
    rw [htrec, ← Category.assoc]
    exact ((IsClosedSubgroup.of_iso r.iso).comp ht).comp_iso s.iso.symm
  have hred : IsReductive s.obj :=
    IsReductive.of_baseChange_of_etale p (hG.of_iso s.iso)
  let : IsAffineHom s.obj.X.hom := hred.isAffineHom
  have hjBorel : IsRelativeBorelSubgroup j := by
    apply IsRelativeBorelSubgroup.of_baseChange_of_etale p hjClosed
    rw [hjrec, ← Category.assoc]
    exact (hi.iso_comp b.iso).comp_iso s.iso.symm
  have hT₀ : RelativeTorus.IsTorus T₀.toGrp :=
    RelativeTorus.IsTorus.of_baseChange_of_etale p
      (RelativeTorus.IsTorus.of_iso r.iso hT)
  have hmaxUp : IsFibrewiseMaximalTorus
      (T := (CommGroupScheme.baseChange p).obj T₀)
      ((GroupScheme.baseChange p).map t₀) := by
    rw [htrec, ← Category.assoc]
    exact (IsFibrewiseMaximalTorus.iso_comp
      (T' := (CommGroupScheme.baseChange p).obj T₀) hmax r.iso).comp_iso s.iso.symm
  have hmax₀ : IsFibrewiseMaximalTorus (T := T₀) t₀ :=
    IsFibrewiseMaximalTorus.of_baseChange p htClosed hmaxUp
  have hincl₀ : SubgroupFunctor.range t₀ ≤ SubgroupFunctor.range j := by
    let : IsClosedImmersion j.hom.hom.left := hjClosed
    let : Mono j.hom.hom := Over.mono_of_mono_left _
    apply SubgroupFunctor.le_range_of_etaleBaseChange_le p j
    rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom,
      htrec, hjrec, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_iso_comp]
    exact (SubgroupFunctor.range_comp_iso_le_iff t i s.iso.symm).2 hincl
  exact
    { reductive := hred
      borel := ⟨b.obj, j, hjBorel⟩
      torus := T₀
      torusInclusion := t₀
      torusIsTorus := hT₀
      torusClosed := htClosed
      torusMaximal := hmax₀
      torus_le_borel := hincl₀ }

end Assembly

end Descent.Solution

end Langlands.GroupScheme
