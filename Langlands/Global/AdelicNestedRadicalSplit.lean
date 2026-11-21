import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # A split extension between the radicals of nested standard parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J Q : StandardIndex F G fam.i fam.ν)

/-- The larger radical splits as an extension of the inner Levi radical
by the smaller radical. The assertions are on the actual schemes. -/
structure NestedRadicalSplit (fam : StandardParabolicFamily F G)
    (J Q : StandardIndex F G fam.i fam.ν) where
  W : GroupScheme (Spec (CommRingCat.of F))
  normal : fam.U Q ⟶ fam.U J
  sectionHom : W ⟶ fam.U J
  leviHom : W ⟶ fam.M Q
  projection : fam.U J ⟶ W
  normal_comp : normal ≫ fam.iU J ≫ fam.p J = fam.iU Q ≫ fam.p Q
  section_comp : sectionHom ≫ fam.iU J ≫ fam.p J = leviHom ≫ fam.l Q ≫ fam.p Q
  section_projection : sectionHom ≫ projection = 𝟙 W
  section_closed : IsClosedSubgroup sectionHom
  kernel : ∀ (X : Over (Spec (CommRingCat.of F))) (x : X ⟶ (fam.U J).X),
    x ≫ projection.hom.hom = 1 ↔ ∃ n : X ⟶ (fam.U Q).X, n ≫ normal.hom.hom = x

/-- For nested standard indices this splitting is induced by the actual
Levi retraction and holds on every test scheme. -/
def NestedRadicalSplitStatement : Prop := J ≤ Q → Nonempty (NestedRadicalSplit fam J Q)

set_option maxHeartbeats 1800000 in
theorem nestedRadicalSplit : NestedRadicalSplitStatement fam J Q := by
  intro hJQ
  let q := fam.p Q
  let m := fam.l Q
  let r := fam.iU Q
  let v := fam.iU J ≫ fam.p J
  let n := r ≫ q
  let l := m ≫ q
  let hc := (fam.isCompatible Q).parabolic.isClosedSubgroup
  let hv : IsClosedSubgroup v := fam.closedU J
  let : Mono q.hom.hom.left := hc.mono
  let : Mono v.hom.hom.left := hv.mono
  let hl := (fam.isCompatible Q).levi.isClosedSubgroup.comp hc
  let : Mono l.hom.hom.left := hl.mono
  let : Mono q.hom.hom := Over.mono_of_mono_left _
  let : Mono q := (Grp.forget _).mono_of_mono_map (f := q) ‹Mono q.hom.hom›
  let : Mono v.hom.hom := Over.mono_of_mono_left _
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  let hr := fam.isUnipotentRadical Q
  let R : ParabolicRootPresentation q m (fam.a Q) :=
    ⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩
  let : IsIso (subgroupMultiplication m r) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication R fam.connectedReductive hr
  let π := leviRetraction m r hr.1.isNormal
  let H := subgroupIntersection v l
  let s := subgroupIntersectionFst v l
  let t := subgroupIntersectionSnd v l
  let h := subgroupIntersectionHom v l
  have hh : h = s ≫ v := rfl
  have ht : h = t ≫ l := subgroupIntersection_condition v l
  have hs : IsClosedSubgroup s := isClosedSubgroup_subgroupIntersectionFst v hl
  let : Mono h.hom.hom.left := ((hs.comp hv) : IsClosedSubgroup h).mono
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  let : Mono h := (Grp.forget _).mono_of_mono_map (f := h) ‹Mono h.hom.hom›
  have hN : SubgroupFunctor.range n ≤ SubgroupFunctor.range v := fam.radical_le_of_le hJQ
  have hV : SubgroupFunctor.range v ≤ SubgroupFunctor.range q :=
    (SubgroupFunctor.range_comp_le _ _).trans ((fam.le_iff_range_le J Q).mp hJQ)
  let vQ := SubgroupFunctor.rangeFactor v q hV
  have hvQ : vQ ≫ q = v := SubgroupFunctor.rangeFactor_comp v q hV
  let inc := SubgroupFunctor.rangeFactor n v hN
  have hι : inc ≫ v = n := SubgroupFunctor.rangeFactor_comp n v hN
  let proj := vQ ≫ π ≫ l
  have hProj : SubgroupFunctor.range proj ≤ SubgroupFunctor.range h := by
    rw [show SubgroupFunctor.range h = SubgroupFunctor.range v ⊓ SubgroupFunctor.range l from
      range_subgroupIntersectionHom _ _]
    intro X x hx
    obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    let a := u ≫ vQ.hom.hom
    let b := radicalComponent m r a
    have ha : a ≫ q.hom.hom ∈ (SubgroupFunctor.range v).carrier X := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hvQ]
      exact ⟨u, rfl⟩
    have hb : (b ≫ r.hom.hom) ≫ q.hom.hom ∈ (SubgroupFunctor.range v).carrier X := by
      apply hN X
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨b, ?_⟩
      simp only [n, Grp.comp_hom_hom, Category.assoc]
    have hDecomp : ((a ≫ π.hom.hom) ≫ m.hom.hom) * (b ≫ r.hom.hom) = a := by
      rw [comp_leviRetraction]
      exact leviComponent_mul_radicalComponent m r a
    have hVsplit : (((a ≫ π.hom.hom) ≫ m.hom.hom) ≫ q.hom.hom) *
        ((b ≫ r.hom.hom) ≫ q.hom.hom) = a ≫ q.hom.hom := by
      rw [← MonObj.mul_comp, hDecomp]
    refine ⟨?_, SubgroupFunctor.mem_range.mpr ⟨a ≫ π.hom.hom, ?_⟩⟩
    · change u ≫ proj.hom.hom ∈ (SubgroupFunctor.range v).carrier X
      have hz : u ≫ proj.hom.hom =
          ((a ≫ π.hom.hom) ≫ m.hom.hom) ≫ q.hom.hom := by
        simp only [proj, a, l, Grp.comp_hom_hom, Category.assoc]
      rw [hz, (eq_mul_inv_iff_mul_eq).mpr hVsplit]
      exact mul_mem ha (inv_mem hb)
    · simp only [proj, a, Grp.comp_hom_hom, Category.assoc]
  let d := SubgroupFunctor.rangeFactor proj h hProj
  have hd : d ≫ h = proj := SubgroupFunctor.rangeFactor_comp proj h hProj
  have hsQ : s ≫ vQ = t ≫ m := by
    apply (cancel_mono q).mp
    rw [Category.assoc, Category.assoc, hvQ, ← hh]
    exact ht
  have hsD : s ≫ d = 𝟙 H := by
    have hlπ : m ≫ π = 𝟙 (fam.M Q) := levi_comp_leviRetraction m r hr.1.isNormal
    apply (cancel_mono h).mp
    rw [Category.assoc, hd, Category.id_comp]
    change s ≫ vQ ≫ π ≫ l = h
    rw [← Category.assoc s vQ, hsQ, Category.assoc, ← Category.assoc m π, hlπ,
      Category.id_comp, ht]
  have hIncQ : inc ≫ vQ = r := by
    apply (cancel_mono q).mp
    rw [Category.assoc, hvQ, hι]
  have hIncHom : inc.hom.hom ≫ vQ.hom.hom = r.hom.hom := by
    simpa only [Grp.comp_hom_hom] using congrArg (fun z => z.hom.hom) hIncQ
  let : Mono vQ.hom.hom.left := SubgroupFunctor.rangeFactor_mono v q hV
  let : Mono vQ.hom.hom := Over.mono_of_mono_left _
  refine ⟨⟨H, inc, s, t, d, hι, ht, hsD, hs, ?_⟩⟩
  intro X x
  have hdiag : (x ≫ d.hom.hom) ≫ h.hom.hom =
      ((x ≫ vQ.hom.hom) ≫ π.hom.hom) ≫ l.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hd]
    simp only [proj, Grp.comp_hom_hom, Category.assoc]
  have hproj : x ≫ d.hom.hom = 1 ↔ (x ≫ vQ.hom.hom) ≫ π.hom.hom = 1 := by
    constructor
    · intro hx
      apply (cancel_mono l.hom.hom).mp
      rw [← hdiag, hx, MonObj.one_comp, MonObj.one_comp]
    · intro hx
      apply (cancel_mono h.hom.hom).mp
      rw [hdiag, hx, MonObj.one_comp, MonObj.one_comp]
  rw [hproj, comp_leviRetraction_eq_one_iff]
  change (∃ u : X ⟶ (fam.U Q).X, u ≫ r.hom.hom = x ≫ vQ.hom.hom) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, (cancel_mono vQ.hom.hom).mp ?_⟩
    rw [Category.assoc, hIncHom, hu]
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [Category.assoc, hIncHom]⟩

end Langlands.Global.StandardParabolicFamily
