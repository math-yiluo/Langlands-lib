import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.GroupScheme.Rational.NestedParabolicPreimage
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionProof
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # Actual parabolics inside the Levis of a standard family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (I J : StandardIndex F G fam.i fam.ν)

/-- The smaller standard parabolic is pulled back from an actual
parabolic of the outer Levi. The inner radical maps into the original
smaller radical, and strict inclusion gives a proper inner parabolic. -/
structure NestedLeviParabolic where
  inclusion : fam.P I ⟶ fam.P J
  inclusion_comp : inclusion ≫ fam.p J = fam.p I
  projection : fam.P J ⟶ fam.M J
  section_projection : fam.l J ≫ projection = 𝟙 (fam.M J)
  P : GroupScheme (Spec (CommRingCat.of F))
  M : GroupScheme (Spec (CommRingCat.of F))
  U : GroupScheme (Spec (CommRingCat.of F))
  p : P ⟶ fam.M J
  l : M ⟶ P
  iU : U ⟶ P
  parabolic : IsParabolicSubgroup p
  levi : IsRationalLeviSubgroup l
  unipotentRadical : LeviSubgroup.IsGeometricUnipotentRadical iU
  leviSplit : IsIso (subgroupMultiplication l iU)
  pullback_eq : SubgroupFunctor.range inclusion = (SubgroupFunctor.range p).comap projection
  radical_le : SubgroupFunctor.range (iU ≫ p ≫ fam.l J ≫ fam.p J) ≤
    SubgroupFunctor.range (fam.iU I ≫ fam.p I)
  proper : I < J → SubgroupFunctor.range p ≠ ⊤

/-- Nested standard indices supply the inner parabolic and its
representative comparison on every test scheme. -/
def StandardNestedLeviParabolicStatement : Prop :=
  I ≤ J → Nonempty (NestedLeviParabolic fam I J)

set_option maxHeartbeats 1600000 in
theorem standardNestedLeviParabolic : StandardNestedLeviParabolicStatement fam I J := by
  intro hIJ
  let qI := fam.p I
  let qJ := fam.p J
  let lJ := fam.l J
  let uJ := fam.iU J
  let hJ := fam.isCompatible J
  let hI := fam.isCompatible I
  let R : ParabolicRootPresentation qJ lJ (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, hJ⟩
  let : IsIso (subgroupMultiplication lJ uJ) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication R
      fam.connectedReductive (fam.isUnipotentRadical J)
  let hqJ := hJ.parabolic.isClosedSubgroup
  let hqI := hI.parabolic.isClosedSubgroup
  let hlJ := hJ.levi.isClosedSubgroup.comp hqJ
  let : Mono qJ.hom.hom := hqJ.mono_overHom
  let : Mono qI.hom.hom := hqI.mono_overHom
  let : Mono (lJ ≫ qJ).hom.hom := hlJ.mono_overHom
  let : Smooth (fam.P J).X.hom := hJ.parabolic.smooth
  let : IsAffineHom (fam.P J).X.hom := hqJ.isAffineHom
  let : ConnectedSpace (fam.P J).X.left := hJ.levi.connectedSpace
  have hincl : SubgroupFunctor.range qI ≤ SubgroupFunctor.range qJ :=
    (fam.le_iff_range_le I J).mp hIJ
  let hRepI : (SubgroupFunctor.range qI).IsRepresentedBy qI := ⟨inferInstance, rfl⟩
  let hRepJ : (SubgroupFunctor.range qJ).IsRepresentedBy qJ := ⟨inferInstance, rfl⟩
  let inc := hRepI.inclusionHom hRepJ hincl
  have hInc : inc ≫ qJ = qI := hRepI.inclusionHom_comp hRepJ hincl
  have hIncRange : SubgroupFunctor.range inc = (SubgroupFunctor.range qI).comap qJ := by
    apply SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf
    rw [hInc]
    exact SubgroupFunctor.ext fun X => (inf_eq_right.mpr (hincl X)).symm
  let hRadJ := fam.isUnipotentRadical J
  let proj := leviRetraction lJ uJ hRadJ.1.isNormal
  obtain ⟨P, M, U, s, t, u, hs, hu, ht, hmul, hsRange, -, huRange⟩ :=
    representedParabolicLeviIntersection F G fam.connectedReductive
      (fam.P J) (fam.M J) (fam.P I) (fam.M I) (fam.U I)
      qJ lJ hJ.parabolic hJ.levi qI (fam.l I) (fam.iU I)
      hI.parabolic hI.levi (fam.isUnipotentRadical I)
      (Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication
        (⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, hI⟩ :
          ParabolicRootPresentation qI (fam.l I) (fam.a I))
        fam.connectedReductive (fam.isUnipotentRadical I))
      fam.T fam.i fam.maximalSplit ⟨fam.torus J, fam.torus_comp J⟩
      ⟨fam.torus I, fam.torus_comp I⟩
  have hsInt : SubgroupFunctor.range s = (SubgroupFunctor.range qI).comap (lJ ≫ qJ) :=
    SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf s (lJ ≫ qJ) _
      (by simpa only [Category.assoc] using hsRange)
  have hOuterRad : SubgroupFunctor.range uJ ≤ SubgroupFunctor.range inc :=
    range_normalUnipotent_le_nestedParabolic qI qJ inc uJ hI.parabolic hqJ hInc hRadJ
  have hSubLevi : SubgroupFunctor.range (s ≫ lJ) ≤ SubgroupFunctor.range inc := by
    intro X x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hmem : y ≫ s.hom.hom ∈ (SubgroupFunctor.range s).carrier X := ⟨y, rfl⟩
    rw [hsInt, SubgroupFunctor.mem_comap] at hmem
    rw [hIncRange, SubgroupFunctor.mem_comap]
    simpa only [Grp.comp_hom_hom, Category.assoc] using hmem
  have hProj : SubgroupFunctor.range (inc ≫ proj) ≤ SubgroupFunctor.range s := by
    intro X x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    let a := y ≫ inc.hom.hom
    let v := radicalComponent lJ uJ a
    have ha : a ∈ (SubgroupFunctor.range inc).carrier X := ⟨y, rfl⟩
    have hv : v ≫ uJ.hom.hom ∈ (SubgroupFunctor.range inc).carrier X :=
      hOuterRad X ⟨v, rfl⟩
    have hdecomp : (a ≫ proj.hom.hom) ≫ lJ.hom.hom * (v ≫ uJ.hom.hom) = a := by
      rw [comp_leviRetraction]
      exact leviComponent_mul_radicalComponent lJ uJ a
    have hLevi : (a ≫ proj.hom.hom) ≫ lJ.hom.hom ∈ (SubgroupFunctor.range inc).carrier X := by
      rw [(eq_mul_inv_iff_mul_eq).mpr hdecomp]
      exact (SubgroupFunctor.range inc).carrier X |>.mul_mem ha (inv_mem hv)
    rw [hIncRange, SubgroupFunctor.mem_comap] at hLevi
    rw [hsInt, SubgroupFunctor.mem_comap]
    simpa only [a, Grp.comp_hom_hom, Category.assoc] using hLevi
  have hPre := range_eq_comap_leviRetraction inc lJ uJ s hRadJ.1.isNormal hSubLevi hOuterRad hProj
  refine ⟨⟨inc, hInc, proj, levi_comp_leviRetraction lJ uJ hRadJ.1.isNormal,
    P, M, U, s, t, u, hs, ht, hu, hmul, hPre, ?_, ?_⟩⟩
  · change SubgroupFunctor.range (u ≫ s ≫ lJ ≫ qJ) ≤
      SubgroupFunctor.range (fam.iU I ≫ qI)
    rw [huRange]
    exact fun X => inf_le_right (α := Subgroup _)
  · intro hlt htop
    have hrev : SubgroupFunctor.range qJ ≤ SubgroupFunctor.range qI := by
      intro X x hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      have hy : y ∈ (SubgroupFunctor.range inc).carrier X := by
        rw [hPre, SubgroupFunctor.mem_comap, htop]
        exact Subgroup.mem_top _
      rw [hIncRange, SubgroupFunctor.mem_comap] at hy
      exact hy
    exact (not_le_of_gt hlt) ((fam.le_iff_range_le J I).mpr hrev)

end Langlands.Global.StandardParabolicFamily
