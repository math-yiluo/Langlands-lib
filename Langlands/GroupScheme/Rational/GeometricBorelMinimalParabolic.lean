import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.BaseChangeReflection

/-! # A geometric Borel is a minimal rational parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {B P G : GroupScheme (Spec (CommRingCat.of k))}

/-- A parabolic factor into a field-defined geometric Borel is an isomorphism. -/
theorem IsGeometricBorelSubgroup.isIso_parabolicFactor {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) {j : P ⟶ G}
    (hj : IsParabolicSubgroup j) (f : P ⟶ B) (hf : f ≫ i = j) : IsIso f := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  obtain ⟨D, d, l, hd, hl⟩ := hj.exists_isBorelSubgroup
  have hfi : F.map f ≫ F.map i = F.map j := by rw [← F.map_comp, hf]
  have hcomp : (l ≫ F.map f) ≫ F.map i = d := by
    rw [Category.assoc, hfi]
    exact hl
  let : IsIso (l ≫ F.map f) := hd.maximal _ (F.map i) (l ≫ F.map f)
    hi.2.isClosedSubgroup hi.2.smooth hi.2.connectedSpace hi.2.isSolvableGroupScheme hcomp
  let : IsClosedImmersion (F.map j).hom.hom.left := hj.isClosedSubgroup.baseChange b
  let : Mono (F.map j).hom.hom := Over.mono_of_mono_left _
  let : Mono (F.map j) := (Grp.forget _).mono_of_mono_map
    (show Mono (F.map j).hom.hom from Over.mono_of_mono_left _)
  let : Mono (F.map f) := mono_of_mono_fac hfi
  let : IsSplitEpi (F.map f) := IsSplitEpi.mk' {
    section_ := inv (l ≫ F.map f) ≫ l
    id := by rw [Category.assoc, IsIso.inv_hom_id] }
  let : IsIso (F.map f) := isIso_of_mono_of_isSplitEpi _
  obtain ⟨hbSurj, hbFlat, hbQC⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hbSurj
  let : Flat b := hbFlat
  let : QuasiCompact b := hbQC
  exact isIso_of_baseChange b f

/-- A parabolic factoring through a field-defined geometric Borel has exactly
that source presentation, by an actual isomorphism over the ground field. -/
def IsGeometricBorelSubgroup.parabolicFactorIso {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) {j : P ⟶ G}
    (hj : IsParabolicSubgroup j) (f : P ⟶ B) (hf : f ≫ i = j) : P ≅ B := by
  let : IsIso f := hi.isIso_parabolicFactor hj f hf
  exact asIso f

@[simp] theorem IsGeometricBorelSubgroup.parabolicFactorIso_hom {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) {j : P ⟶ G}
    (hj : IsParabolicSubgroup j) (f : P ⟶ B) (hf : f ≫ i = j) :
    (hi.parabolicFactorIso hj f hf).hom = f := rfl

/-- A field-defined geometric Borel is minimal among rational parabolics,
with inclusions checked on every scheme test. -/
theorem IsGeometricBorelSubgroup.isMinimalParabolicSubgroup {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) : IsMinimalParabolicSubgroup i := by
  refine ⟨hi.isParabolicSubgroup, ?_⟩
  intro P j hj hle
  let : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let f := hrep.factorHom j hle
  have hf : f ≫ i = j := hrep.factorHom_comp j hle
  let e := hi.parabolicFactorIso hj f hf
  change SubgroupFunctor.range j = SubgroupFunctor.range i
  rw [← hf]
  exact SubgroupFunctor.range_iso_comp e i

/-- Minimality of the all-test range of a geometric Borel. -/
theorem IsGeometricBorelSubgroup.isMinimalParabolicFunctor {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) :
    IsMinimalParabolicFunctor (SubgroupFunctor.range i) :=
  hi.isMinimalParabolicSubgroup.isMinimalParabolicFunctor

end Langlands.GroupScheme
