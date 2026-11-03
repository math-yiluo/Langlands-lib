import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup

/-! # Canonical comparison of represented solvable radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {P R R' : GroupScheme (Spec (CommRingCat.of k))}
  {r : R ⟶ P} {r' : R' ⟶ P}

namespace IsSolvableRadical

/-- Greatest represented solvable radicals have the same image on every test scheme. -/
theorem range_eq (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r') :
    SubgroupFunctor.range r = SubgroupFunctor.range r' :=
  le_antisymm
    (hr'.greatest R r hr.isClosedSubgroup hr.smooth hr.connectedSpace
      hr.isSolvableGroupScheme hr.isNormal)
    (hr.greatest R' r' hr'.isClosedSubgroup hr'.smooth hr'.connectedSpace
      hr'.isSolvableGroupScheme hr'.isNormal)

/-- The canonical isomorphism between two representatives of the solvable radical. -/
def iso (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r') : R ≅ R' := by
  letI : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  letI : IsClosedImmersion r'.hom.hom.left := hr'.isClosedSubgroup
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (show (SubgroupFunctor.range r).IsRepresentedBy r from
      ⟨Over.mono_of_mono_left _, rfl⟩)
    (show (SubgroupFunctor.range r).IsRepresentedBy r' from
      ⟨Over.mono_of_mono_left _, (hr.range_eq hr').symm⟩)

/-- The comparison isomorphism preserves the actual inclusion in the ambient group. -/
@[simp] theorem iso_hom_comp (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r') :
    (hr.iso hr').hom ≫ r' = r := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The inverse comparison also preserves the actual inclusion. -/
@[simp] theorem iso_inv_comp (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r') :
    (hr.iso hr').inv ≫ r = r' := by
  calc
    (hr.iso hr').inv ≫ r = (hr.iso hr').inv ≫ ((hr.iso hr').hom ≫ r') :=
      congrArg (fun f => (hr.iso hr').inv ≫ f) (hr.iso_hom_comp hr').symm
    _ = r' := (hr.iso hr').inv_hom_id_assoc r'

/-- Compatibility with the inclusion uniquely determines the comparison homomorphism. -/
theorem iso_hom_unique (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r')
    {f : R ⟶ R'} (hf : f ≫ r' = r) : f = (hr.iso hr').hom := by
  let : IsClosedImmersion r'.hom.hom.left := hr'.isClosedSubgroup
  have hrep : (SubgroupFunctor.range r').IsRepresentedBy r' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  apply hrep.hom_ext
  rw [hf, iso_hom_comp]

variable {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Transport an actual morphism into one radical to the specified representative. -/
def factor (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r') (b : H ⟶ R) :
    H ⟶ R' :=
  b ≫ (hr.iso hr').hom

/-- Transport preserves the actual ambient morphism. -/
@[simp] theorem factor_comp (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r')
    (b : H ⟶ R) : hr.factor hr' b ≫ r' = b ≫ r := by
  simp only [factor, Category.assoc, iso_hom_comp]

/-- Transport is the unique morphism with the original ambient composite. -/
theorem factor_unique (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r')
    (b : H ⟶ R) {b' : H ⟶ R'} (hb' : b' ≫ r' = b ≫ r) :
    b' = hr.factor hr' b := by
  let : IsClosedImmersion r'.hom.hom.left := hr'.isClosedSubgroup
  have hrep : (SubgroupFunctor.range r').IsRepresentedBy r' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  apply hrep.hom_ext
  rw [hb', factor_comp]

/-- The composite stays equal after any further ambient inclusion. -/
@[simp] theorem factor_comp_ambient (hr : IsSolvableRadical r)
    (hr' : IsSolvableRadical r') (b : H ⟶ R)
    {G : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ G) :
    hr.factor hr' b ≫ r' ≫ j = b ≫ r ≫ j := by
  rw [← Category.assoc, factor_comp, Category.assoc]

variable {B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The transported morphism of a split subtorus is still a split subtorus. -/
theorem isSplitSubtorus_factor (hr : IsSolvableRadical r) (hr' : IsSolvableRadical r')
    {b : B.toGrp ⟶ R} (hb : IsSplitSubtorus b) :
    IsSplitSubtorus (hr.factor hr' b) :=
  hb.comp (IsClosedSubgroup.of_iso (hr.iso hr'))

/-- Maximal splitness inside the radical is independent of its representative. -/
theorem isMaximalSplitTorus_factor (hr : IsSolvableRadical r)
    (hr' : IsSolvableRadical r') {b : B.toGrp ⟶ R} (hb : IsMaximalSplitTorus b) :
    IsMaximalSplitTorus (hr.factor hr' b) := by
  apply IsMaximalSplitTorus.of_comp (IsClosedSubgroup.of_iso (hr.iso hr').symm)
  simpa only [factor, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using hb

end IsSolvableRadical

end Langlands.GroupScheme
