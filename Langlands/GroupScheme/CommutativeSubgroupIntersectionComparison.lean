import Langlands.GroupScheme.CommutativeSubgroupIntersectionBaseChange
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Comparison with actual commutative intersection representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {B : Scheme.{u}} {P R : GroupScheme B} {T S : CommGroupScheme B}
variable (f : T.toGrp ⟶ P) (r : R ⟶ P) [Mono r.hom.hom]
variable (sT : S.toGrp ⟶ T.toGrp)
variable (hf : IsClosedSubgroup f) (hr : IsClosedSubgroup r)
  (hsT : IsClosedSubgroup sT)
variable (hRange : SubgroupFunctor.range (sT ≫ f) =
  SubgroupFunctor.range f ⊓ SubgroupFunctor.range r)

/-- The canonical intersection is isomorphic to any closed commutative
representative of its image on every test scheme. -/
def commutativeSubgroupIntersectionRepresentativeIso :
    (commutativeSubgroupIntersection f r).toGrp ≅ S.toGrp := by
  let : IsClosedImmersion (sT ≫ f).hom.hom.left := hsT.comp hf
  exact (isRepresentedBy_commutativeSubgroupIntersection f r hf hr).isoOfIsRepresentedBy
    ⟨Over.mono_of_mono_left _, hRange⟩

/-- The comparison preserves the actual common map into the ambient group. -/
@[reassoc]
theorem commutativeSubgroupIntersectionRepresentativeIso_hom_comp :
    (commutativeSubgroupIntersectionRepresentativeIso f r sT hf hr hsT hRange).hom ≫
      (sT ≫ f) = commutativeSubgroupIntersectionFst f r ≫ f := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The comparison preserves the specified map into the commutative factor. -/
@[reassoc]
theorem commutativeSubgroupIntersectionRepresentativeIso_hom_fst :
    (commutativeSubgroupIntersectionRepresentativeIso f r sT hf hr hsT hRange).hom ≫
      sT = commutativeSubgroupIntersectionFst f r := by
  let : IsClosedImmersion f.hom.hom.left := hf
  have hrep : (SubgroupFunctor.range f).IsRepresentedBy f :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  apply hrep.hom_ext
  rw [Category.assoc, commutativeSubgroupIntersectionRepresentativeIso_hom_comp]

/-- Compatibility in the ambient group forces preservation of the second map. -/
@[reassoc]
theorem commutativeSubgroupIntersectionRepresentativeIso_hom_snd
    (sR : S.toGrp ⟶ R) (h : sT ≫ f = sR ≫ r) :
    (commutativeSubgroupIntersectionRepresentativeIso f r sT hf hr hsT hRange).hom ≫
      sR = commutativeSubgroupIntersectionSnd f r := by
  have hrep : (SubgroupFunctor.range r).IsRepresentedBy r := ⟨inferInstance, rfl⟩
  apply hrep.hom_ext
  rw [Category.assoc, ← h, commutativeSubgroupIntersectionRepresentativeIso_hom_comp]
  exact commutativeSubgroupIntersection_condition f r

/-- The inverse comparison retains the first specified projection. -/
@[reassoc]
theorem commutativeSubgroupIntersectionRepresentativeIso_inv_fst :
    (commutativeSubgroupIntersectionRepresentativeIso f r sT hf hr hsT hRange).inv ≫
      commutativeSubgroupIntersectionFst f r = sT := by
  rw [← commutativeSubgroupIntersectionRepresentativeIso_hom_fst
    f r sT hf hr hsT hRange, Iso.inv_hom_id_assoc]

/-- The inverse comparison retains the second specified projection. -/
@[reassoc]
theorem commutativeSubgroupIntersectionRepresentativeIso_inv_snd
    (sR : S.toGrp ⟶ R) (h : sT ≫ f = sR ≫ r) :
    (commutativeSubgroupIntersectionRepresentativeIso f r sT hf hr hsT hRange).inv ≫
      commutativeSubgroupIntersectionSnd f r = sR := by
  rw [← commutativeSubgroupIntersectionRepresentativeIso_hom_snd
    f r sT hf hr hsT hRange sR h, Iso.inv_hom_id_assoc]

/-- The inverse comparison is the canonical lift of the supplied compatible pair. -/
theorem commutativeSubgroupIntersectionRepresentativeIso_inv_eq_lift
    (sR : S.toGrp ⟶ R) (h : sT ≫ f = sR ≫ r) :
    (commutativeSubgroupIntersectionRepresentativeIso f r sT hf hr hsT hRange).inv =
      commutativeSubgroupIntersectionLift f r sT sR h := by
  apply commutativeSubgroupIntersection_hom_ext f r
  · rw [commutativeSubgroupIntersectionRepresentativeIso_inv_fst,
      commutativeSubgroupIntersectionLift_fst]
  · rw [commutativeSubgroupIntersectionRepresentativeIso_inv_snd
      f r sT hf hr hsT hRange sR h, commutativeSubgroupIntersectionLift_snd]

end Base

section Field

variable {k : Type u} [Field k]
variable {P R : GroupScheme (Spec (CommRingCat.of k))}
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}
variable (f : T.toGrp ⟶ P) (r : R ⟶ P) [Mono r.hom.hom]

/-- A radical maximal torus representing the entire intersection makes the
canonical intersection projection a maximal torus of the same radical. -/
theorem isMaximalTorus_commutativeSubgroupIntersectionSnd_of_representative
    (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ R)
    (hf : IsClosedSubgroup f) (hr : IsClosedSubgroup r)
    (hsT : IsClosedSubgroup sT) (hsR : IsMaximalTorus sR)
    (h : sT ≫ f = sR ≫ r)
    (hRange : SubgroupFunctor.range (sT ≫ f) =
      SubgroupFunctor.range f ⊓ SubgroupFunctor.range r) :
    IsMaximalTorus (commutativeSubgroupIntersectionSnd f r) := by
  have hi := hsR.iso_comp
    (T := S) (T' := commutativeSubgroupIntersection f r)
    (commutativeSubgroupIntersectionRepresentativeIso f r sT hf hr hsT hRange)
  rwa [commutativeSubgroupIntersectionRepresentativeIso_hom_snd
    f r sT hf hr hsT hRange sR h] at hi

variable {K : Type u} [Field K] [Algebra k K]

local notation "bc" => GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))
local notation "cbc" => CommGroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- It suffices to supply any full intersection representative over an extension
field whose map to the second factor is a maximal torus. -/
theorem isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange_representative
    {S' : CommGroupScheme (Spec (CommRingCat.of K))}
    (sT : S'.toGrp ⟶ ((cbc).obj T).toGrp) (sR : S'.toGrp ⟶ (bc).obj R)
    (hf : IsClosedSubgroup f) (hr : IsClosedSubgroup r)
    (hsT : IsClosedSubgroup sT) (hsR : IsMaximalTorus sR)
    (h : sT ≫ (bc).map f = sR ≫ (bc).map r)
    (hRange : SubgroupFunctor.range (sT ≫ (bc).map f) =
      SubgroupFunctor.range ((bc).map f) ⊓ SubgroupFunctor.range ((bc).map r)) :
    IsMaximalTorus (commutativeSubgroupIntersectionSnd f r) := by
  apply isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange
    (K := K) f r hf
  exact isMaximalTorus_commutativeSubgroupIntersectionSnd_of_representative
    (T := (cbc).obj T) ((bc).map f) ((bc).map r) sT sR
    (hf.baseChange _) (hr.baseChange _) hsT hsR h hRange

end Field

end Langlands.GroupScheme
