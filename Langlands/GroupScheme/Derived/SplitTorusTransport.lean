import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Transport of derived-torus witnesses between actual derived-subgroup inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace IsDerivedSubgroup

section Comparison

variable {B : Scheme.{u}} {G D D' : GroupScheme B} {d : D ⟶ G} {d' : D' ⟶ G}

/-- The canonical isomorphism between two actual representations of the full derived
subgroup. Its composite with the second inclusion is the first inclusion. -/
def iso (hd : IsDerivedSubgroup d) (hd' : IsDerivedSubgroup d') : D ≅ D' :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    hd.isRepresentedBy hd'.isRepresentedBy

@[reassoc]
theorem iso_hom_comp (hd : IsDerivedSubgroup d) (hd' : IsDerivedSubgroup d') :
    (hd.iso hd').hom ≫ d' = d :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    hd.isRepresentedBy hd'.isRepresentedBy

@[reassoc]
theorem iso_inv_comp (hd : IsDerivedSubgroup d) (hd' : IsDerivedSubgroup d') :
    (hd.iso hd').inv ≫ d = d' := by
  calc
    (hd.iso hd').inv ≫ d =
        (hd.iso hd').inv ≫ ((hd.iso hd').hom ≫ d') :=
      congrArg (fun a => (hd.iso hd').inv ≫ a) (hd.iso_hom_comp hd').symm
    _ = d' := Iso.inv_hom_id_assoc _ _

/-- The comparison homomorphism is the unique homomorphism commuting with the
two inclusions into the ambient group. -/
theorem eq_iso_hom (hd : IsDerivedSubgroup d) (hd' : IsDerivedSubgroup d')
    (f : D ⟶ D') (hf : f ≫ d' = d) : f = (hd.iso hd').hom :=
  hd'.isRepresentedBy.hom_ext (hf.trans (hd.iso_hom_comp hd').symm)

end Comparison

section Tori

variable {k : Type u} [Field k]
  {G D D' : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {d' : D' ⟶ G}
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}

/-- A derived-torus witness is independent of the supplied representation of the
full derived subgroup. The ambient torus and its map are unchanged. -/
theorem exists_maximalSplitTorus_factor_iff
    (hd : IsDerivedSubgroup d) (hd' : IsDerivedSubgroup d') :
    (∃ (S_D : CommGroupScheme (Spec (CommRingCat.of k))) (j : S_D.toGrp ⟶ D)
      (e : S_D ⟶ S),
      IsMaximalSplitTorus j ∧
      IsClosedSubgroup (CommGroupScheme.groupHom e) ∧
      j ≫ d = CommGroupScheme.groupHom e ≫ i) ↔
    (∃ (S_D : CommGroupScheme (Spec (CommRingCat.of k))) (j : S_D.toGrp ⟶ D')
      (e : S_D ⟶ S),
      IsMaximalSplitTorus j ∧
      IsClosedSubgroup (CommGroupScheme.groupHom e) ∧
      j ≫ d' = CommGroupScheme.groupHom e ≫ i) := by
  constructor
  · rintro ⟨S_D, j, e, hj, he, hcomm⟩
    refine ⟨S_D, j ≫ (hd.iso hd').hom, e, hj.comp_iso (hd.iso hd'), he, ?_⟩
    rw [Category.assoc, hd.iso_hom_comp hd', hcomm]
  · rintro ⟨S_D, j, e, hj, he, hcomm⟩
    refine ⟨S_D, j ≫ (hd'.iso hd).hom, e, hj.comp_iso (hd'.iso hd), he, ?_⟩
    rw [Category.assoc, hd'.iso_hom_comp hd, hcomm]

end Tori

end IsDerivedSubgroup

end Langlands.GroupScheme
