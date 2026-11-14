import Langlands.GroupScheme.CentralIsogeny.ProductIntersectionRestriction
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison

/-! # Inverse parabolic construction in a central product over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Transport

variable {S : Scheme.{u}} {Z D G P P' : GroupScheme S}

/-- Precomposing a commuting product with a map on its second factor
composes the second factor map. -/
private theorem whiskerLeft_prodHom {B B' : GroupScheme S}
    (z : Z ⟶ G) (hz : IsCentral z) (j : B ⟶ G) (f : B' ⟶ B) :
    (Z ◁ f) ≫ prodHom z j (hz.commute_values _) =
      prodHom z (f ≫ j) (hz.commute_values _) := by
  apply hom_ext_points
  intro U p
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom, comp_prodHom]
  have hfst : (Z ◁ f).hom.hom ≫ fst Z.X B.X = fst Z.X B'.X :=
    congrArg (fun g : Z ⊗ B' ⟶ Z => g.hom.hom) (whiskerLeft_fst Z f)
  have hsnd : (Z ◁ f).hom.hom ≫ snd Z.X B.X = snd Z.X B'.X ≫ f.hom.hom :=
    congrArg (fun g : Z ⊗ B' ⟶ B => g.hom.hom) (whiskerLeft_snd Z f)
  simp only [productPointsEquiv_fst, productPointsEquiv_snd, Category.assoc,
    hfst, hsnd, Grp.comp_hom_hom]

/-- Transport a restricted central product along an isomorphism with the
actual intersection, compatible with the factor embeddings. -/
private theorem exists_centralIsogeny_of_intersection_iso
    (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) [Mono i.hom.hom]
    (hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i)
    (i' : P' ⟶ D) (a : P' ≅ subgroupIntersection d i)
    (ha : a.hom ≫ subgroupIntersectionFst d i = i') :
    ∃ e : Z ⊗ P' ⟶ P, IsCentralIsogeny e ∧
      e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _) := by
  let b : Z ⊗ P' ≅ Z ⊗ subgroupIntersection d i := (tensorLeft Z).mapIso a
  refine ⟨b.hom ≫ centralProductIntersectionFactor z hz d i hzi,
    (isCentralIsogeny_centralProductIntersectionFactor z hz d hprod i hzi).iso_comp b, ?_⟩
  rw [Category.assoc, centralProductIntersectionFactor_comp]
  change (Z ◁ a.hom) ≫ prodHom z (subgroupIntersectionHom d i) _ = _
  rw [whiskerLeft_prodHom z hz]
  have ha' : a.hom ≫ subgroupIntersectionHom d i = i' ≫ d :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ d) ha)
  rw [ha']

/-- Transport a restricted central product from the actual intersection to
any monic presentation with the same all-test range. -/
theorem exists_centralIsogeny_of_intersection_range_eq
    (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) [Mono i.hom.hom]
    (hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i)
    (i' : P' ⟶ D) [Mono i'.hom.hom]
    (h : SubgroupFunctor.range (subgroupIntersectionFst d i) = SubgroupFunctor.range i') :
    ∃ e : Z ⊗ P' ⟶ P, IsCentralIsogeny e ∧
      e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _) := by
  have hpb := subgroupIntersection_isPullback d i
  have : Mono (subgroupIntersectionFst d i).hom.hom := hpb.mono_fst_of_mono
  let hI : (SubgroupFunctor.range i').IsRepresentedBy (subgroupIntersectionFst d i) :=
    ⟨inferInstance, h⟩
  let hP' : (SubgroupFunctor.range i').IsRepresentedBy i' := ⟨inferInstance, rfl⟩
  exact exists_centralIsogeny_of_intersection_iso z hz d hprod i hzi i'
    (hP'.isoOfIsRepresentedBy hI) (hP'.isoOfIsRepresentedBy_hom_comp hI)

end Transport

namespace CentralProductParabolic

variable {k : Type u} [Field k]
    {Z D G P' : GroupScheme (Spec (CommRingCat.of k))}

/-- Extend a parabolic of the closed factor by its field cocharacter. -/
def extensionCocharacter (hD : IsConnectedReductive D) (i' : P' ⟶ D)
    (hi' : IsParabolicSubgroup i') :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D :=
  Classical.choose
    (ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup hD i' hi')

/-- The chosen cocharacter presents the original parabolic on every test scheme. -/
theorem range_extensionCocharacter (hD : IsConnectedReductive D) (i' : P' ⟶ D)
    (hi' : IsParabolicSubgroup i') :
    SubgroupFunctor.range i' = Dynamic.parabolic (extensionCocharacter hD i' hi') :=
  Classical.choose_spec
    (ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup hD i' hi')

/-- Every parabolic of the connected reductive closed factor of a central
product is the actual intersection with an ambient parabolic, and central
multiplication induces a central isogeny onto that ambient parabolic. -/
theorem exists_inverse
    (hG : IsConnectedReductive G) (hD : IsConnectedReductive D)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i' : P' ⟶ D) (hi' : IsParabolicSubgroup i') :
    ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G) (e : Z ⊗ P' ⟶ P),
      IsParabolicSubgroup i ∧ IsCentralIsogeny e ∧
      e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _) ∧
      SubgroupFunctor.range (subgroupIntersectionFst d i) = SubgroupFunctor.range i' := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := extensionCocharacter hD i' hi'
  let i := Dynamic.Affine.parabolicHom (χ ≫ d)
  have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom (χ ≫ d)
  have hi : IsParabolicSubgroup i :=
    (parabolicDynamic k G hG _ i
      (Dynamic.Affine.isClosedSubgroup_parabolicHom (χ ≫ d))).mpr ⟨χ ≫ d, hrep.2⟩
  have hzi : SubgroupFunctor.range z ≤ SubgroupFunctor.range i := by
    rw [hrep.2]
    exact ((isCentral_iff_range_le_center z).mp hz).trans
      ((center_le_dynamicCentralizer (χ ≫ d)).trans (Dynamic.centralizer_le_parabolic _))
  have hinter : SubgroupFunctor.range (subgroupIntersectionFst d i) =
      SubgroupFunctor.range i' := by
    rw [range_subgroupIntersectionFst_eq_comap, hrep.2,
      ← Dynamic.parabolic_eq_comap_of_isClosedSubgroup χ d hd]
    exact (range_extensionCocharacter hD i' hi').symm
  have : IsClosedImmersion i'.hom.hom.left := hi'.isClosedSubgroup
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  have : Mono i.hom.hom := hrep.1
  obtain ⟨e, he, heq⟩ :=
    exists_centralIsogeny_of_intersection_range_eq z hz d hprod i hzi i' hinter
  exact ⟨_, i, e, hi, he, heq, hinter⟩

end CentralProductParabolic

end Langlands.GroupScheme
