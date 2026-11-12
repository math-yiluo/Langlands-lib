import Langlands.GroupScheme.Rational.DynamicElementarySubgroup
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Parabolic elementary subgroups under homomorphisms of reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {A G : GroupScheme (Spec (CommRingCat.of k))}

/-- The image under an arbitrary homomorphism of the rational points of a
geometric unipotent radical of a parabolic subgroup of a connected reductive
group lies in the parabolic elementary subgroup of a connected reductive
target. -/
theorem rationalPoints_range_radical_le_parabolicElementarySubgroup
    (hA : IsConnectedReductive A) (hG : IsConnectedReductive G) (a : A ⟶ G)
    {P U : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ A) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    (rationalPoints.map (r ≫ p ≫ a)).range ≤ parabolicElementarySubgroup G := by
  have := hA.isAffineHom
  have := hA.smooth
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k A hA P p hp.isClosedSubgroup).mp hp
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have hP : (Dynamic.parabolic χ).IsRepresentedBy p := ⟨Over.mono_of_mono_left _, hχ⟩
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hred := dynamicCentralizerReductive k A hA χ _ _
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ) hZ
  have hrange := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer χ hP hZ hred hr
  rintro _ ⟨x, rfl⟩
  have hx : rationalPoints.map (r ≫ p) x ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hmap := map_dynamicUnipotent_le_parabolicElementarySubgroup hG a χ ⟨_, hx, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using hmap

/-- An arbitrary homomorphism of connected reductive groups maps the parabolic
elementary subgroup of the source into that of the target. -/
theorem parabolicElementarySubgroup_map_le_of_hom
    (hA : IsConnectedReductive A) (hG : IsConnectedReductive G) (a : A ⟶ G) :
    (parabolicElementarySubgroup A).map (rationalPoints.map a) ≤
      parabolicElementarySubgroup G := by
  rw [Subgroup.map_le_iff_le_comap, parabolicElementarySubgroup_le_iff]
  intro P U p r hp hr
  rintro _ ⟨x, rfl⟩
  have h := rationalPoints_range_radical_le_parabolicElementarySubgroup hA hG a p r hp hr
    ⟨x, rfl⟩
  simpa only [Subgroup.mem_comap, rationalPoints.map_apply, Grp.comp_hom_hom,
    Category.assoc] using h

end Langlands.GroupScheme
