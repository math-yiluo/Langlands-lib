import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.DynamicRadicalRootGeneration

/-! # Parabolic-radical images in normal subgroups containing relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G)

/-- Conjugating an arbitrary cocharacter into the given maximal split torus
puts its entire dynamic radical in every normal subgroup containing the
actual root groups, with the structural inputs explicit. -/
theorem dynamicUnipotent_le_normalSubgroup_of_root_groups
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [hK : K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (ζ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Dynamic.unipotent ζ).carrier (Over.mk (𝟙 _)) ≤ K := by
  let := hG.smooth
  let := hG.connectedSpace
  obtain ⟨g, ν, hg⟩ := exists_innerIso_comp_eq_cocharacter hconj hi ζ
  have hν := dynamicUnipotent_le_of_disjoint_positive_rays hG hi ν
    (hdisj ν) K (fun α => hroot α α.property)
  intro x hx
  have hc := (Dynamic.mem_unipotent_conj ζ g).mp hx
  rw [hg] at hc
  simp only [constantPoint_self] at hc
  have hk := hν hc
  simpa [mul_assoc] using hK.conj_mem _ hk g⁻¹

/-- Functoriality carries a source dynamic radical into the corresponding
ambient one; the homomorphism need not be injective or normal. -/
theorem map_dynamicUnipotent_le_normalSubgroup_of_root_groups
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (f : H ⟶ G) (ζ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H) :
    ((Dynamic.unipotent ζ).carrier (Over.mk (𝟙 _))).map (rationalPoints.map f) ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  exact dynamicUnipotent_le_normalSubgroup_of_root_groups i hconj hG hi
    hdisj K hroot (ζ ≫ f) (Dynamic.unipotent_le_comap ζ f _ hx)

/-- Every actual parabolic-radical image of a connected reductive source
lies in a normal subgroup containing all ambient root groups. Parabolic
cocharacter presentation, centralizer reductivity and split-torus conjugacy
remain explicit structural inputs. -/
theorem parabolicRadical_range_le_normalSubgroup_of_root_groups
    (hPD : ParabolicDynamicStatement.{u})
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (hH : IsConnectedReductive H) (f : H ⟶ G)
    {P U : GroupScheme (Spec (CommRingCat.of k))} {p : P ⟶ H} {r : U ⟶ P}
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    (rationalPoints.map (r ≫ p ≫ f)).range ≤ K := by
  let := hH.isAffineHom
  let := hH.smooth
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨ζ, hζ⟩ := (hPD k H hH P p hp.isClosedSubgroup).mp hp
  let := hp.isClosedSubgroup.mono
  have hP : (Dynamic.parabolic ζ).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, hζ⟩
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom ζ
  have hred := hDCR k H hH ζ _ (Dynamic.Affine.centralizerHom ζ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom ζ) hZ
  have heq := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
    ζ hP hZ hred hr
  have hmap := map_dynamicUnipotent_le_normalSubgroup_of_root_groups
    i hconj hG hi hdisj K hroot f ζ
  rintro _ ⟨x, rfl⟩
  have hx : rationalPoints.map (r ≫ p) x ∈
      (Dynamic.unipotent ζ).carrier (Over.mk (𝟙 _)) := by
    rw [← heq]
    exact ⟨x, rfl⟩
  apply hmap
  refine ⟨rationalPoints.map (r ≫ p) x, hx, ?_⟩
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

/-- The actual radical-point homomorphism with codomain restricted to a
normal subgroup containing all ambient relative-root groups. -/
def parabolicRadicalPointsToNormalSubgroup
    (hPD : ParabolicDynamicStatement.{u})
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (hH : IsConnectedReductive H) (f : H ⟶ G)
    {P U : GroupScheme (Spec (CommRingCat.of k))} {p : P ⟶ H} {r : U ⟶ P}
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    rationalPoints U →* K :=
  (rationalPoints.map (r ≫ p ≫ f)).codRestrict K fun x =>
    parabolicRadical_range_le_normalSubgroup_of_root_groups
      i hPD hDCR hconj hG hi hdisj K hroot hH f hp hr ⟨x, rfl⟩

end Langlands.GroupScheme
