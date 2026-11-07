import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Split-component factors through an intermediate group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {G P M L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {B A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {b : B.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l b)
  (j : L ⟶ G) (hj : IsClosedSubgroup j)
  (i : M ⟶ L) (hi : i ≫ j = l ≫ p)
  (a : A.toGrp ⟶ L) (ha : IsCentral a)

include pres hj hi ha

/-- A central map into the intermediate group lies in the supplied fine Levi
image, because it centralizes the fine defining cocharacter. -/
theorem range_centralMap_comp_le_levi :
    SubgroupFunctor.range (a ≫ j) ≤ SubgroupFunctor.range (l ≫ p) := by
  rw [pres.levi_eq_splitComponentCocharacter]
  let chiL := CommGroupScheme.groupHom pres.splitComponentCocharacter ≫ b ≫ i
  have hchi : chiL ≫ j =
      CommGroupScheme.groupHom pres.splitComponentCocharacter ≫ b ≫ l ≫ p := by
    simp only [chiL, Category.assoc, hi]
  rintro T _ ⟨x, rfl⟩
  have hz := center_le_dynamicCentralizer chiL T (ha T x)
  have hz' := Dynamic.centralizer_le_comap chiL j T hz
  rw [SubgroupFunctor.mem_comap, hchi] at hz'
  change (x ≫ a.hom.hom) ≫ j.hom.hom ∈ _ at hz'
  change x ≫ (a ≫ j).hom.hom ∈ _
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact hz'

/-- The actual all-test factor of a central map through the original fine Levi. -/
def intermediateCentralFactor : A.toGrp ⟶ M := by
  have hc := pres.isCompatible.levi.isClosedSubgroup.comp
    pres.isCompatible.parabolic.isClosedSubgroup
  let := hc.mono
  exact (show (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p) from
    ⟨Over.mono_of_mono_left _, rfl⟩).factorHom
    (a ≫ j) (pres.range_centralMap_comp_le_levi j hj i hi a ha)

/-- Its composite with the supplied intermediate inclusion is the original map. -/
theorem intermediateCentralFactor_comp :
    pres.intermediateCentralFactor j hj i hi a ha ≫ i = a := by
  let := hj.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono j.hom.hom).mp
  change (pres.intermediateCentralFactor j hj i hi a ha ≫ i ≫ j).hom.hom =
    (a ≫ j).hom.hom
  rw [hi]
  exact congrArg (fun f : A.toGrp ⟶ G => f.hom.hom)
    (SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _)

/-- The lifted map is central in the original fine Levi. -/
theorem isCentral_intermediateCentralFactor :
    IsCentral (pres.intermediateCentralFactor j hj i hi a ha) := by
  have hic : IsClosedSubgroup i := IsClosedSubgroup.of_comp hj (by
    rw [hi]
    exact pres.isCompatible.levi.isClosedSubgroup.comp
      pres.isCompatible.parabolic.isClosedSubgroup)
  let := hic.mono
  have hicm : Mono i.hom.hom := Over.mono_of_mono_left _
  apply IsCentral.of_comp hicm
  rw [pres.intermediateCentralFactor_comp j hj i hi a ha]
  exact ha

variable (hA : IsSplitTorus A.toGrp)

include hA

/-- The central split-torus map factors through the specified fine split
component. Both original ambient and intermediate maps are retained. -/
theorem exists_intermediateSplitComponentFactor :
    ∃ f : A.toGrp ⟶ B.toGrp, f ≫ b ≫ i = a := by
  have : IsAffineHom M.X.hom := pres.isCompatible.levi.isConnectedReductive.isAffineHom
  obtain ⟨f, hf⟩ := pres.isCompatible.splitComponent.exists_factor hA
    (pres.isCentral_intermediateCentralFactor j hj i hi a ha)
  exact ⟨f, by rw [← Category.assoc, hf,
    pres.intermediateCentralFactor_comp j hj i hi a ha]⟩

/-- A chosen actual split-component factor for the supplied nested maps. -/
def intermediateSplitComponentFactor : A ⟶ B :=
  Additive.ofMul (pres.exists_intermediateSplitComponentFactor j hj i hi a ha hA).choose

/-- The chosen factor commutes with the original intermediate map. -/
theorem intermediateSplitComponentFactor_comp :
    CommGroupScheme.groupHom
      (pres.intermediateSplitComponentFactor j hj i hi a ha hA) ≫ b ≫ i = a :=
  (pres.exists_intermediateSplitComponentFactor j hj i hi a ha hA).choose_spec

end Langlands.GroupScheme.ParabolicRootPresentation
