import Langlands.GroupScheme.Rational.LeviCentralizerExtension
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.Characters

/-! # Ambient maximality from compatible Levi centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P L M : GroupScheme (Spec (CommRingCat.of k))}
  {A B : CommGroupScheme (Spec (CommRingCat.of k))}
  {j : P ⟶ G} {l : L ⟶ P} {m : M ⟶ P}
  {a : A.toGrp ⟶ L} {b : B.toGrp ⟶ G}

namespace IsRationalLeviSubgroup

/-- A split component whose ambient centralizer is the original Levi is
ambient maximal if one ambient maximal split extension has a centralizer
which is a rational Levi of the same group. -/
theorem isMaximalSplitTorus_of_splitComponent_extension
    (hl : IsRationalLeviSubgroup l) (hm : IsRationalLeviSubgroup m)
    (hj : IsClosedSubgroup j) (hA : IsSplitComponent a)
    (ha : (torusCentralizer (a ≫ l ≫ j)).IsRepresentedBy (l ≫ j))
    (hb : IsMaximalSplitTorus b)
    (hZb : (torusCentralizer b).IsRepresentedBy (m ≫ j))
    (f : A.toGrp ⟶ B.toGrp) (hf : f ≫ b = a ≫ l ≫ j) :
    IsMaximalSplitTorus (a ≫ l ≫ j) := by
  let bL := hl.centralizerExtensionFactor hm hj ha hZb f hf
  have hbL : bL ≫ (l ≫ j) = b :=
    hl.centralizerExtensionFactor_comp hm hj ha hZb f hf
  have hfL : f ≫ bL = a := by
    apply ha.hom_ext
    rw [Category.assoc, hbL, hf]
  have : IsIso f := hA.2 B bL
    (hl.isCentralSplitTorus_centralizerExtensionFactor hm hj ha hZb f hf hb.1) f hfL
  apply hb.of_factor (hA.1.1.comp (hl.isClosedSubgroup.comp hj)) (inv f)
  rw [← hf, IsIso.inv_hom_id_assoc]

/-- For an affine group locally of finite type, it suffices that each ambient
maximal split extension has a centralizer realized as a rational Levi of the
same group. This is a criterion; it does not construct those Levi realizations. -/
theorem isMaximalSplitTorus_of_splitComponent_centralizers
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hl : IsRationalLeviSubgroup l) (hj : IsClosedSubgroup j)
    (hA : IsSplitComponent a)
    (ha : (torusCentralizer (a ≫ l ≫ j)).IsRepresentedBy (l ≫ j))
    (hcompat : ∀ (B : CommGroupScheme (Spec (CommRingCat.of k)))
      (b : B.toGrp ⟶ G), IsMaximalSplitTorus b →
        ∀ f : A.toGrp ⟶ B.toGrp, f ≫ b = a ≫ l ≫ j →
          ∃ (M : GroupScheme (Spec (CommRingCat.of k))) (m : M ⟶ P),
            IsRationalLeviSubgroup m ∧
              (torusCentralizer b).IsRepresentedBy (m ≫ j)) :
    IsMaximalSplitTorus (a ≫ l ≫ j) := by
  obtain ⟨B, b, hb, f, hf⟩ := exists_maximalSplitTorus_extension G (a ≫ l ≫ j)
    (hA.1.1.comp (hl.isClosedSubgroup.comp hj))
  obtain ⟨M, m, hm, hZb⟩ := hcompat B b hb f hf
  exact hl.isMaximalSplitTorus_of_splitComponent_extension hm hj hA ha hb hZb f hf

variable {R : GroupScheme (Spec (CommRingCat.of k))} {r : R ⟶ P}

/-- The actual factor of the original split component through a specified
solvable radical, with its original ambient composite, ambient maximality and
whole-torus centralizer. The compatible-extension Levi premise is explicit. -/
def splitComponentRadicalWitness
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hl : IsRationalLeviSubgroup l) (hj : IsClosedSubgroup j)
    (hR : IsSolvableRadical r) (hA : IsSplitComponent a)
    (ha : (torusCentralizer (a ≫ l ≫ j)).IsRepresentedBy (l ≫ j))
    (hcompat : ∀ (B : CommGroupScheme (Spec (CommRingCat.of k)))
      (b : B.toGrp ⟶ G), IsMaximalSplitTorus b →
        ∀ f : A.toGrp ⟶ B.toGrp, f ≫ b = a ≫ l ≫ j →
          ∃ (M : GroupScheme (Spec (CommRingCat.of k))) (m : M ⟶ P),
            IsRationalLeviSubgroup m ∧
              (torusCentralizer b).IsRepresentedBy (m ≫ j)) :
    {aR : A.toGrp ⟶ R // aR ≫ r = a ≫ l ∧
      IsMaximalSplitTorus (aR ≫ r ≫ j) ∧
        torusCentralizer (aR ≫ r ≫ j) = SubgroupFunctor.range (l ≫ j)} := by
  let aR := hl.centralTorusRadicalFactor a hR hA.1.1.1.isTorus hA.1.1.2 hA.1.2
  have hfac : aR ≫ r = a ≫ l :=
    hl.centralTorusRadicalFactor_comp a hR hA.1.1.1.isTorus hA.1.1.2 hA.1.2
  have hamb : aR ≫ r ≫ j = a ≫ l ≫ j := by
    rw [← Category.assoc, hfac, Category.assoc]
  refine ⟨aR, hfac, ?_, ?_⟩
  · rw [hamb]
    exact hl.isMaximalSplitTorus_of_splitComponent_centralizers hj hA ha hcompat
  · rw [hamb]
    exact ha.2.symm

end IsRationalLeviSubgroup

end Langlands.GroupScheme
