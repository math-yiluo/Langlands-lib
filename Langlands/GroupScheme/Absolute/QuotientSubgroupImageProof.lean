import Langlands.GroupScheme.Absolute.QuotientSubgroupImageStatement
import Langlands.GroupScheme.Rational.QuotientParabolicImageProof
import Langlands.GroupScheme.Absolute.QuotientMaximalUnipotent
import Langlands.GroupScheme.Absolute.QuotientTorusImageAmbient
import Langlands.GroupScheme.Absolute.QuotientSubgroupRealization
import Langlands.GroupScheme.Absolute.QuotientParabolicRealization

/-! # Assembly of the algebraically closed quotient subgroup image theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The arbitrary-field parabolic/Borel image statement supplies the remaining
input to all eight algebraically closed image and realization clauses. -/
theorem algClosedQuotientSubgroupImage_of_quotientParabolicImage
    (himage : QuotientParabolicImageStatement.{u}) :
    AlgClosedQuotientSubgroupImageStatement.{u} := by
  intro k _ _ G Q _ _ _ _ _ _ q hflat hsurj
  have hborel :
      ∀ (B C : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (c : C ⟶ Q) (p : B ⟶ C),
        IsClosedSubgroup c → Smooth C.X.hom → Surjective p.hom.hom.left →
          b ≫ q = p ≫ c → IsBorelSubgroup b → IsBorelSubgroup c := by
    intro B C b c p hc hCsm hp hcomm hb
    have : IsIso (toAlgebraicClosure k) :=
      isIso_SpecMap_iff.mpr IsAlgClosed.algebraMap_bijective_of_isIntegral
    exact ((himage k G Q q hflat hsurj B C b c p hc hCsm hp hcomm).2
      ⟨hb, hb.baseChange_of_isIso (toAlgebraicClosure k)⟩).isBorelSubgroup
  have hbimages :
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G), IsBorelSubgroup b →
        ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ Q) (p : B ⟶ C),
          IsBorelSubgroup c ∧ Surjective p.hom.hom.left ∧ b ≫ q = p ≫ c := by
    intro B b hb
    have : Smooth B.X.hom := hb.smooth
    have : ConnectedSpace B.X.left := hb.connectedSpace
    have : IsAffineHom B.X.hom := hb.isClosedSubgroup.isAffineHom
    obtain ⟨C, c, p, hc, hpc, _, hp, _, _, hCsm, _, _⟩ := HomImage.exists_image (b ≫ q)
    exact ⟨C, c, p, hborel B C b c p hc hCsm hp hpc.symm hb, hp, hpc.symm⟩
  have huimages : PreservesMaximalUnipotentSubgroups q :=
    QuotientMaximalUnipotent.preservesMaximalUnipotentSubgroups_of_borel_images q hbimages
  have htimages :
      ∀ (T S : CommGroupScheme (Spec (CommRingCat.of k)))
        (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ Q) (f : T.toGrp ⟶ S.toGrp),
        IsClosedSubgroup s → Smooth S.X.hom → Surjective f.hom.hom.left →
          t ≫ q = f ≫ s → IsMaximalTorus t → IsMaximalTorus s := by
    intro T S t s f hs hSsm hf hcomm ht
    exact QuotientTorusImage.isMaximalTorus_image_of_borel_images q hbimages
      t s f hs hSsm hf hcomm ht
  have hblift :
      ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ Q), IsBorelSubgroup c →
        ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (p : B ⟶ C),
          IsBorelSubgroup b ∧ Surjective p.hom.hom.left ∧ b ≫ q = p ≫ c := by
    intro C c hc
    exact QuotientSubgroupRealization.exists_borel_image_of_borel_images q hsurj hbimages c hc
  refine ⟨?_, ?_, ?_, hblift, ?_, ?_⟩
  · intro H H' i j f hj hH'sm hf hcomm
    exact ⟨(himage k G Q q hflat hsurj H H' i j f hj hH'sm hf hcomm).1,
      hborel H H' i j f hj hH'sm hf hcomm,
      huimages H H' i j f hj hH'sm hf hcomm⟩
  · intro T S i j f hj hSsm hf hcomm hi
    exact htimages T S i j (CommGroupScheme.groupHom f) hj hSsm hf hcomm hi
  · intro H' j hj
    exact QuotientSubgroupRealization.exists_parabolic_image_of_borel_realization
      q hsurj hblift j hj
  · intro H' j hj
    exact QuotientMaximalUnipotent.exists_maximalUnipotent_image_of_images
      q hsurj huimages j hj
  · intro S j hj
    exact QuotientSubgroupRealization.exists_maximalTorus_image_of_maximalTorus_images
      q hsurj htimages j hj

/-- Milne, Proposition 17.20: quotient maps over algebraically closed fields preserve
parabolic, Borel, maximal smooth connected unipotent and maximal torus subgroups,
and every such target subgroup is an image of one of the same kind. -/
theorem algClosedQuotientSubgroupImage : AlgClosedQuotientSubgroupImageStatement.{u} :=
  algClosedQuotientSubgroupImage_of_quotientParabolicImage quotientParabolicImage

end Langlands.GroupScheme
