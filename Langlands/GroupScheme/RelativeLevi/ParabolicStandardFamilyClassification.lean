import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Unique conjugacy indices for a supplied complete standard family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

namespace Langlands.GroupScheme

/-- A represented family indexed exactly by the simple-root subsets classifies
all rational parabolics, with equality of subgroup functors on every test. -/
theorem existsUnique_conjugate_standardFamily
    {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {A : Type v}
    (e : A ≃ {B : Set (characterLattice T) // B ⊆ simpleRelativeRoots i ν})
    (ζ : A → cocharacterLattice T)
    (hζ : ∀ a, IsStandardCocharacter i ν (e a).1 (ζ a))
    (P : A → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ a, P a ⟶ G)
    (hj : ∀ a, SubgroupFunctor.range (j a) =
      Dynamic.parabolic (CommGroupScheme.groupHom (ζ a) ≫ i))
    (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G)
    (hq : IsParabolicSubgroup q) :
    ∃! a : A, ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      SubgroupFunctor.range (q ≫ (G.innerIso g).hom) = SubgroupFunctor.range (j a) := by
  classical
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG Q q hq.isClosedSubgroup).mp hq
  have hstandard (a : A) : SubgroupFunctor.range (j a) =
      standardParabolic i ν (e a).1 :=
    (hj a).trans ((standardCocharacter k G hG T i hi ν hν (e a).1 (e a).2).2
      (ζ a) (hζ a)).1.symm
  have heq (a : A) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
      SubgroupFunctor.range (q ≫ (G.innerIso g).hom) = SubgroupFunctor.range (j a) ↔
      Dynamic.parabolic χ = (standardParabolic i ν (e a).1).comap
        (G.innerIso g).hom := by
    rw [SubgroupFunctor.range_comp_iso, hχ, hstandard]
    exact (SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).symm
  obtain ⟨B, hB, huniq⟩ := (standardParabolicClassification k G hG T i hi ν hν).2 χ
  refine ⟨e.symm B, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hB
    refine ⟨g, (heq _ g).mpr ?_⟩
    simpa only [e.apply_symm_apply] using hg
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    apply huniq
    obtain ⟨g, hg⟩ := ha
    exact ⟨g, (heq a g).mp hg⟩

section ChosenIndex

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
  (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
  {A : Type v}
  (e : A ≃ {B : Set (characterLattice T) // B ⊆ simpleRelativeRoots i ν})
  (ζ : A → cocharacterLattice T)
  (hζ : ∀ a, IsStandardCocharacter i ν (e a).1 (ζ a))
  (P : A → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ a, P a ⟶ G)
  (hj : ∀ a, SubgroupFunctor.range (j a) =
    Dynamic.parabolic (CommGroupScheme.groupHom (ζ a) ≫ i))
  (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G)
  (hq : IsParabolicSubgroup q)

/-- The unique standard-family index of a rational parabolic conjugacy class. -/
def standardFamilyConjugacyIndex : A :=
  Classical.choose
    (existsUnique_conjugate_standardFamily G hG T i hi ν hν e ζ hζ P j hj Q q hq)

/-- The selected index has the required all-test conjugacy property. -/
theorem standardFamilyConjugacyIndex_spec :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      SubgroupFunctor.range (q ≫ (G.innerIso g).hom) = SubgroupFunctor.range
        (j (standardFamilyConjugacyIndex G hG T i hi ν hν e ζ hζ P j hj Q q hq)) :=
  (Classical.choose_spec
    (existsUnique_conjugate_standardFamily G hG T i hi ν hν e ζ hζ P j hj Q q hq)).1

/-- Every index with the conjugacy property equals the selected index. -/
theorem standardFamilyConjugacyIndex_unique (a : A)
    (ha : ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      SubgroupFunctor.range (q ≫ (G.innerIso g).hom) = SubgroupFunctor.range (j a)) :
    a = standardFamilyConjugacyIndex G hG T i hi ν hν e ζ hζ P j hj Q q hq :=
  (Classical.choose_spec
    (existsUnique_conjugate_standardFamily G hG T i hi ν hν e ζ hζ P j hj Q q hq)).2 a ha

end ChosenIndex

end Langlands.GroupScheme
