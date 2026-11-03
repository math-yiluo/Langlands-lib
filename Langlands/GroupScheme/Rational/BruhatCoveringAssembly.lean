import Langlands.GroupScheme.Rational.BruhatCoveringReduction
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.ParabolicTorusStatement
import Langlands.GroupScheme.Rational.MinimalParabolicContainment
import Langlands.GroupScheme.Rational.Statement

/-! # Rational Bruhat covering from common tori in minimal parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Scheme

variable {S : Scheme.{u}} {G P : GroupScheme S}
  {T T' : CommGroupScheme S}


/-- A rational Bruhat factorization carries the actual normalizing point and
the two factors in the specified subgroup functor. -/
structure RationalBruhatFactorization (i : T.toGrp ⟶ G) (F : SubgroupFunctor G)
    (g : Over.mk (𝟙 S) ⟶ G.X) where
  normalizer : normalizerPoints i
  leftFactor : F.carrier (Over.mk (𝟙 S))
  rightFactor : F.carrier (Over.mk (𝟙 S))
  eq_mul : g = leftFactor.val * normalizer.val * rightFactor.val

/-- A conjugacy inside a subgroup induces the corresponding ambient conjugacy. -/
theorem conjugacy_eq_of_subgroup_factor
    (j : P ⟶ G) (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)
    (f : T.toGrp ⟶ P) (f' : T'.toGrp ⟶ P)
    (hf : f ≫ j = i) (hf' : f' ≫ j = i')
    (p : Over.mk (𝟙 S) ⟶ P.X) (e : T.toGrp ≅ T'.toGrp)
    (he : f ≫ (P.innerIso p).hom = e.hom ≫ f') :
    i ≫ (G.innerIso (p ≫ j.hom.hom)).hom = e.hom ≫ i' := by
  calc
    _ = (f ≫ j) ≫ (G.innerIso (p ≫ j.hom.hom)).hom := by rw [hf]
    _ = (f ≫ (P.innerIso p).hom) ≫ j := by
      simp only [Category.assoc, innerIso_hom_comp]
    _ = (e.hom ≫ f') ≫ j := by rw [he]
    _ = e.hom ≫ i' := by rw [Category.assoc, hf']

end Scheme

/-- Common maximal split tori and conjugacy inside minimal parabolics imply
rational Bruhat covering for an actual minimal parabolic containing the torus. -/
theorem rationalBruhatCovering_of_commonTorus
    (hCommon : ParabolicIntersectionCentralizerStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)
    (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G)
    (hj : IsMinimalParabolicSubgroup j) (f : T.toGrp ⟶ P) (hf : f ≫ j = i) :
    ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ n ∈ normalizerPoints i,
        ∃ p ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)),
        ∃ q ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)),
          g = p * n * q := by
  intro g
  let eg := G.innerIso g
  let jg := j ≫ eg.hom
  have hjg : IsMinimalParabolicSubgroup jg := hj.comp_iso eg
  obtain ⟨T', i', hi', hZ, hZg⟩ := hCommon k G hG P P j jg hj.1 hjg.1
  have := hj.1.isClosedSubgroup.mono
  have := hjg.1.isClosedSubgroup.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono jg.hom.hom := Over.mono_of_mono_left _
  let hrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  let hrepg : (SubgroupFunctor.range jg).IsRepresentedBy jg := ⟨inferInstance, rfl⟩
  let f' := hrep.factorHom i' ((range_le_torusCentralizer i').trans hZ)
  have hf' : f' ≫ j = i' := hrep.factorHom_comp _ _
  let f'g := hrepg.factorHom i' ((range_le_torusCentralizer i').trans hZg)
  have hf'g : f'g ≫ jg = i' := hrepg.factorHom_comp _ _
  obtain ⟨p, e, hp⟩ := hInside k G hG P j hj T T' i i' hi hi' f f' hf hf'
  have hfg : f ≫ jg = i ≫ eg.hom := by
    dsimp only [jg]
    rw [← Category.assoc, hf]
  obtain ⟨q, e', hq⟩ := hInside k G hG P jg hjg T T' (i ≫ eg.hom) i'
    (hi.comp_iso eg) hi' f f'g hfg hf'g
  have hpG := conjugacy_eq_of_subgroup_factor j i i' f f' hf hf' p e hp
  have hqbase := conjugacy_eq_of_subgroup_factor j i (f'g ≫ j) f f'g hf rfl q e' hq
  have hqG : i ≫ (G.innerIso (q ≫ j.hom.hom)).hom ≫ (G.innerIso g).hom =
      e'.hom ≫ i' := by
    calc
      _ = (i ≫ (G.innerIso (q ≫ j.hom.hom)).hom) ≫ eg.hom :=
        (Category.assoc _ _ _).symm
      _ = (e'.hom ≫ f'g ≫ j) ≫ eg.hom := by rw [hqbase]
      _ = e'.hom ≫ i' := by
        simpa only [jg, Category.assoc] using congrArg (fun a => e'.hom ≫ a) hf'g
  let n := normalizerPointOfConjugacySquare i i' g
    (p ≫ j.hom.hom) (q ≫ j.hom.hom) e e' hpG hqG
  refine ⟨n.val, n.property, p ≫ j.hom.hom, ⟨p, rfl⟩,
    (q ≫ j.hom.hom)⁻¹, ?_, ?_⟩
  · exact ((SubgroupFunctor.range j).carrier _).inv_mem ⟨q, rfl⟩
  · change g = (p ≫ j.hom.hom) *
      ((p ≫ j.hom.hom)⁻¹ * g * (q ≫ j.hom.hom)) * (q ≫ j.hom.hom)⁻¹
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

/-- Generic minimality, common tori, and inside-parabolic conjugacy give the
covering half of the published rational Bruhat decomposition. -/
theorem rationalBruhatCovering_of_structural
    (hMinimal : GenericMinimalParabolicStatement.{u})
    (hCommon : ParabolicIntersectionCentralizerStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        ∃ n ∈ normalizerPoints i,
          ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
          ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
            g = p * n * q := by
  have := hG.isAffineHom
  intro hν
  obtain ⟨P, j, hj, heq⟩ :=
    isMinimalParabolicFunctor_iff_exists.mp (hMinimal k G hG T i hi ν hν)
  have := hj.1.isClosedSubgroup.mono
  have hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, heq⟩
  have hcover := rationalBruhatCovering_of_commonTorus hCommon hInside k G hG T i hi P j hj
    (Dynamic.parabolicTorusFactor i (CommGroupScheme.groupHom ν) hrep)
    (Dynamic.parabolicTorusFactor_comp i (CommGroupScheme.groupHom ν) hrep)
  simpa only [heq] using hcover


/-- Choose actual normalizer and dynamic-parabolic factors from the three
explicit structural premises. -/
def rationalBruhatFactorizationOfStructural
    (hMinimal : GenericMinimalParabolicStatement.{u})
    (hCommon : ParabolicIntersectionCentralizerStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        RationalBruhatFactorization i (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) g := by
  have := hG.isAffineHom
  intro hν g
  apply Classical.choice
  obtain ⟨n, hn, p, hp, q, hq, heq⟩ :=
    rationalBruhatCovering_of_structural hMinimal hCommon hInside k G hG T i hi ν hν g
  exact ⟨⟨⟨n, hn⟩, ⟨p, hp⟩, ⟨q, hq⟩, heq⟩⟩

end Langlands.GroupScheme
