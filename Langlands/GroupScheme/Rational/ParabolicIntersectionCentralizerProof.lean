import Langlands.GroupScheme.Rational.ParabolicTorusStatement
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusProof
import Langlands.GroupScheme.Absolute.SplitParabolicCocharacterAbsoluteReduction
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof
import Langlands.GroupScheme.Absolute.FixedTorusGaloisDescent
import Langlands.GroupScheme.Rational.SplitTorusImageDominant
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Common maximal split torus centralizers for two rational parabolics: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A rational parabolic containing a rational maximal torus is the dynamic parabolic of a
cocharacter of that torus defined over the ground field. -/
theorem exists_fixedTorusCocharacter_range_eq_parabolic {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G} (ht : IsMaximalTorus t)
    {j : P ⟶ G} (hj : IsParabolicSubgroup j) (f : T.toGrp ⟶ P) (hf : f ≫ j = t) :
    ∃ mu : cocharacterLattice T,
      SubgroupFunctor.range j = Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ t) := by
  obtain ⟨K, hK, hAlg, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T.toGrp ht.1
  let : Field K := hK
  let : Algebra k K := hAlg
  have : FiniteDimensional k K := hfin
  have : IsGalois k K := hgal
  have : Algebra.IsAlgebraic k K := inferInstance
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion t.hom.hom.left := ht.2.1
  have : IsAffineHom T.X.hom := by
    rw [← Over.w t.hom.hom]
    infer_instance
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hsplitPar : SplitParabolicCocharacterStatement.{u} :=
    splitParabolicCocharacterStatement_of_absoluteBorelOvergroup borelConjugacy
      absoluteBorelOvergroupCocharacter maximalTorusBaseChange
  let bc := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  apply (exists_range_eq_parabolic_iff_finiteGaloisBaseChange k K T t j hsplit).mpr
  exact hsplitPar K (bc.obj G) hG.baseChange_of_algebraicExtension
    ((CommGroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
    (bc.map t) hsplit ((maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht)
    (bc.obj P) (bc.map j) (bc.map f) (parabolicFieldExtensionStatement k K G hG P j hj)
    ((bc.map_comp f j).symm.trans (congrArg bc.map hf))

/-- **Borel–Tits 4.18.** For two rational parabolic subgroups of a connected reductive group
over any field, the whole-torus centralizer of some ambient maximal split torus lies in both
parabolic subgroup functors on every test scheme. -/
theorem parabolicIntersectionCentralizer : ParabolicIntersectionCentralizerStatement.{u} := by
  intro k _ G hG P P' j j' hj hj'
  obtain ⟨T, t, f, f', ht, hf, hf'⟩ := parabolicIntersectionTorus k G hG P P' j j' hj hj'
  obtain ⟨mu, hmu⟩ := exists_fixedTorusCocharacter_range_eq_parabolic hG ht hj f hf
  obtain ⟨mu', hmu'⟩ := exists_fixedTorusCocharacter_range_eq_parabolic hG ht hj' f' hf'
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let S := Spec (CommRingCat.of k)
  let I := ULift.{u} Bool
  let i₁ : I := ULift.up true
  let i₂ : I := ULift.up false
  have hne : i₁ ≠ i₂ := fun h => Bool.noConfusion (congrArg ULift.down h)
  let D := splitTorus.commGroupScheme S I
  let φ : D ⟶ T := splitTorus.proj S I i₁ ≫ mu + splitTorus.proj S I i₂ ≫ mu'
  have hφ₁ : splitTorus.single S I i₁ ≫ φ = mu := by
    classical
    simp only [φ, Preadditive.comp_add, ← Category.assoc, splitTorus.single_comp_proj,
      hne, ite_true, ite_false, Category.id_comp, Limits.zero_comp, add_zero]
  have hφ₂ : splitTorus.single S I i₂ ≫ φ = mu' := by
    classical
    simp only [φ, Preadditive.comp_add, ← Category.assoc, splitTorus.single_comp_proj,
      hne.symm, ite_true, ite_false, Category.id_comp, Limits.zero_comp, zero_add]
  obtain ⟨A, p, a, ha, hpa, -, -⟩ :=
    IsSplitTorus.exists_dominant_factor_isSplitSubtorus (D := D) (isSplitTorus_splitTorus I)
      (CommGroupScheme.groupHom φ ≫ t)
  obtain ⟨M, s, hs, g, hg⟩ := exists_maximalSplitTorus_extension G a ha
  have hfac : ∀ (i : I) (ν : cocharacterLattice T), splitTorus.single S I i ≫ φ = ν →
      CommGroupScheme.groupHom ν ≫ t =
        (CommGroupScheme.groupHom (splitTorus.single S I i) ≫ p ≫ g) ≫ s := by
    intro i ν hν
    have hν' : CommGroupScheme.groupHom (splitTorus.single S I i) ≫
        CommGroupScheme.groupHom φ = CommGroupScheme.groupHom ν :=
      congrArg CommGroupScheme.groupHom hν
    rw [Category.assoc, Category.assoc, hg, hpa, ← Category.assoc, hν']
  refine ⟨M, s, hs, ?_, ?_⟩
  · rw [hmu, hfac i₁ mu hφ₁]
    exact (torusCentralizer_le_dynamicCentralizer s _).trans (Dynamic.centralizer_le_parabolic _)
  · rw [hmu', hfac i₂ mu' hφ₂]
    exact (torusCentralizer_le_dynamicCentralizer s _).trans (Dynamic.centralizer_le_parabolic _)

end Langlands.GroupScheme
