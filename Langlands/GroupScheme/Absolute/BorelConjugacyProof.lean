import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.BorelProperQuotientProof
import Langlands.GroupScheme.Absolute.BorelFixedPointConjugacy
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SolvableProperFixedPointProof
import Langlands.GroupScheme.ConjugacyComposition

/-! # Existence and conjugacy of Borel subgroups over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every smooth connected affine group over an algebraically closed field has a Borel
subgroup, and any two actual Borel embeddings are conjugate by a rational point. -/
theorem borelConjugacy : BorelConjugacyStatement.{u} := by
  have hproper : SomeBorelQuotientProperStatement.{u} := someBorelQuotientProper
  intro k _ _ G _ _ _
  obtain ⟨C, j, hj, hCproper⟩ := hproper k G inferInstance
  obtain ⟨Q, q, hsep, hft, hqc, hsmooth, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G C j hj.isClosedSubgroup hj.smooth
  have := hsmooth
  have := hsurj
  have := hqqc
  have : IsProper Q.hom :=
    hCproper Q q hsep hft hqc hsmooth hsurj hqqc hfib
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib
  let z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q := 1 ≫ q
  have hne : Nonempty Q.left :=
    ⟨z.left (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))⟩
  refine ⟨⟨C, j, hj⟩, ?_⟩
  intro B B' i i' hi hi'
  have hcommon : ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (l : D ⟶ G),
      IsBorelSubgroup l →
        ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (φ : D ≅ C),
          l ≫ (G.innerIso g).hom = φ.hom ≫ j := by
    intro D l hl
    have := hl.smooth
    have : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
    have : IsAffineHom D.X.hom := by
      rw [← Over.w l.hom.hom]
      infer_instance
    obtain ⟨x, hx⟩ := solvableProperFixedPoint k D hl.connectedSpace hl.isSolvableGroupScheme
      Q inferInstance hne (a.restrict l)
    let d := hl.conjugatingDataOfFixedPoint hj q hfib a
      (fun T g h => Dynamic.flagQuotientSchemeAction_act_lift G
        (SubgroupFunctor.range j) q hfib g h) x hx
    exact ⟨d.1, d.2.1, d.2.2⟩
  obtain ⟨g, φ, hg⟩ := hcommon B i hi
  obtain ⟨g', φ', hg'⟩ := hcommon B' i' hi'
  let d := conjugatingDataOfCommonTarget ⟨g, φ, hg⟩ ⟨g', φ', hg'⟩
  exact ⟨d.1, d.2.1, d.2.2⟩

end Langlands.GroupScheme
