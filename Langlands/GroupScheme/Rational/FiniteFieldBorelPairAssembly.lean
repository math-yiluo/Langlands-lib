import Langlands.GroupScheme.Rational.FiniteFieldBorelConjugacy
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Assembling pair conjugacy from a Borel conjugator -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.FiniteFieldBorelPair

variable {k : Type u} [Field k]
  {G B B' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Once the Borels of two pairs are conjugate, rational maximal-torus
conjugacy inside the target Borel supplies simultaneous pair conjugacy. -/
theorem pair_conjugacy_of_borel_conjugator
    (b : B ⟶ G) (b' : B' ⟶ G) (j : T.toGrp ⟶ G) (j' : T'.toGrp ⟶ G)
    (hj : IsMaximalTorus j)
    (hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b)
    (hb' : IsBorelSubgroup b') (hj' : IsMaximalTorus j')
    (hjb' : SubgroupFunctor.range j' ≤ SubgroupFunctor.range b')
    (g : rationalPoints G)
    (hg : SubgroupFunctor.range (b ≫ (G.innerIso g).hom) =
      SubgroupFunctor.range b') :
    ∃ q : rationalPoints G,
      SubgroupFunctor.range (b ≫ (G.innerIso q).hom) = SubgroupFunctor.range b' ∧
        SubgroupFunctor.range (j ≫ (G.innerIso q).hom) = SubgroupFunctor.range j' := by
  let : Smooth B'.X.hom := hb'.smooth
  let : ConnectedSpace B'.X.left := hb'.connectedSpace
  let : IsClosedImmersion b'.hom.hom.left := hb'.isClosedSubgroup
  let : Mono b'.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom B'.X.hom := by
    rw [← Over.w b'.hom.hom]
    infer_instance
  let hr : (SubgroupFunctor.range b').IsRepresentedBy b' := ⟨inferInstance, rfl⟩
  let jg := j ≫ (G.innerIso g).hom
  have hjg : IsMaximalTorus jg := hj.comp_iso (G.innerIso g)
  have hcontain : SubgroupFunctor.range jg ≤ SubgroupFunctor.range b' := by
    rw [← hg]
    exact SubgroupFunctor.range_comp_mono hjb _
  let f := hr.factorHom jg hcontain
  let f' := hr.factorHom j' hjb'
  have hf : f ≫ b' = jg := hr.factorHom_comp _ _
  have hf' : f' ≫ b' = j' := hr.factorHom_comp _ _
  have hmax : IsMaximalTorus f :=
    IsMaximalTorus.of_comp hb'.isClosedSubgroup (by rw [hf]; exact hjg)
  have hmax' : IsMaximalTorus f' :=
    IsMaximalTorus.of_comp hb'.isClosedSubgroup (by rw [hf']; exact hj')
  obtain ⟨p, e, he⟩ :=
    solvableMaximalTorusConjugacy k B' hb'.isSolvableGroupScheme T T' f f' hmax hmax'
  let pG := p ≫ b'.hom.hom
  have htorus : jg ≫ (G.innerIso pG).hom = e.hom ≫ j' := by
    rw [← hf, Category.assoc, ← innerIso_hom_comp, ← Category.assoc,
      he, Category.assoc, hf']
  refine ⟨pG * g, ?_, ?_⟩
  · rw [innerIso_mul_hom, ← Category.assoc]
    rw [(SubgroupFunctor.range_comp_iso_eq_iff
      (b ≫ (G.innerIso g).hom) b' (G.innerIso pG)).mpr hg]
    exact range_comp_innerIso_of_mem b' p
  · rw [innerIso_mul_hom, ← Category.assoc]
    change SubgroupFunctor.range (jg ≫ (G.innerIso pG).hom) = _
    rw [htorus, SubgroupFunctor.range_iso_comp]

end Langlands.GroupScheme.FiniteFieldBorelPair
