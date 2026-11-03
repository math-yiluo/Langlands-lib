import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.MaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.BruhatCoveringReduction

/-! # Correcting rational subgroup conjugacy to normalize a maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P Q : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
  {i : T.toGrp ⟶ G} {j : P ⟶ G} {j' : Q ⟶ G}

/-- A rational conjugacy between overgroups containing an ambient maximal split
torus can be corrected inside the second overgroup to normalize that torus.
The smooth connected affine maximal split-torus conjugacy statement remains an
explicit premise. -/
theorem SubgroupConjugate.exists_normalizerPoint_of_factors
    (h : SubgroupConjugate j j')
    (htorus : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hi : IsMaximalSplitTorus i) (hj' : IsClosedSubgroup j')
    (f : T.toGrp ⟶ P) (f' : T.toGrp ⟶ Q)
    (hf : f ≫ j = i) (hf' : f' ≫ j' = i) :
    ∃ (n : normalizerPoints i) (e : P ≅ Q),
      j ≫ (G.innerIso n.val).hom = e.hom ≫ j' := by
  obtain ⟨g, e, hje⟩ := h
  have hfe : (f ≫ e.hom) ≫ j' = i ≫ (G.innerIso g).hom := by
    rw [Category.assoc, ← hje, ← Category.assoc, hf]
  have hm : IsMaximalSplitTorus (f ≫ e.hom) := by
    apply IsMaximalSplitTorus.of_comp hj'
    rw [hfe]
    exact hi.comp_iso (G.innerIso g)
  have hm' : IsMaximalSplitTorus f' := by
    apply IsMaximalSplitTorus.of_comp hj'
    rwa [hf']
  obtain ⟨p, eT, hp⟩ := htorus k Q T T (f ≫ e.hom) f' hm hm'
  have hn : i ≫ (G.innerIso ((p ≫ j'.hom.hom) * g)).hom = eT.hom ≫ i := by
    calc
      i ≫ (G.innerIso ((p ≫ j'.hom.hom) * g)).hom
          = (i ≫ (G.innerIso g).hom) ≫
              (G.innerIso (p ≫ j'.hom.hom)).hom := by
            rw [innerIso_mul_hom, Category.assoc]
      _ = ((f ≫ e.hom) ≫ (Q.innerIso p).hom) ≫ j' := by
            rw [← hfe]
            simp only [Category.assoc, innerIso_hom_comp]
      _ = eT.hom ≫ i := by
            rw [hp, Category.assoc, hf']
  let σ : T ≅ T :=
    { hom := Additive.ofMul eT.hom
      inv := Additive.ofMul eT.inv
      hom_inv_id := congrArg Additive.ofMul eT.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul eT.inv_hom_id }
  refine ⟨⟨(p ≫ j'.hom.hom) * g, ⟨σ, hn⟩⟩, e ≪≫ Q.innerIso p, ?_⟩
  rw [innerIso_mul_hom, ← Category.assoc, hje, Iso.trans_hom, Category.assoc,
    Category.assoc, innerIso_hom_comp]

/-- The all-test containment form of normalizer conjugacy correction. -/
theorem SubgroupConjugate.exists_normalizerPoint
    (h : SubgroupConjugate j j')
    (htorus : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hi : IsMaximalSplitTorus i)
    (hj : IsClosedSubgroup j) (hj' : IsClosedSubgroup j')
    (hcontained : SubgroupFunctor.range i ≤ SubgroupFunctor.range j)
    (hcontained' : SubgroupFunctor.range i ≤ SubgroupFunctor.range j') :
    ∃ (n : normalizerPoints i) (e : P ≅ Q),
      j ≫ (G.innerIso n.val).hom = e.hom ≫ j' := by
  have := hj.mono
  have := hj'.mono
  have hrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hrep' : (SubgroupFunctor.range j').IsRepresentedBy j' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact h.exists_normalizerPoint_of_factors htorus hi hj'
    (hrep.factorHom i hcontained) (hrep'.factorHom i hcontained')
    (hrep.factorHom_comp i hcontained) (hrep'.factorHom_comp i hcontained')

/-- Choose an actual normalizing rational point and source isomorphism realizing
a given rational conjugacy of closed overgroups of a maximal split torus. -/
def SubgroupConjugate.normalizerCorrection
    (h : SubgroupConjugate j j')
    (htorus : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hi : IsMaximalSplitTorus i)
    (hj : IsClosedSubgroup j) (hj' : IsClosedSubgroup j')
    (hcontained : SubgroupFunctor.range i ≤ SubgroupFunctor.range j)
    (hcontained' : SubgroupFunctor.range i ≤ SubgroupFunctor.range j') :
    (n : normalizerPoints i) ×
      {e : P ≅ Q // j ≫ (G.innerIso n.val).hom = e.hom ≫ j'} :=
  let hex := h.exists_normalizerPoint htorus hi hj hj' hcontained hcontained'
  ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

end Langlands.GroupScheme
