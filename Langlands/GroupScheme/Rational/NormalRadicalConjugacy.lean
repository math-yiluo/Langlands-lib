import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Rational.BruhatCoveringReduction
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyReduction
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.NormalizerRepresentability

/-! # Conjugation transport through a represented normal subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Scheme

variable {S : Scheme.{u}} {H R P G G' : GroupScheme S}
  {B : CommGroupScheme S}

/-- Whole-torus centralizers commute with an isomorphism of ambient groups. -/
theorem torusCentralizer_eq_comap_of_iso (b : B.toGrp ⟶ G) (e : G ≅ G') :
    torusCentralizer b = (torusCentralizer (b ≫ e.hom)).comap e.hom := by
  simpa only [torusCentralizer_eq_centralizer_range] using
    SubgroupFunctor.centralizer_range_eq_comap_of_iso b e

namespace SubgroupFunctor.IsRepresentedBy

variable {F : SubgroupFunctor P} {r : R ⟶ P}

/-- Conjugate a map into a represented normal subgroup, retaining that
specified representative as the codomain. -/
def conjugateFactor (hr : F.IsRepresentedBy r) (hn : F.IsNormal)
    (b : H ⟶ R) (g : Over.mk (𝟙 S) ⟶ P.X) : H ⟶ R :=
  hr.factorHom (b ≫ r ≫ (P.innerIso g).hom) (by
    rintro U _ ⟨x, rfl⟩
    change U ⟶ H.X at x
    change x ≫ (b ≫ r ≫ (P.innerIso g).hom).hom.hom ∈ F.carrier U
    simp only [Grp.comp_hom_hom, ← Category.assoc]
    rw [comp_innerIso_hom]
    apply hn U _ _ (Subgroup.mem_top _)
    rw [← hr.2]
    exact ⟨x ≫ b.hom.hom, rfl⟩)

/-- The transported map has exactly the conjugated original composite. -/
@[simp] theorem conjugateFactor_comp (hr : F.IsRepresentedBy r) (hn : F.IsNormal)
    (b : H ⟶ R) (g : Over.mk (𝟙 S) ⟶ P.X) :
    hr.conjugateFactor hn b g ≫ r = b ≫ r ≫ (P.innerIso g).hom :=
  hr.factorHom_comp _ _

/-- The inclusion in the specified normal subgroup determines the transported
homomorphism uniquely. -/
theorem conjugateFactor_unique (hr : F.IsRepresentedBy r) (hn : F.IsNormal)
    (b : H ⟶ R) (g : Over.mk (𝟙 S) ⟶ P.X) {b' : H ⟶ R}
    (hb' : b' ≫ r = b ≫ r ≫ (P.innerIso g).hom) :
    b' = hr.conjugateFactor hn b g :=
  hr.hom_ext (hb'.trans (hr.conjugateFactor_comp hn b g).symm)

/-- Any further ambient homomorphism carries the factor transport to
conjugation by the image of the same rational point. -/
theorem conjugateFactor_comp_ambient (hr : F.IsRepresentedBy r) (hn : F.IsNormal)
    (b : H ⟶ R) (g : Over.mk (𝟙 S) ⟶ P.X) (j : P ⟶ G) :
    hr.conjugateFactor hn b g ≫ r ≫ j =
      (b ≫ r ≫ j) ≫ (G.innerIso (g ≫ j.hom.hom)).hom := by
  rw [← Category.assoc, conjugateFactor_comp]
  simp only [Category.assoc, innerIso_hom_comp]

end SubgroupFunctor.IsRepresentedBy

end Scheme

section Field

variable {k : Type u} [Field k]
  {L L' R P G : GroupScheme (Spec (CommRingCat.of k))}
  {l : L ⟶ P} {l' : L' ⟶ P}

/-- A maximal-split centralizer presentation through a specified normal
subgroup transports to every supplied rationally conjugate subgroup. -/
theorem SubgroupConjugate.exists_maximalSplitTorus_centralizer
    (hconj : SubgroupConjugate l l') {F : SubgroupFunctor P} {r : R ⟶ P}
    (hr : F.IsRepresentedBy r) (hn : F.IsNormal) (j : P ⟶ G)
    (h : ∃ (B : CommGroupScheme (Spec (CommRingCat.of k))) (b : B.toGrp ⟶ R),
      IsMaximalSplitTorus (b ≫ r ≫ j) ∧
        torusCentralizer (b ≫ r ≫ j) = SubgroupFunctor.range (l ≫ j)) :
    ∃ (B : CommGroupScheme (Spec (CommRingCat.of k))) (b : B.toGrp ⟶ R),
      IsMaximalSplitTorus (b ≫ r ≫ j) ∧
        torusCentralizer (b ≫ r ≫ j) = SubgroupFunctor.range (l' ≫ j) := by
  obtain ⟨g, e, he⟩ := hconj
  obtain ⟨B, b, hb, hcent⟩ := h
  let a := G.innerIso (g ≫ j.hom.hom)
  have hsquare : (l ≫ j) ≫ a.hom = e.hom ≫ (l' ≫ j) := by
    dsimp only [a]
    rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, he, Category.assoc]
  have hrange := SubgroupFunctor.range_eq_comap_of_iso_square a e hsquare
  have hcent' : torusCentralizer ((b ≫ r ≫ j) ≫ a.hom) =
      SubgroupFunctor.range (l' ≫ j) := by
    have hmap :
        (torusCentralizer ((b ≫ r ≫ j) ≫ a.hom)).comap a.hom =
          (SubgroupFunctor.range (l' ≫ j)).comap a.hom :=
      (torusCentralizer_eq_comap_of_iso (b ≫ r ≫ j) a).symm.trans
        (hcent.trans hrange)
    have hinv := congrArg (fun K : SubgroupFunctor G => K.comap a.inv) hmap
    simpa only [SubgroupFunctor.comap_iso_hom_inv] using hinv
  refine ⟨B, hr.conjugateFactor hn b g, ?_, ?_⟩
  · rw [hr.conjugateFactor_comp_ambient hn b g j]
    exact hb.comp_iso a
  · rw [hr.conjugateFactor_comp_ambient hn b g j]
    exact hcent'

end Field

end Langlands.GroupScheme
