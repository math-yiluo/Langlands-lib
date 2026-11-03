import Langlands.GroupScheme.Rational.MinimalPseudoParabolic
import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # All-test range reductions for minimal pseudo-parabolic conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- Membership in an fppf-local product descends into any monic represented
subgroup containing both factors on every test scheme. -/
theorem FppfLocallyInProduct.mem_range
    {F N : SubgroupFunctor G} {j : Q ⟶ G} [Mono j.hom.hom]
    (hF : F ≤ range j) (hN : N ≤ range j)
    {T : Over S} {x : T ⟶ G.X} (hx : FppfLocallyInProduct F N x) :
    x ∈ (range j).carrier T := by
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ := hx
  let : Flat v.left := hf
  let : Surjective v.left := hs
  let : LocallyOfFinitePresentation v.left := hl
  apply mem_range_of_comp_mem_range j v
  rw [he]
  exact (range j).carrier V |>.mul_mem (hF V hp) (hN V hn)

/-- A represented fppf-local product lies in every monic represented subgroup
containing its two factors. -/
theorem IsFppfProduct.range_le
    {F N : SubgroupFunctor G} {i : P ⟶ G} {j : Q ⟶ G}
    (hi : IsFppfProduct F N i) [Mono j.hom.hom]
    (hF : F ≤ range j) (hN : N ≤ range j) : range i ≤ range j := by
  intro T x hx
  exact FppfLocallyInProduct.mem_range hF hN ((hi.mem_range_iff T x).mp hx)

end SubgroupFunctor

section Conjugacy

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- The isomorphism between two closed subgroup representatives with equal
images on every relative scheme test. -/
def IsClosedSubgroup.sourceIsoOfRangeEq {i : P ⟶ G} {j : Q ⟶ G}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range j) : P ≅ Q := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range i).IsRepresentedBy j := ⟨inferInstance, h.symm⟩
  exact hr.isoOfIsRepresentedBy hr'

/-- The isomorphism from equal images commutes with the subgroup inclusions. -/
theorem IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp {i : P ⟶ G} {j : Q ⟶ G}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range j) :
    (hi.sourceIsoOfRangeEq hj h).hom ≫ j = i := by
  unfold sourceIsoOfRangeEq
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- Equality of all-test images of closed subgroups gives an actual source
isomorphism and subgroup conjugacy by the identity rational point. -/
theorem SubgroupConjugate.of_range_eq {i : P ⟶ G} {j : Q ⟶ G}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range j) :
    SubgroupConjugate i j := by
  refine ⟨1, hi.sourceIsoOfRangeEq hj h, ?_⟩
  rw [innerIso_one_hom, Category.comp_id]
  exact (hi.sourceIsoOfRangeEq_hom_comp hj h).symm

/-- Equality of the conjugated all-test image gives actual rational subgroup
conjugacy, including an isomorphism of the two source group schemes. -/
theorem SubgroupConjugate.of_conjugate_range_eq {i : P ⟶ G} {j : Q ⟶ G}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (g : Over.mk (𝟙 S) ⟶ G.X)
    (h : SubgroupFunctor.range (i ≫ (G.innerIso g).hom) = SubgroupFunctor.range j) :
    SubgroupConjugate i j :=
  (SubgroupConjugate.conjugate i g).trans
    (SubgroupConjugate.of_range_eq (hi.comp_iso (G.innerIso g)) hj h)

end Conjugacy

section Minimality

variable {k : Type u} [Field k]
  {G P Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Minimality turns containment of one pseudo-parabolic in a minimal one
into actual subgroup conjugacy by the identity point. -/
theorem IsMinimalPseudoParabolicSubgroup.subgroupConjugate_of_range_le
    {i : P ⟶ G} {j : Q ⟶ G}
    (hj : IsMinimalPseudoParabolicSubgroup j) (hi : IsPseudoParabolicSubgroup i)
    (hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j) :
    SubgroupConjugate i j :=
  SubgroupConjugate.of_range_eq hi.isClosedSubgroup hj.isClosedSubgroup
    (hj.range_eq_of_le hi hle)

/-- The final range/minimality step of CGP C.2.5. Its geometric inputs remain
explicit: the conjugate must be pseudo-parabolic and contained on every test. -/
theorem IsMinimalPseudoParabolicSubgroup.subgroupConjugate_of_conjugate_range_le
    {i : P ⟶ G} {j : Q ⟶ G}
    (hi : IsClosedSubgroup i) (hj : IsMinimalPseudoParabolicSubgroup j)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hconj : IsPseudoParabolicSubgroup (i ≫ (G.innerIso g).hom))
    (hle : SubgroupFunctor.range (i ≫ (G.innerIso g).hom) ≤ SubgroupFunctor.range j) :
    SubgroupConjugate i j :=
  SubgroupConjugate.of_conjugate_range_eq hi hj.isClosedSubgroup g
    (hj.range_eq_of_le hconj hle)

end Minimality

end Langlands.GroupScheme
