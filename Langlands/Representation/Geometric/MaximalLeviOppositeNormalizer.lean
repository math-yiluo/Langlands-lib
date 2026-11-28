import Langlands.GroupScheme.Rational.MaximalLeviParabolicCountProof
import Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport
import Langlands.Representation.Geometric.ConjugatedParabolicIndexing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Normalizers of the common Levi of a maximal opposite pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G P M Q : GroupScheme (Spec (CommRingCat.of k))}

private theorem range_eq_left_or_right_of_maximal_commonLevi
    (hG : IsConnectedReductive G) {p : P ⟶ G} {l : M ⟶ P}
    {q : Q ⟶ G} {lQ : M ⟶ Q}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hlevi : lQ ≫ q = l ≫ p) (hproper : ¬ IsIso p)
    (hmax : ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (j : R ⟶ G) (f : P ⟶ R),
      IsParabolicSubgroup j → f ≫ j = p → IsIso f ∨ IsIso j)
    (hne : SubgroupFunctor.range p ≠ SubgroupFunctor.range q)
    {R : GroupScheme (Spec (CommRingCat.of k))} {j : R ⟶ G} {lR : M ⟶ R}
    (hj : IsParabolicSubgroup j) (hlR : IsRationalLeviSubgroup lR)
    (he : lR ≫ j = l ≫ p) :
    SubgroupFunctor.range j = SubgroupFunctor.range p ∨
      SubgroupFunctor.range j = SubgroupFunctor.range q := by
  classical
  by_contra! hd
  let S := {F : SubgroupFunctor G //
    ∃ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ G) (m : M ⟶ T),
      IsParabolicSubgroup t ∧ IsRationalLeviSubgroup m ∧
        m ≫ t = l ≫ p ∧ SubgroupFunctor.range t = F}
  let a : S := ⟨_, P, p, l, hp, hl, rfl, rfl⟩
  let b : S := ⟨_, Q, q, lQ, hq, hlQ, hlevi, rfl⟩
  let c : S := ⟨_, R, j, lR, hj, hlR, he, rfl⟩
  let f : Fin 3 → S := ![a, b, c]
  have hf : Function.Injective (fun i => (f i).1) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, a, b, c]
  have hs (s : S) := s.property
  choose Ts ts ms hts hms hcomp hrange using hs
  have hcount := maximalLeviParabolicCount k G hG P M p l hp hl hproper hmax 3
    (fun i => Ts (f i)) (fun i => ts (f i)) (fun i => ms (f i))
    (fun i => hts (f i)) (fun i => hms (f i)) (fun i => hcomp (f i))
    (fun i j h => hf (by simpa only [hrange] using h))
  omega

variable {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {lQ : M ⟶ Q}

/-- A normalizer of the common Levi either exchanges the two distinct maximal opposite
parabolic ranges or belongs to their common Levi. -/
theorem range_swap_or_mem_levi_of_normalizes
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hlevi : lQ ≫ q = l ≫ p)
    (hinf : SubgroupFunctor.range p ⊓ SubgroupFunctor.range q = SubgroupFunctor.range (l ≫ p))
    (hproper : ¬ IsIso p)
    (hmax : ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (j : R ⟶ G) (f : P ⟶ R),
      IsParabolicSubgroup j → f ≫ j = p → IsIso f ∨ IsIso j)
    (hne : SubgroupFunctor.range p ≠ SubgroupFunctor.range q)
    (g : rationalPoints G) (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom) :
    (SubgroupFunctor.range (p ≫ (G.innerIso g).hom) = SubgroupFunctor.range q ∧
      SubgroupFunctor.range (q ≫ (G.innerIso g).hom) = SubgroupFunctor.range p) ∨
      g ∈ pointImage (l ≫ p) := by
  let e := G.innerIso g
  have hlp : (φ.inv ≫ l) ≫ p ≫ e.hom = l ≫ p := by
    rw [Category.assoc, ← hφ, Iso.inv_hom_id_assoc]
  have hlq : (φ.inv ≫ lQ) ≫ q ≫ e.hom = l ≫ p := by
    simpa only [Category.assoc, ← Category.assoc lQ q, hlevi] using hlp
  have hcompare := @range_eq_left_or_right_of_maximal_commonLevi k _ G P M Q
    hG p l q lQ hp hl hq hlQ hlevi hproper hmax hne
  have hpc := hcompare (hp.comp_iso e) (hl.iso_comp φ.symm) hlp
  have hqc := hcompare (hq.comp_iso e) (hlQ.iso_comp φ.symm) hlq
  have hdistinct : SubgroupFunctor.range (p ≫ e.hom) ≠ SubgroupFunctor.range (q ≫ e.hom) :=
    fun h => hne ((SubgroupFunctor.range_comp_iso_eq_iff p q e).mp h)
  rcases hpc with hfix | hswap
  · have hfixQ := hqc.resolve_left (fun h => hdistinct (hfix.trans h.symm))
    have hgp := mem_pointImage_of_range_comp_innerIso_eq hp.isClosedSubgroup
      (parabolicSelfNormalizer k G hG P p hp) g hfix.symm
    have hgq := mem_pointImage_of_range_comp_innerIso_eq hq.isClosedSubgroup
      (parabolicSelfNormalizer k G hG Q q hq) g hfixQ.symm
    right
    rw [pointImage_eq_range_carrier, ← hinf]
    exact ⟨hgp, hgq⟩
  · exact Or.inl ⟨hswap, hqc.resolve_right (fun h => hdistinct (hswap.trans h.symm))⟩

/-- A Levi normalizer in the identity double coset of a maximal opposite pair
belongs to the Levi. -/
theorem mem_levi_of_normalizer_identity_doubleCoset
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hlevi : lQ ≫ q = l ≫ p)
    (hinf : SubgroupFunctor.range p ⊓ SubgroupFunctor.range q = SubgroupFunctor.range (l ≫ p))
    (hproper : ¬ IsIso p)
    (hmax : ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (j : R ⟶ G) (f : P ⟶ R),
      IsParabolicSubgroup j → f ≫ j = p → IsIso f ∨ IsIso j)
    (hne : SubgroupFunctor.range p ≠ SubgroupFunctor.range q)
    (g : rationalPoints G) (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom)
    (hg : DoubleCoset.mk (pointImage p) (pointImage q) g =
      DoubleCoset.mk (pointImage p) (pointImage q) 1) :
    g ∈ pointImage (l ≫ p) := by
  rcases range_swap_or_mem_levi_of_normalizes hG hp hl hq hlQ hlevi hinf hproper hmax
      hne g φ hφ with ⟨_, hswap⟩ | hmem
  · obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hxy⟩ := DoubleCoset.eq.mp hg.symm
    rw [mul_one] at hxy
    let e := G.innerIso (rationalPoints.map p a)
    have hqfix : SubgroupFunctor.range (q ≫ (G.innerIso (rationalPoints.map q b)).hom) =
        SubgroupFunctor.range q := range_comp_innerIso_of_mem q b
    have hpfix : SubgroupFunctor.range (p ≫ e.hom) =
        SubgroupFunctor.range p := range_comp_innerIso_of_mem p a
    rw [hxy, innerIso_mul_hom, ← Category.assoc] at hswap
    have hconj := (SubgroupFunctor.range_comp_iso_eq_iff _ q e).mpr hqfix
    have he := hconj.symm.trans (hswap.trans hpfix.symm)
    exact (hne ((SubgroupFunctor.range_comp_iso_eq_iff q p e).mp he).symm).elim
  · exact hmem

end Langlands.Aubert.General.RepresentedParabolic
