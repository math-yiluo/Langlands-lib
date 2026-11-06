import Langlands.GroupScheme.Rational.ReductiveParabolicContraction
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Moving a supplied presenting cocharacter into the original Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G P L U : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {l : L ⟶ P}

/-- The supplied ground-field radical is the exact all-test kernel of the
ambient dynamic presentation. -/
theorem DynamicLeviConjugacy.mem_range_radical_iff_of_reductive
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p)
    {r : U ⟶ P} (hr : IsUnipotentRadical r)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ P.X) :
    x ∈ (SubgroupFunctor.range r).carrier T ↔
      x ≫ p.hom.hom ∈ (Dynamic.unipotent χ).carrier T := by
  let : Mono p.hom.hom := hP.1
  rw [← Dynamic.range_comp_radical_eq_unipotent_of_reductive hG χ p hP r hr]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr
      ⟨y, by simp only [Grp.comp_hom_hom, Category.assoc]⟩
  · intro hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨y, (cancel_mono p.hom.hom).mp ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy

/-- A supplied dynamic presentation can be realized by a central cocharacter
of the original rational Levi, with the original parabolic map unchanged. -/
theorem IsRationalLeviSubgroup.exists_centralCocharacter_of_dynamicParabolic
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p) :
    ∃ psiL : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L,
      IsCentral psiL ∧ (Dynamic.parabolic (psiL ≫ l ≫ p)).IsRepresentedBy p := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsSeparated G.X.hom := hG.isSeparated
  obtain ⟨U, r, q, hr, -, hlq, hker⟩ := hl.exists_unipotentRadical_retraction
  have hker' : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ P.X),
      x ≫ q.hom.hom = 1 ↔ x ≫ p.hom.hom ∈ (Dynamic.unipotent χ).carrier T := by
    intro T x
    rw [hker, DynamicLeviConjugacy.mem_range_radical_iff_of_reductive hG χ hP hr.1 x]
  let psiL := DynamicLeviConjugacy.parabolicCocharacter χ hP ≫ q
  have hpsiL : IsCentral psiL := by
    apply (isCentral_iff_dynamicCentralizer_eq_top psiL).2
    exact DynamicLeviConjugacy.centralizer_leviCocharacter_eq_top (hj := hP) l q hlq hker'
  obtain ⟨v, hv, hμ⟩ := Dynamic.exists_unipotent_conj_of_mul_inv_mem χ (psiL ≫ l ≫ p)
    (DynamicLeviConjugacy.leviCocharacter_mul_inv_mem (hj := hP) l q hlq hker')
  have hpar : Dynamic.parabolic (psiL ≫ l ≫ p) = Dynamic.parabolic χ := by
    rw [← hμ]
    exact DynamicLeviConjugacy.parabolic_comp_innerIso_eq χ
      (Dynamic.unipotent_le_parabolic χ _ hv)
  exact ⟨psiL, hpsiL, hP.1, hP.2.trans hpar.symm⟩

section SplitComponent

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ L}

set_option maxHeartbeats 800000 in
/-- Every specified split component of the original rational Levi contains a
cocharacter realizing the supplied dynamic presentation and the original Levi.
Its whole-group centralizer is that original Levi image. -/
theorem IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p) (ha : IsSplitComponent a) :
    ∃ ν : cocharacterLattice A,
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p)).IsRepresentedBy p ∧
        Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) =
          SubgroupFunctor.range (l ≫ p) ∧
        torusCentralizer (a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) := by
  let : IsAffineHom L.X.hom := hl.isConnectedReductive.isAffineHom
  obtain ⟨psiL, hpsiL, hpsiLP⟩ := hl.exists_centralCocharacter_of_dynamicParabolic hG χ hP
  obtain ⟨ν, hν⟩ := ha.exists_factor isSplitTorus_gm hpsiL
  have hνP : (Dynamic.parabolic (ν ≫ a ≫ l ≫ p)).IsRepresentedBy p := by
    rw [← Category.assoc ν a, hν]
    exact hpsiLP
  refine ⟨Additive.ofMul ν, hνP, ?_, ?_⟩
  · change Dynamic.centralizer (ν ≫ a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p)
    have h := hl.centralizer_eq_of_dynamicParabolic hG (ν ≫ a) (by
      simpa only [Category.assoc] using hνP)
    simpa only [Category.assoc] using h
  · exact hl.torusCentralizer_eq_of_dynamicParabolic hG a ha.1.2 ν hνP

variable (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p) (ha : IsSplitComponent a)

/-- A chosen actual cocharacter of the specified split component realizing the
original parabolic and Levi, starting from any supplied dynamic presentation. -/
def IsRationalLeviSubgroup.splitComponentCocharacterOfDynamicParabolic : cocharacterLattice A :=
  (hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha).choose

/-- The chosen cocharacter presents the original parabolic, has exactly the
original Levi centralizer, and identifies the whole split-component centralizer. -/
theorem IsRationalLeviSubgroup.splitComponentCocharacterOfDynamicParabolic_spec :
    (Dynamic.parabolic
      (CommGroupScheme.groupHom (hl.splitComponentCocharacterOfDynamicParabolic hG χ hP ha) ≫
        a ≫ l ≫ p)).IsRepresentedBy p ∧
      Dynamic.centralizer
        (CommGroupScheme.groupHom (hl.splitComponentCocharacterOfDynamicParabolic hG χ hP ha) ≫
          a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) ∧
      torusCentralizer (a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) :=
  (hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha).choose_spec

end SplitComponent

end Langlands.GroupScheme
