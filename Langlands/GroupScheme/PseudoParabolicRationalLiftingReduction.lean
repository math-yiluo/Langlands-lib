import Langlands.GroupScheme.PseudoParabolicQuotientSplitRadicalReduction
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingStatement

/-! # Rational lifts through a supplied split-radical quotient

The fixed-group property keeps exactly the quotient hypotheses and rational
lifting conclusion of the published target. A section of the supplied group
quotient transfers this property from the reduced group once an actual
pseudo-parabolic subgroup with the exact full preimage has been supplied.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The rational-lifting property of a fixed ambient group, retaining every
supplied quotient model and the exact all-test right-coset condition. -/
def PseudoParabolicRationalLiftingProperty
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
    IsPseudoParabolicSubgroup i →
    ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
      IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
      Smooth q.left → Surjective q.left → QuasiCompact q.left →
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, g ≫ q = x

/-- The fixed-group property is exactly the body of the published target. -/
theorem pseudoParabolicQuotientRationalLiftingStatement_iff :
    PseudoParabolicQuotientRationalLiftingStatement.{u} ↔
      ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth G.X.hom] [IsAffineHom G.X.hom],
        ConnectedSpace G.X.left → PseudoParabolicRationalLiftingProperty G :=
  Iff.rfl

namespace PseudoParabolicRationalLiftingReduction

variable {G P N H K : GroupScheme (Spec (CommRingCat.of k))}
variable [IsAffineHom G.X.hom]

section Point

variable (i : P ⟶ G) (hi : IsPseudoParabolicSubgroup i)
variable (n : N ⟶ G) (hn : IsSplitUnipotentRadical n)
variable (f : G ⟶ H)
variable (hf : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) f)
variable (j : K ⟶ H) (hj : IsPseudoParabolicSubgroup j)
variable (hpre : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap f)
variable (s : H.X ⟶ G.X) (hs : s ≫ f.hom.hom = 𝟙 H.X)
variable (hH : PseudoParabolicRationalLiftingProperty H)
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable (hsep : IsSeparated Q.hom) (hlft : LocallyOfFiniteType Q.hom)
variable (hqc : QuasiCompact Q.hom)
variable (hsmq : Smooth q.left) (hsurjq : Surjective q.left)
variable (hqcq : QuasiCompact q.left)
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
  a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T)

include hi hn hf hj hpre hs hH hsep hlft hqc hsmq hsurjq hqcq hfib

/-- Reduced rational lifting and an actual section of the supplied group
quotient lift every rational point of the original supplied quotient. -/
theorem exists_lift
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, g ≫ q = x := by
  let : Smooth q.left := hsmq
  let : Surjective q.left := hsurjq
  let : QuasiCompact q.left := hqcq
  let : IsAffineHom H.X.hom := hj.isAffineHom
  have hcomp : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  let : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := hcomp
  let : QuasiCompact f.hom.hom.left := QuasiCompact.of_comp _ H.X.hom
  let r := PseudoParabolicQuotientSplitRadicalReduction.quotientMap
    i hi n hn f hf q hfib
  have hfac : f.hom.hom ≫ r = q :=
    PseudoParabolicQuotientSplitRadicalReduction.fac_quotientMap
      i hi n hn f hf q hfib
  obtain ⟨a, ha⟩ := hH K j hj Q r hsep hlft hqc
    (PseudoParabolicQuotientSplitRadicalReduction.quotientMap_smooth
      i hi n hn f hf q hfib)
    (PseudoParabolicQuotientSplitRadicalReduction.quotientMap_surjective
      i hi n hn f hf q hfib)
    (PseudoParabolicQuotientSplitRadicalReduction.quotientMap_quasiCompact
      i hi n hn f hf q hfib)
    (PseudoParabolicQuotientSplitRadicalReduction.quotientMap_fibers
      i hi n hn f hf q hfib j hj hpre) x
  have hsq : s ≫ q = r := by
    rw [← hfac, ← Category.assoc, hs, Category.id_comp]
  exact ⟨a ≫ s, by rw [Category.assoc, hsq, ha]⟩

/-- A chosen actual lift in the original group, together with its equation
under the original supplied quotient map. -/
def lift
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X // g ≫ q = x} :=
  ⟨Classical.choose
      (exists_lift i hi n hn f hf j hj hpre s hs hH q hsep hlft hqc
        hsmq hsurjq hqcq hfib x),
    Classical.choose_spec
      (exists_lift i hi n hn f hf j hj hpre s hs hH q hsep hlft hqc
        hsmq hsurjq hqcq hfib x)⟩

end Point

/-- An actual section and pseudo-parabolic descent on all tests transfer the
entire fixed-group lifting property from the supplied quotient group. -/
theorem property_of_section
    (n : N ⟶ G) (hn : IsSplitUnipotentRadical n)
    (f : G ⟶ H)
    (hf : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) f)
    (s : H.X ⟶ G.X) (hs : s ≫ f.hom.hom = 𝟙 H.X)
    (hH : PseudoParabolicRationalLiftingProperty H)
    (hdescent : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i →
      ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ H),
        IsPseudoParabolicSubgroup j ∧
          SubgroupFunctor.range i = (SubgroupFunctor.range j).comap f) :
    PseudoParabolicRationalLiftingProperty G := by
  intro P i hi Q q hsep hlft hqc hsmq hsurjq hqcq hfib x
  obtain ⟨K, j, hj, hpre⟩ := hdescent P i hi
  let a := lift i hi n hn f hf j hj hpre s hs hH q hsep hlft hqc
    hsmq hsurjq hqcq hfib x
  exact ⟨a.val, a.property⟩

end PseudoParabolicRationalLiftingReduction
end Langlands.GroupScheme
