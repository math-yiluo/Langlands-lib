import Langlands.GroupScheme.PseudoParabolicRationalLiftingReduction
import Langlands.GroupScheme.Lie.QuotientConnectedKernelDimension
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceStatement
import Langlands.GroupScheme.NormalSubgroupQuotientStatement
import Langlands.GroupScheme.SplitUnipotentQuotientSection

/-! # Dimension induction through the split ground-field radical

An actual affine quotient with an actual section is constructed from the
normal-quotient and split-unipotent torsor statements. Strict Lie-dimension
induction then reduces rational lifting to the trivial split-radical case,
conditional on pseudo-parabolic descent for supplied group quotients.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual smooth connected affine quotient by the supplied represented
split radical, equipped with a scheme section of its actual projection. -/
structure SplitRadicalQuotientWithSection
    {N G : GroupScheme (Spec (CommRingCat.of k))} (n : N ⟶ G) where
  quotient : GroupScheme (Spec (CommRingCat.of k))
  projection : G ⟶ quotient
  smooth : Smooth quotient.X.hom
  isAffineHom : IsAffineHom quotient.X.hom
  connectedSpace : ConnectedSpace quotient.X.left
  isFppfQuotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) projection
  sectionMap : quotient.X ⟶ G.X
  section_comp : sectionMap ≫ projection.hom.hom = 𝟙 quotient.X

namespace SplitRadicalQuotientWithSection

variable {N G : GroupScheme (Spec (CommRingCat.of k))} {n : N ⟶ G}

/-- Choose the normal affine quotient and obtain an actual section by
split-unipotent affine-torsor triviality. Connectedness descends from G. -/
def ofStatements
    (hquot : NormalSubgroupQuotientStatement.{u})
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hn : IsSplitUnipotentRadical n) : SplitRadicalQuotientWithSection n :=
  Classical.choice (by
    obtain ⟨H, f, hsm, haff, hf⟩ :=
      hquot k G N n hn.isClosedSubgroup hn.isNormal
    let : Smooth H.X.hom := hsm
    let : IsAffineHom H.X.hom := haff
    let : Smooth N.X.hom := hn.smooth
    obtain ⟨s, hs⟩ := HomogeneousQuotient.fppf_section_of_split_unipotent_torsors
      G N n htor hn.isClosedSubgroup hn.isSplitUnipotent H f hf
    let : Surjective f.hom.hom.left := hf.2.1
    exact ⟨{
      quotient := H
      projection := f
      smooth := hsm
      isAffineHom := haff
      connectedSpace := f.hom.hom.left.surjective.connectedSpace
        f.hom.hom.left.continuous
      isFppfQuotient := hf
      sectionMap := s
      section_comp := hs
    }⟩)

/-- Any actual quotient in this package has smaller Lie dimension if its
specified split-radical kernel has nontrivial image on all tests. -/
theorem dimension_lt
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (D : SplitRadicalQuotientWithSection n)
    (hn : IsSplitUnipotentRadical n) (hne : SubgroupFunctor.range n ≠ ⊥) :
    letI := D.isAffineHom
    Lie.dimension D.quotient < Lie.dimension G := by
  let : Smooth D.quotient.X.hom := D.smooth
  let : IsAffineHom D.quotient.X.hom := D.isAffineHom
  exact hn.quotient_lieDimension_lt D.isFppfQuotient hne

/-- The actual section transfers the full rational-lifting property while
preserving every original supplied Q and q, given exact subgroup descent. -/
theorem liftingProperty
    [IsAffineHom G.X.hom]
    (D : SplitRadicalQuotientWithSection n)
    (hn : IsSplitUnipotentRadical n)
    (hH : PseudoParabolicRationalLiftingProperty D.quotient)
    (hdescent : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i →
      ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ D.quotient),
        IsPseudoParabolicSubgroup j ∧
          SubgroupFunctor.range i = (SubgroupFunctor.range j).comap D.projection) :
    PseudoParabolicRationalLiftingProperty G :=
  PseudoParabolicRationalLiftingReduction.property_of_section n hn
    D.projection D.isFppfQuotient D.sectionMap D.section_comp hH hdescent

end SplitRadicalQuotientWithSection

namespace PseudoParabolicSplitRadicalInduction

/-- Under the stated structural inputs, strong induction on actual Lie
dimension reduces the exact target to groups with trivial split radical.
No triviality assertion about the radical of the quotient is required. -/
theorem statement_of_trivial_split_radical
    (hrad : SplitUnipotentRadicalExistenceStatement.{u})
    (hquot : NormalSubgroupQuotientStatement.{u})
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    (hdescent : ∀ (k : Type u) [Field k]
      (G H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
      (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
      IsSplitUnipotentRadical n →
      ∀ f : G ⟶ H,
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) f →
        ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
          IsPseudoParabolicSubgroup i →
          ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ H),
            IsPseudoParabolicSubgroup j ∧
              SubgroupFunctor.range i = (SubgroupFunctor.range j).comap f)
    (htrivial : ∀ (k : Type u) [Field k]
      (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
      (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
      IsSplitUnipotentRadical n → SubgroupFunctor.range n = ⊥ →
        PseudoParabolicRationalLiftingProperty G) :
    PseudoParabolicQuotientRationalLiftingStatement.{u} := by
  rw [pseudoParabolicQuotientRationalLiftingStatement_iff]
  intro k _ G _ _ hconn
  let : ConnectedSpace G.X.left := hconn
  apply smoothConnectedAffineGroup_lieDimension_induction
    PseudoParabolicRationalLiftingProperty ?_ G
  intro G _ _ _ ih
  obtain ⟨N, n, hn⟩ := hrad k G
  by_cases hzero : SubgroupFunctor.range n = ⊥
  · exact htrivial k G N n hn hzero
  · let D := SplitRadicalQuotientWithSection.ofStatements hquot htor hn
    let : Smooth D.quotient.X.hom := D.smooth
    let : IsAffineHom D.quotient.X.hom := D.isAffineHom
    let : ConnectedSpace D.quotient.X.left := D.connectedSpace
    have hH : PseudoParabolicRationalLiftingProperty D.quotient :=
      ih D.quotient (D.dimension_lt hn hzero)
    exact D.liftingProperty hn hH
      (hdescent k G D.quotient N n hn D.projection D.isFppfQuotient)

end PseudoParabolicSplitRadicalInduction
end Langlands.GroupScheme
