import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement

/-! # Component transport and reductions for parabolic root presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

namespace ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
  {P M G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {a' : A'.toGrp ⟶ M}

/-- Pull back a compatible presentation along a compatible component map.
The supplied source map is itself required to be a split component. -/
def pullbackComponent (s : ParabolicRootPresentation p l a') (g : A ⟶ A')
    (ha : IsSplitComponent a) (hga : CommGroupScheme.groupHom g ≫ a' = a) :
    ParabolicRootPresentation p l a where
  data := {
    T := s.data.T
    i := s.data.i
    ν := s.data.ν
    J := s.data.J
    f := g ≫ s.data.f
  }
  isCompatible := {
    parabolic := s.isCompatible.parabolic
    levi := s.isCompatible.levi
    splitComponent := ha
    maximalSplit := s.isCompatible.maximalSplit
    generic := s.isCompatible.generic
    subset_simpleRoots := s.isCompatible.subset_simpleRoots
    parabolic_eq := s.isCompatible.parabolic_eq
    levi_eq := s.isCompatible.levi_eq
    factor_comp := by
      change (CommGroupScheme.groupHom g ≫ CommGroupScheme.groupHom s.data.f) ≫
        s.data.i = a ≫ l ≫ p
      rw [Category.assoc, s.isCompatible.factor_comp, ← Category.assoc, hga]
    minimal := s.isCompatible.minimal
    minimal_le := s.isCompatible.minimal_le
    realization := s.isCompatible.realization
  }

/-- Both restricted-root image equalities for a presentation and its compatible
component pullback. All other presentation fields are retained here. -/
theorem image_restrictedRoots_pullbackComponent (s : ParabolicRootPresentation p l a')
    (e : A ≅ A') (ha : IsSplitComponent a)
    (hea : CommGroupScheme.groupHom e.hom ≫ a' = a) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) '' s.restrictedRoots =
        (s.pullbackComponent e.hom ha hea).restrictedRoots ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
          (s.pullbackComponent e.hom ha hea).restrictedRoots = s.restrictedRoots :=
  image_restrictedSimpleRoots_iso s.data.i s.data.ν s.data.J e rfl

section FiniteType

variable [LocallyOfFiniteType G.X.hom]

/-- Equality of the restricted-root sets alone determines both cones, even
when all the presentation choices differ. -/
theorem cones_eq_of_restrictedRoots_eq
    (r s : ParabolicRootPresentation p l a)
    (h : r.restrictedRoots = s.restrictedRoots) :
    r.positiveCone = s.positiveCone ∧ r.nonnegCone = s.nonnegCone :=
  ⟨positiveCombinations_congr h r.finite_restrictedRoots s.finite_restrictedRoots,
    nonnegCombinations_congr h r.finite_restrictedRoots s.finite_restrictedRoots⟩

/-- Both positive-cone image equalities for a component pullback. -/
theorem image_positiveCone_pullbackComponent (s : ParabolicRootPresentation p l a')
    (e : A ≅ A') (ha : IsSplitComponent a)
    (hea : CommGroupScheme.groupHom e.hom ≫ a' = a) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) '' s.positiveCone =
        (s.pullbackComponent e.hom ha hea).positiveCone ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
          (s.pullbackComponent e.hom ha hea).positiveCone = s.positiveCone :=
  image_restrictedRootPositiveCone_iso s.data.i s.data.ν s.data.J
    s.finite_simpleRoots e rfl

/-- Both nonnegative-cone image equalities for a component pullback. -/
theorem image_nonnegCone_pullbackComponent (s : ParabolicRootPresentation p l a')
    (e : A ≅ A') (ha : IsSplitComponent a)
    (hea : CommGroupScheme.groupHom e.hom ≫ a' = a) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) '' s.nonnegCone =
        (s.pullbackComponent e.hom ha hea).nonnegCone ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
          (s.pullbackComponent e.hom ha hea).nonnegCone = s.nonnegCone :=
  image_restrictedRootNonnegCone_iso s.data.i s.data.ν s.data.J
    s.finite_simpleRoots e rfl

end FiniteType

end ParabolicRootPresentation

/-- Full presentation independence gives all six component-isomorphism
equalities, without any presentation-existence premise. -/
theorem parabolicRootPresentationIsoStatement_of_independence
    (hind : ParabolicRootPresentationIndependenceStatement.{u}) :
    ParabolicRootPresentationIsoStatement.{u} := by
  intro k _ G hG P M A A' p l a a' e
  let := hG.isAffineHom
  let := hG.smooth
  intro hea r s
  let t := s.pullbackComponent e.hom r.isCompatible.splitComponent hea
  obtain ⟨hroot, hpositive, hnonneg⟩ := hind k G hG P M A p l a r t
  obtain ⟨hrootForward, hrootReverse⟩ :=
    s.image_restrictedRoots_pullbackComponent e r.isCompatible.splitComponent hea
  obtain ⟨hpositiveForward, hpositiveReverse⟩ :=
    s.image_positiveCone_pullbackComponent e r.isCompatible.splitComponent hea
  obtain ⟨hnonnegForward, hnonnegReverse⟩ :=
    s.image_nonnegCone_pullbackComponent e r.isCompatible.splitComponent hea
  exact ⟨hrootForward.trans hroot.symm, hroot ▸ hrootReverse,
    hpositiveForward.trans hpositive.symm, hpositive ▸ hpositiveReverse,
    hnonnegForward.trans hnonneg.symm, hnonneg ▸ hnonnegReverse⟩

/-- The aggregate's component-isomorphism conjunct follows from its other
independence conjunct. Existence remains a separate necessary premise. -/
theorem parabolicRootPresentationStatement_iff_existence_independence :
    ParabolicRootPresentationStatement.{u} ↔
      ParabolicRootPresentationExistenceStatement.{u} ∧
        ParabolicRootPresentationIndependenceStatement.{u} := by
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hex, hind⟩
    exact ⟨hex, hind, parabolicRootPresentationIsoStatement_of_independence hind⟩

end Langlands.GroupScheme
