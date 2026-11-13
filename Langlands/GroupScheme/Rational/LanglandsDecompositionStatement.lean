import Langlands.GroupScheme.Rational.LanglandsDecompositionCones
import Langlands.GroupScheme.Rational.ParabolicRootPresentation

/-! # Langlands' combinatorial lemma for actual standard parabolics (Renard V.3.18) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

/-- Renard V.3.18, Langlands' combinatorial lemma (with the `μ⁻` cone of the V.5.5 proof).
For actual standard-parabolic data `P = MN` of `J`, restriction along `f : A_M → A_∅` identifies
the coroot annihilator `𝔞*_M ⊂ 𝔞*_∅` with the actual `X*(A_M) ⊗ ℝ`; every `μ ∈ 𝔞*_M` has a
unique decomposition `(K, μ_G, μ⁺, μ⁻)` (with `Q ⊇ P` the standard parabolic of `K`), whose
components are the orthogonal projection on `𝔞*_G` and the projections on the closed cones
`^G_P[(𝔞^G_M)*]^+` and `⁻[𝔞*_M]^G_P`, are pairwise orthogonal, and form the unique
decomposition of `μ` relative to `P_∅`. -/
def LanglandsCombinatorialDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ (D : RelativeRootReflectionData i) (B : LinearMap.BilinForm ℝ (Vstar T)),
      IsWeylInvariantInnerProduct i B →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (P M : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (J : Set (characterLattice T)) (f : A ⟶ T),
      (⟨T, i, ν, J, f⟩ : ParabolicRootPresentationData A G).IsCompatible p l a →
      (∀ x : Vstar A, ∃! y : Vstar T, y ∈ corootAnnihilator i D J ∧
          rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = x) ∧
      ∀ μ ∈ corootAnnihilator i D J,
        (∃! d : Set (characterLattice T) × Vstar T × Vstar T × Vstar T,
          IsLanglandsDecomposition i ν D J μ d.1 d.2.1 d.2.2.1 d.2.2.2) ∧
        ∀ (K : Set (characterLattice T)) (μG μp μm : Vstar T),
          IsLanglandsDecomposition i ν D J μ K μG μp μm →
            (∀ z ∈ LinearMap.range (rationalCharacterRestrictReal i), B (μ - μG) z = 0) ∧
            (μp ∈ closedCorootFace i ν D J ∧ ∀ w ∈ closedCorootFace i ν D J,
              B (μ - μp) (μ - μp) ≤ B (μ - w) (μ - w)) ∧
            (-μm ∈ projectedRootNonnegCone i D J (simpleRelativeRoots i ν \ J) ∧
              ∀ w : Vstar T, -w ∈ projectedRootNonnegCone i D J (simpleRelativeRoots i ν \ J) →
                B (μ - μm) (μ - μm) ≤ B (μ - w) (μ - w)) ∧
            B μG μp = 0 ∧ B μG μm = 0 ∧ B μp μm = 0 ∧
            ∀ (K' : Set (characterLattice T)) (μG' μp' μm' : Vstar T),
              IsLanglandsDecomposition i ν D ∅ μ K' μG' μp' μm' ↔
                K' = K ∧ μG' = μG ∧ μp' = μp ∧ μm' = μm

end Langlands.GroupScheme
