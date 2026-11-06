import Langlands.GroupScheme.Rational.FiniteWeightCoarsening
import Langlands.GroupScheme.Rational.OppositeIntersectionRootInclusions
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Finite-weight coarsening of a proper cocharacter centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A direction whose parabolic contains the original one, whose centralizer
strictly contains the original centralizer, and whose centralizer is proper. -/
def IsProperCentralizerCoarsening (i : T.toGrp ⟶ G)
    (zeta mu : cocharacterLattice T) : Prop :=
  Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) ∧
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) <
      Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) ∧
    Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) ≠ ⊤

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Strict inclusion in a proper centralizer supplies an integral direction
with a larger proper centralizer and a larger dynamic parabolic. -/
theorem exists_properCentralizerCoarsening
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T)
    (hlt : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) <
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))
    (hproper : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ≠ ⊤) :
    ∃ mu : cocharacterLattice T, IsProperCentralizerCoarsening i zeta mu := by
  classical
  have hzero : ∀ alpha ∈ relativeRoots i,
      latticePairing T alpha zeta = 0 → latticePairing T alpha eta = 0 :=
    fun _ halpha h0 =>
      relativeRoot_pairing_eq_zero_of_centralizer_le hT i eta zeta hlt.le halpha h0
  have hgne : ∃ alpha ∈ relativeRoots i, latticePairing T alpha eta ≠ 0 := by
    by_contra h
    apply hproper
    apply (isCentral_iff_dynamicCentralizer_eq_top _).mp
    apply rootAnnihilatorCentrality k G T hT i eta
    intro alpha halpha
    by_contra hne
    exact h ⟨alpha, halpha, hne⟩
  have hretain : ∃ alpha ∈ relativeRoots i,
      latticePairing T alpha eta = 0 ∧ latticePairing T alpha zeta ≠ 0 := by
    by_contra h
    apply hlt.not_ge
    apply dynamicCentralizer_le_of_root_zero_imp dynamicConnected hT i eta zeta
    intro alpha halpha h0
    by_contra hne
    exact h ⟨alpha, halpha, h0, hne⟩
  obtain ⟨n, m, hn, hnonneg, beta, hbeta, hfbetane, hbeta0⟩ :=
    exists_integral_boundary_combination (hT.finite_relativeRoots i)
      (fun alpha => latticePairing T alpha zeta)
      (fun alpha => latticePairing T alpha eta) hzero hgne
  let mu : cocharacterLattice T := n • zeta + m • eta
  have hpair (alpha : characterLattice T) :
      latticePairing T alpha mu =
        n * latticePairing T alpha zeta + m * latticePairing T alpha eta := by
    simp only [mu, map_add, map_zsmul, smul_eq_mul]
  have hle : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) := by
    apply dynamicCentralizer_le_of_root_zero_imp dynamicConnected hT i zeta mu
    intro alpha halpha h0
    rw [hpair, h0, hzero alpha halpha h0]
    ring
  refine ⟨mu, ?_, ?_, ?_⟩
  · apply (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport
      dynamicConnected hT i zeta mu).mpr
    intro alpha halpha h0
    rw [hpair]
    exact hnonneg alpha halpha h0
  · refine lt_of_le_not_ge hle ?_
    intro hback
    have h := relativeRoot_pairing_eq_zero_of_centralizer_le
      hT i zeta mu hback hbeta ((hpair beta).trans hbeta0)
    exact hfbetane h
  · intro htop
    obtain ⟨alpha, halpha, heta0, hzetane⟩ := hretain
    have hle' : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ≤
        Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) := by
      intro U g _
      rw [htop]
      exact Subgroup.mem_top g
    have hmu0 := relativeRoot_pairing_eq_zero_of_centralizer_le
      hT i mu eta hle' halpha heta0
    rw [hpair, heta0, mul_zero, add_zero] at hmu0
    exact (mul_ne_zero (ne_of_gt hn) hzetane) hmu0

end Langlands.GroupScheme
