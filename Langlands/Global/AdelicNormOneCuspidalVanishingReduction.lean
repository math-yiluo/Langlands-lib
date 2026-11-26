import Langlands.Global.AdelicNormOneCuspidalSeparationStatement
import Langlands.Global.AdelicLeviFibreCuspidality
import Langlands.Global.AdelicParabolicCuspidalVanishingReduction
import Langlands.Global.AdelicMaximalCompactFactors

/-! # The parabolic criterion from norm-one cuspidal separation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Assembly

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (fam : StandardParabolicFamily F G)
  (P : StandardIndex F G fam.i fam.ν)

omit [NumberField F] in
private theorem isCompact_leviInfiniteCompact
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hK : IsCompact (Kinf : Set (InfiniteAdelicGroupPoints F G))) :
    IsCompact (fam.leviInfiniteCompact Kinf P : Set (InfiniteAdelicGroupPoints F (fam.M P))) := by
  let j := fam.l P ≫ fam.p P
  let : IsClosedImmersion j.hom.hom.left := (fam.isCompatible P).levi.isClosedSubgroup.comp
    (fam.isCompatible P).parabolic.isClosedSubgroup
  let : T2Space (NumberField.InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  exact ((fam.M P).isClosedEmbedding_affinePointsTarget G
    (CommAlgCat.of F (NumberField.InfiniteAdeleRing F)) j).isCompact_preimage hK

/-- The norm-one separation on connected reductive groups suffices for
separation on the relatively cuspidal part of every parabolic quotient. -/
theorem adelicCuspidalAlongSeparation_of_normOne (hSep : NormOneCuspidalSeparationStatement.{u})
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hK : IsCompact (Kinf : Set (InfiniteAdelicGroupPoints F G)))
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hρ : IsClosedSubgroup rho) :
    fam.AdelicCuspidalAlongSeparation Kinf rho := by
  intro P f hf hc hTest
  funext g
  change f g = 0
  rw [← fam.leviFibre_one P f g]
  let M := fam.M P
  let j := fam.l P ≫ fam.p P
  let mMap := map F M G j
  have hM := (fam.isCompatible P).levi.isConnectedReductive
  have hj : IsClosedSubgroup j := (fam.isCompatible P).levi.isClosedSubgroup.comp
    (fam.isCompatible P).parabolic.isClosedSubgroup
  refine hSep F M hM (fam.leviSmooth P) (fam.leviInfiniteCompact Kinf P) (j ≫ rho)
    (isCompact_leviInfiniteCompact fam P hK) hN (hj.comp hρ) (fam.leviFibre P f g)
    (fam.isLeftInvariantUnder_leviFibre P hf.1 g) (fam.continuous_leviFibre P hf.2.1 g)
    (fam.hasModerateGrowthFunction_leviFibre hN P hf.2.2 g)
    (fam.leviFibreCuspidality P f hf.2.1 hf.1 hc g) ?_
  intro ψ hψ hψC a
  have h := hTest ψ ⟨hψ, hψC⟩ (mMap a * g)
  have heq : normOneCuspidalPairingIntegrand (fam.leviFibre P f g) ψ a =
      fam.leviPairingIntegrand P f (mMap a * g) ψ := by
    funext x
    simp only [normOneCuspidalPairingIntegrand, StandardParabolicFamily.leviFibre,
      StandardParabolicFamily.leviPairingIntegrand, map_mul, mul_assoc, mMap, j, M]
  rw [heq]
  exact h

end Assembly

/-- The norm-one cuspidal case implies the full parabolic vanishing criterion. -/
def NormOneCuspidalVanishingReductionStatement : Prop :=
  NormOneCuspidalSeparationStatement.{u} → ParabolicCuspidalVanishingStatement.{u}

theorem normOneCuspidalVanishingReduction : NormOneCuspidalVanishingReductionStatement.{u} := by
  intro hSep
  apply parabolicCuspidalVanishingReduction
  intro F _ _ G _ _ _ fam K hK _ N rho hN hClosed
  exact adelicCuspidalAlongSeparation_of_normOne fam hSep hK.isMaximalCompact_comap_ofInfinite.1
    rho hN hClosed

end Langlands.Global
