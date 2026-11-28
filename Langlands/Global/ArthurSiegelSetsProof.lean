import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.ArthurSiegelPartitionProof
import Langlands.Global.ArthurSiegelCoveringProof
import Langlands.Global.ArthurSiegelReductionProof
import Langlands.Global.ArthurTruncationIdempotenceProof
import Langlands.Global.ArthurIwasawaTruncationRapidDecayProof
import Langlands.Global.AdelicCompatibleIwasawaCompact
import Langlands.Global.AdelicSiegelSetupExistence
import Langlands.Global.IntegralIwasawaFamilyProof
import Langlands.Global.InfinitePlaceLeviIwasawaProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.StandardMinimalLeviStructure
import Langlands.Global.FinitePlaceIwasawaProof
import Langlands.Global.ArthurParabolicSpacesProof

/-! # The Siegel partition and truncation bundle

The proof constructs one maximal compact subgroup `K` with `P_0(𝔸) K = G(𝔸)`.
Its intersection with `P_0(𝔸)` commutes with the positive torus of every Siegel setup
for the fixed maximal split torus and generic cocharacter. The proof specializes Siegel
covering, both partition identities, constant-term vanishing, pointwise idempotence and
restricted rapid decay to this `K`. The partition identities follow from the
reduction-theoretic lemma used in Arthur 1978, §6. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors

set_option backward.isDefEq.respectTransparency false

/-- Finite-place Iwasawa existence gives a maximal compact subgroup `K` of `G(𝔸)` with
`P_0(𝔸) K = G(𝔸)` whose parabolic part commutes with the positive torus of every actual Siegel
setup for the same `T`, `i`, `ν`. The archimedean factors are Levi-compatible Iwasawa compacts,
which depend on `P_0` and its Levi only. -/
theorem exists_compatible_parabolicIwasawaCompact
    (hfinite : FinitePlaceGroupPoints.ParabolicIwasawaStatement.{u})
    (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    ∃ K : Subgroup (AdelicGroupPoints F G),
      IsParabolicIwasawaCompact F G (Standard.parabolicScheme i ν ∅)
          (Standard.parabolicHom i ν ∅) K ∧
        ∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
          IsSiegelAlgebraicSetup F G T i ν T₀ j → IsPositiveTorusCompatible F G T i ν T₀ j K := by
  have hp : IsParabolicSubgroup (Standard.parabolicHom i ν ∅) :=
    (Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal i ν
      genericMinimalParabolic hG hi hν).isParabolicSubgroup
  have hl : IsRationalLeviSubgroup (Standard.leviToParabolic i ν ∅) :=
    (standardMinimalLeviStructure F G T i ν hG hi hν).2.1
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
    hp.isClosedSubgroup
  have : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left
  obtain ⟨K₀, hK₀⟩ := IntegralIwasawaFamily.existenceStatement F G hG _ _ hp
  obtain ⟨Kloc, hKarch, hK⟩ := exists_leviCompatible_parabolicIwasawaCompact F G
    (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
    (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅)
    (InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement F G hG _ _ hp _ _ hl)
    (hfinite F G hG _ _ hp) K₀ hK₀
  exact ⟨_, hK, fun T₀ j hS =>
    isPositiveTorusCompatible_coordinateSubgroup F G T i ν T₀ j hS Kloc hKarch⟩

/-- Finite-place Iwasawa existence and the results for every compact Iwasawa subgroup
give `ArthurSiegelSetsStatement` using the witness of `exists_compatible_parabolicIwasawaCompact`. -/
theorem arthurSiegelSetsStatement_of_iwasawa
    (hfinite : FinitePlaceGroupPoints.ParabolicIwasawaStatement.{u})
    (hcover : IwasawaSiegelCoveringStatement.{u})
    (hpart : IwasawaSiegelPartitionStatement.{u})
    (hidem : IwasawaTruncationIdempotentStatement.{u})
    (hdecay : IwasawaTruncationRapidDecayStatement.{u}) :
    ArthurSiegelSetsStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν
  obtain ⟨K, hKP, hKc⟩ := exists_compatible_parabolicIwasawaCompact hfinite F G T i ν hG hi hν
  have hK := hKP.isIwasawaCompact
  refine ⟨K, hK, hKP.1, hKc, fun D hρ => ?_⟩
  obtain ⟨hpartition, hrelative⟩ := hpart F G T i ν hG hi hν D K hK hρ
  exact ⟨hcover F G T i ν hG hi hν K hK hρ, hidem F G T i ν hG hi hν D K hK hρ,
    hpartition, hrelative, hdecay F G T i ν hG hi hν D K hK hρ⟩

/-- **The Siegel partition and truncation bundle.** Arthur 1978, §6 and Lemma 6.4.
Arthur 2005, Theorem 8.1, Lemma 8.2, (8.1), Proposition 13.1(a),(b) and Proposition 13.2(a)
in the restricted form of `IsTruncationRapidDecay`. -/
theorem arthurSiegelSets : ArthurSiegelSetsStatement.{u} :=
  arthurSiegelSetsStatement_of_iwasawa FinitePlaceGroupPoints.parabolicIwasawaStatement
    iwasawaSiegelCovering
    (iwasawaSiegelPartitionStatement_of_reduction parabolicSpacesComparison iwasawaSiegelReduction)
    iwasawaTruncationIdempotent iwasawaTruncationRapidDecay

end Langlands.Global.ArthurTruncation
