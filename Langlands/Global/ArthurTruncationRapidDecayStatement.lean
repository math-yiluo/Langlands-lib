import Langlands.Automorphic.GroupSchemeNormOneSmooth
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.Global.ArthurNormOneTruncation
import Langlands.Global.ArthurSiegelSets
import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicSiegelFiniteVolume

/-! # Arthur's norm-one truncation estimates

Arthur 2005, Proposition 13.2(a),(b) on `G(F) \ G(𝔸_F)¹`. Use the actual embedded
archimedean norm-one group, a fixed open compact finite level for (b), and the
Siegel sets and closed-representation height from the L1 objects. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ContDiff ENNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces
open Langlands.Automorphic.GroupSchemeFunctions AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {d e N : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}

/-- The uniform temperedness of Arthur 2005, p.70: a fixed smooth level and one real
exponent for all left-invariant derivatives on the norm-one group. -/
def IsNormOneUniformlyTempered (A : NormOneLieAtlas F G hsmooth e)
    (rho : MatrixRepresentation G (Fin N)) (f : normOneSubgroup F G → ℂ) : Prop :=
  (∃ (K₀ : Subgroup (FiniteAdelicGroupPoints F G))
    (hc : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))),
    IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)) ∧ IsNormOneCr A ∞ K₀ hc f) ∧
  ∃ p : ℝ, 0 ≤ p ∧ ∀ D : NormOneDifferentialWord e, ∃ B : ℝ, 0 ≤ B ∧
    ∀ x : normOneSubgroup F G,
      ‖normOneDifferential A D f x‖ ≤ B * RepresentationGrowth.adelicSourceNorm F G rho x ^ p

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

/-- **Proposition 13.2(a),(b) for given atlas, height, compact and parameter.** The family
bound is pointwise on the norm-one part of the given Siegel set, with the same bound
for every member of that part, i.e. the supremum estimate (13.5)–(13.6). -/
def IsNormOneTruncationEstimate (A : NormOneLieAtlas F G hsmooth e)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (rho : MatrixRepresentation G (Fin N))
    (Tp : V T) : Prop :=
  (∀ f : normOneSubgroup F G → ℂ, IsNormOneUniformlyTempered A rho f →
    IsRapidlyDecreasing hG hi hK hρ rho (normOneExtend (normOneTruncation hG hi D hK hρ Tp f))) ∧
  ∀ C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅),
    C.compactSubgroup = K → ∀ (T₁ : V T) (n n₀ : ℕ), 0 < n → 0 < n₀ →
    ∀ (K₀ : Subgroup (FiniteAdelicGroupPoints F G))
      (hc : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))),
      IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)) →
      ∃ (r : ℕ) (ops : Finset (NormOneDifferentialWord e)) (B : NNReal),
        0 < r ∧ (∀ X ∈ ops, X.OrderLE r) ∧
        ∀ (Ω : Type v) [MeasurableSpace Ω] (m : Measure Ω)
          (φ : Ω → normOneSubgroup F G → ℂ),
          (∀ o, IsNormOneCr A r K₀ hc (φ o)) →
          Measurable (fun p : Ω × normOneSubgroup F G => φ p.1 p.2) →
          ∀ x : normOneSubgroup F G, (x : AdelicGroupPoints F G) ∈
              siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁ →
            Measurable (fun o => normOneTruncation hG hi D hK hρ Tp (φ o) x) ∧
            ENNReal.ofReal (RepresentationGrowth.adelicSourceNorm F G rho x ^ (n : ℝ)) *
                (∫⁻ o, ENNReal.ofReal ‖normOneTruncation hG hi D hK hρ Tp (φ o) x‖ ∂m) ≤
              (B : ℝ≥0∞) * ⨆ y : normOneSubgroup F G,
                ENNReal.ofReal (RepresentationGrowth.adelicSourceNorm F G rho y ^ (-(n₀ : ℝ))) *
                  ∑ X ∈ ops, ∫⁻ o, ENNReal.ofReal ‖normOneDifferential A X (φ o) y‖ ∂m

/-- **Arthur 2005, Proposition 13.2.** Assert the embedded Lie geometry of the actual
infinite norm-one subgroup and a single suitable maximal compact. For all closed matrix
realizations and all sufficiently regular truncation parameters, (a) and (b) hold. The
norm-one Lie atlas is produced, not added as an external premise. -/
def TruncationRapidDecayStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∃ (e : ℕ) (A : NormOneLieAtlas F G hG.smoothDimension_spec e)
      (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K),
      IsMaximalCompactSubgroup F G K ∧
      (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j → IsPositiveTorusCompatible F G T i ν T₀ j K) ∧
      ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅))
        {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
        ∃ c : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) →
          IsNormOneTruncationEstimate.{u, v} A hG hi D hK hρ rho Tp

end Langlands.Global.ArthurTruncation
