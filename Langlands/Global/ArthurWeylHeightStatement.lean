import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.Automorphic.GroupSchemeConstantTermConjugation

/-! # A uniform Weyl displacement bound for the minimal Iwasawa height

Arthur 1980, §1, proof of Lemma 1.1, p.91. For the minimal parabolic `P_0 = N_0 M_0` of a
connected reductive group over a number field, a compact subgroup `K` of `G(𝔸)` with
`P_0(𝔸)K = G(𝔸)` and its height `H_0`, a fundamental weight `ϖ ∈ Δ̂_0`, a rational point `w`
normalizing the maximal split torus with Weyl class `s`, every `v ∈ N_0(𝔸)` and every
`x ∈ G(𝔸)`:

`ϖ(H_0(x)) ≤ (sϖ)(H_0(w v x)) + B`,

with `B` depending on `w`, `ϖ` and `K` only. This is a derived form, for every such `K`, of the
nonnegativity of `ϖ(s⁻¹H_0(w_s v w_s⁻¹))` used in Arthur's proof; see the Markdown. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces
open Langlands.Automorphic.GroupSchemeFunctions (innerAdelicPoint)

/-- **A uniform Weyl displacement bound for the minimal Iwasawa height** (derived from Arthur
1980, proof of Lemma 1.1, p.91). Take the data of `IwasawaTruncationIdempotentStatement`: a
number field `F`, a connected reductive `G`, a maximal split torus `i : T → G`, a generic
cocharacter `ν` (fixing `P_0`), reflection data `D`, a compact subgroup `K` with
`P_0(𝔸)K = G(𝔸)` and the bijectivity `hρ`, with the height `H_0 = height hi hK hρ`. For every
simple relative root `β`, every fundamental weight `ϖ = ϖ_β` (`D.IsRealFundamentalWeight ν β ϖ`)
and every rational normalizing point `n` of `i`, with Weyl class `s` and adelic image `w`, there
is `B ≥ 0` such that for all `v ∈ N_0(𝔸)` and `x ∈ G(𝔸)`:
`⟨ϖ, H_0(x)⟩ ≤ ⟨sϖ, H_0(w v x)⟩ + B`. -/
def WeylHeightLowerBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (_hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
    ∀ (β : simpleRelativeRoots i ν) (ϖ : Vstar T), D.IsRealFundamentalWeight ν β ϖ →
    ∀ n : normalizerPoints i,
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ (v : AdelicSubgroupPoints.adelicPoints F G
            (SubgroupFunctor.range (Standard.unipotentHom i ν ∅)))
          (x : AdelicGroupPoints F G),
          pair T ϖ (height hi hK hρ x) ≤
            pair T (relativeWeylFullRealAction i (QuotientGroup.mk n : relativeWeylGroup i) ϖ)
                (height hi hK hρ
                  (innerAdelicPoint F G n.val * (v : AdelicGroupPoints F G) * x)) + B

end Langlands.Global.ArthurTruncation
