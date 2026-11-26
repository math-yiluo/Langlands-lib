import Langlands.Global.ArthurSiegelSetsStatement

/-! # Siegel sets and truncation for every compact Iwasawa subgroup

Arthur 1978, §6, pp.941–942; Arthur 2005, §8 and §13; Arthur 1980, §1. The predicates of
`Langlands.Global.ArthurSiegelSetsStatement` and `Langlands.Global.ArthurTruncationStatement`
are asserted here for **every** compact subgroup `K` with `P_0(𝔸)K = G(𝔸)`, the constants
depending on `K`. The module also defines the predicate `IsSiegelReductionLemma` of one compact
subgroup: the result from reduction theory quoted by Arthur 1978, p.941. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors

section Predicates

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

/-- **The reduction-theoretic lemma of Arthur 1978, p.941, for one compact subgroup `K`**
(from the proof of Langlands, *On the functional equations satisfied by Eisenstein series*,
Lemma 2.12). For all compact factor data `ω` (with the compact subgroup `K`) and `T_1 ∈ 𝔞_0` there
is `c` such that every `T ∈ 𝔞_0` with `β(T) > c` for every `β ∈ Δ_0` has the following property:
if `P_1 ⊆ P` are standard (`Δ_0^{P_1} = S₁ ⊆ SP = Δ_0^P`), `x ∈ G(𝔸)` and `δ ∈ P(F)` with
`x, δx ∈ S^P(T_1, ω)`, and `α(H_0(x) − T) > 0` for every `α ∈ Δ_0^P ∖ Δ_0^{P_1}`, then
`δ ∈ P_1(F)`. Arthur's p.941 sentence prints `S^{P_1}(T_0, ω)`; the Siegel set `S^P` is the one
in which he applies the result in the proof of Lemma 6.4 (p.942). -/
def IsSiegelReductionLemma (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) : Prop :=
  ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (T₁ : V T), C.compactSubgroup = K →
    ∃ c : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) →
      ∀ SP ∈ (simpleFinset ν hG hi).powerset, ∀ S₁ ∈ SP.powerset,
        ∀ x δ : AdelicGroupPoints F G,
          δ ∈ parabolicRationalImage
            (Standard.parabolicHom i ν (SP : Set (characterLattice T))) →
          x ∈ siegelSet hi hK hρ C SP T₁ → δ * x ∈ siegelSet hi hK hρ C SP T₁ →
          (∀ α ∈ SP, α ∉ S₁ → 0 < eval T α (height hi hK hρ x - Tp)) →
          δ ∈ parabolicRationalImage
            (Standard.parabolicHom i ν (S₁ : Set (characterLattice T)))

end Predicates

/-- **Siegel covering for every compact Iwasawa subgroup** (Arthur 1978, §6, p.941: "By the
properties of Siegel sets we can fix `ω` and `T_0` so that for any `P_1`,
`G(𝔸) = P_1(ℚ) S^{P_1}(T_0, ω)`"; for `P_1 = G`, Arthur 2005, Theorem 8.1). For every compact
`K` with `P_0(𝔸)K = G(𝔸)` there are compact factor data `ω` with the compact subgroup `K` and
`T_1 ∈ 𝔞_0` such that `G(𝔸) = P_1(F) S^{P_1}(T_1, ω)` for every standard `P_1`. -/
def IwasawaSiegelCoveringStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∀ (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
      (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
      ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
        (T₁ : V T), C.compactSubgroup = K ∧ IsSiegelCovering hG hi hK hρ C T₁

/-- **The reduction-theoretic lemma for every compact Iwasawa subgroup** (Arthur 1978, p.941;
Langlands, Lemma 2.12): `IsSiegelReductionLemma` holds for every compact `K` with
`P_0(𝔸)K = G(𝔸)`. -/
def IwasawaSiegelReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∀ (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
      (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
      IsSiegelReductionLemma hG hi hK hρ

/-- **Arthur 2005, Lemma 8.2 and (8.1); Arthur 1978, Lemma 6.4, for every compact Iwasawa
subgroup**: `IsSiegelPartition` and `IsRelativeSiegelPartition` hold for every compact `K` with
`P_0(𝔸)K = G(𝔸)` and all reflection data. -/
def IwasawaSiegelPartitionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
      IsSiegelPartition hG hi D hK hρ ∧ IsRelativeSiegelPartition hG hi D hK hρ

/-- **Arthur 2005, Proposition 13.1(a),(b); Arthur 1980, Lemma 1.1, for every compact Iwasawa
subgroup**: `IsTruncationIdempotent` holds for every compact `K` with `P_0(𝔸)K = G(𝔸)` and all
reflection data. -/
def IwasawaTruncationIdempotentStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
      IsTruncationIdempotent hG hi D hK hρ

/-- **Arthur 2005, Proposition 13.2(a) in the restricted form of `IsTruncationRapidDecay`;
Arthur 1980, Lemma 1.4, for every compact Iwasawa subgroup**: `IsTruncationRapidDecay` holds for
every compact `K` with `P_0(𝔸)K = G(𝔸)` and all reflection data. -/
def IwasawaTruncationRapidDecayStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
      IsTruncationRapidDecay hG hi D hK hρ

/-- The five statements of this module. -/
def ArthurSiegelSetsIwasawaStatement : Prop :=
  IwasawaSiegelCoveringStatement.{u} ∧ IwasawaSiegelReductionStatement.{u} ∧
    IwasawaSiegelPartitionStatement.{u} ∧ IwasawaTruncationIdempotentStatement.{u} ∧
      IwasawaTruncationRapidDecayStatement.{u}

end Langlands.Global.ArthurTruncation
