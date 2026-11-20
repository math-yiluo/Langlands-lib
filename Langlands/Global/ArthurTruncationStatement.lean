import Langlands.Global.ArthurTruncation
import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicSiegelFiniteVolume

/-! # Statements on Arthur's truncation operator

Arthur 2005, §13, for the objects of `Langlands.Global.ArthurTruncation`:

* for every compact `K` with `P_0(𝔸)K = G(𝔸)`: the finiteness of the sums defining `Λ^T` (p.68,
  Arthur 1978 Lemma 5.1), `Λ^T(B_loc) ⊆ B_loc` with Proposition 13.1(c) (self-adjointness), and
  Proposition 13.3 with (13.10) (cancellation of the partial truncation operators);
* Proposition 13.1(a),(b) as the predicate `IsTruncationIdempotent` of one compact subgroup, and
  the statement that some maximal compact subgroup in the L1 class satisfies it. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

/-- **Finiteness of the inner sums** (Arthur 2005, p.68; Arthur 1978, Lemma 5.1). For every
compact `K` with `P_0(𝔸)K = G(𝔸)`, every standard parabolic subgroup `P ⊇ P_0`, every `T ∈ 𝔞_0`
and every `x ∈ G(𝔸)`, only finitely many `δ ∈ P(F) \ G(F)` have `τ̂_P(H_P(δx) − T) ≠ 0`. -/
def TruncationFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
    ∀ S ∈ (simpleFinset ν hG hi).powerset, ∀ (Tp : V T) (x : AdelicGroupPoints F G),
      {c : ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T))) |
        ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
          (height hi hK hρ (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * x)
            - Tp) ≠ 0}.Finite

/-- **`Λ^T` preserves `B_loc`, and Arthur 2005, Proposition 13.1(c).** For every compact `K` with
`P_0(𝔸)K = G(𝔸)` there is `C` such that for every `T ∈ 𝔞_0` with `β(T) > C` for all `β ∈ Δ_0`:
* for `φ ∈ B_loc(G(F) \ G(𝔸))`, `Λ^T φ ∈ B_loc(G(F) \ G(𝔸))`, and every constant term
  `∫_{N_1(F)\N_1(𝔸)} (Λ^T φ)(n x) dn` is a convergent integral;
* `(Λ^T φ₁, φ₂) = (φ₁, Λ^T φ₂)` for `φ₁ ∈ B_loc(G(F) \ G(𝔸))` and `φ₂` continuous with compact
  support modulo `G(F)`, both products being integrable on `G(F) \ G(𝔸)` for the quotient of
  Haar measure. -/
def TruncationSelfAdjointStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
    ∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
      (∀ φ : AdelicGroupPoints F G → ℂ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
        IsLocallyBoundedInvariant (rationalSubgroup F G) (truncation hG hi D hK hρ Tp φ) ∧
          ∀ S₁ ∈ (simpleFinset ν hG hi).powerset, ∀ x : AdelicGroupPoints F G,
            HasConstantTerm F i ν (S₁ : Set (characterLattice T))
              (truncation hG hi D hK hρ Tp φ) x) ∧
      ∀ φ₁ φ₂ : AdelicGroupPoints F G → ℂ,
        IsLocallyBoundedInvariant (rationalSubgroup F G) φ₁ →
        Continuous φ₂ → (∀ g ∈ rationalSubgroup F G, ∀ x, φ₂ (g * x) = φ₂ x) →
        (∃ Cs : Set (AdelicGroupPoints F G), IsCompact Cs ∧
          ∀ x, φ₂ x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ Cs) →
        let μG : Measure (RationalQuotient F G) := rationalQuotientHaarMeasure F G
        Integrable (fun y : RationalQuotient F G =>
            truncation hG hi D hK hρ Tp φ₁ y.out * (starRingEnd ℂ) (φ₂ y.out)) μG ∧
          Integrable (fun y : RationalQuotient F G =>
            φ₁ y.out * (starRingEnd ℂ) (truncation hG hi D hK hρ Tp φ₂ y.out)) μG ∧
          ∫ y, truncation hG hi D hK hρ Tp φ₁ y.out * (starRingEnd ℂ) (φ₂ y.out) ∂μG =
            ∫ y, φ₁ y.out * (starRingEnd ℂ) (truncation hG hi D hK hρ Tp φ₂ y.out) ∂μG

section Idempotence

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

/-- **Arthur 2005, Proposition 13.1(a),(b), for one compact subgroup `K`.** There is `C` such that
for every `T ∈ 𝔞_0` with `β(T) > C` for all `β ∈ Δ_0` and every `φ ∈ B_loc(G(F) \ G(𝔸))`:
* (a) for every standard `P_1 ⊇ P_0` and every `x ∈ G(𝔸)`, the constant term
  `∫_{N_1(F)\N_1(𝔸)} (Λ^T φ)(n x) dn` vanishes unless `ϖ(H_{P_1}(x) − T) ≤ 0` for every
  `ϖ ∈ Δ̂_{P_1}`;
* (b) `Λ^T (Λ^T φ) = Λ^T φ`. -/
def IsTruncationIdempotent (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) : Prop :=
  ∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
    ∀ φ : AdelicGroupPoints F G → ℂ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      (∀ S₁ ∈ (simpleFinset ν hG hi).powerset, ∀ x : AdelicGroupPoints F G,
        (∃ β ∈ simpleRelativeRoots i ν, β ∉ (S₁ : Set (characterLattice T)) ∧
          0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β
            (height hi hK hρ x - Tp)) →
        constantTerm F i ν (S₁ : Set (characterLattice T))
          (truncation hG hi D hK hρ Tp φ) x = 0) ∧
      truncation hG hi D hK hρ Tp (truncation hG hi D hK hρ Tp φ) =
        truncation hG hi D hK hρ Tp φ

end Idempotence

/-- **Arthur 2005, Proposition 13.1(a),(b), for a chosen suitable `K`** (Arthur 2005, p.24: "We
choose a suitable maximal compact subgroup `K` … with `G(𝔸) = P_0(𝔸)K`"). There is a compact
subgroup `K` of `G(𝔸)` with `P_0(𝔸)K = G(𝔸)`, maximal compact, whose elements in `P_0(𝔸)` commute
with the positive torus of every L1 Siegel setup, such that `IsTruncationIdempotent` holds for
every choice of reflection data `D` (with the bijectivity `hρ`). -/
def TruncationProjectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∃ (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K),
      IsMaximalCompactSubgroup F G K ∧
      (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        AdelicSiegelFactors.IsSiegelAlgebraicSetup F G T i ν T₀ j →
          AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K) ∧
      ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
        IsTruncationIdempotent hG hi D hK hρ

/-- **Arthur 2005, Proposition 13.3.** For every compact `K` with `P_0(𝔸)K = G(𝔸)` and every
`T ∈ 𝔞_0`:
* for `φ ∈ B_loc(G(F) \ G(𝔸))`, each inner sum has only finitely many nonzero terms and
  `∑_{P_1 ⊇ P_0} ∑_{δ ∈ P_1(F)\G(F)} Λ^{T,P_1} φ(δx) τ_{P_1}(H_{P_1}(δx) − T) = φ(x)`;
* more generally, for a standard `P` and `φ ∈ B_loc(P(F) \ G(𝔸))`, (13.10): the constant term
  along `P` converges, each inner sum has only finitely many nonzero terms, and
  `∑_{P_0 ⊆ P_1 ⊆ P} ∑_{δ ∈ P_1(F)\P(F)} Λ^{T,P_1} φ(δx) τ_{P_1}^P(H_{P_1}(δx) − T)
    = ∫_{N_P(F)\N_P(𝔸)} φ(nx) dn`. -/
def TruncationCancellationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)), ∀ Tp : V T,
      (∀ φ : AdelicGroupPoints F G → ℂ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
        ∀ x : AdelicGroupPoints F G,
          (∀ S₁ ∈ (simpleFinset ν hG hi).powerset,
            (Function.support fun c : ParabolicRationalCosets F
                (Standard.parabolicHom i ν (S₁ : Set (characterLattice T))) =>
              relativeTruncation hG hi D hK hρ S₁ Tp φ
                  (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
                (ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
                  (simpleRelativeRoots i ν)
                  (height hi hK hρ
                    (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * x) -
                    Tp) : ℂ)).Finite) ∧
          ∑ S₁ ∈ (simpleFinset ν hG hi).powerset,
            ∑' c : ParabolicRationalCosets F
                (Standard.parabolicHom i ν (S₁ : Set (characterLattice T))),
              relativeTruncation hG hi D hK hρ S₁ Tp φ
                  (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
                (ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
                  (simpleRelativeRoots i ν)
                  (height hi hK hρ
                    (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * x) -
                    Tp) : ℂ) = φ x) ∧
      ∀ SP ∈ (simpleFinset ν hG hi).powerset, ∀ φ : AdelicGroupPoints F G → ℂ,
        IsLocallyBoundedInvariant
          (parabolicRationalImage (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) φ →
        ∀ x : AdelicGroupPoints F G,
          HasConstantTerm F i ν (SP : Set (characterLattice T)) φ x ∧
          (∀ S₁ ∈ SP.powerset,
            (Function.support fun c : RelativeCosets (F := F) (i := i) (ν := ν)
                (S₁ : Set (characterLattice T)) (SP : Set (characterLattice T)) =>
              relativeTruncation hG hi D hK hρ S₁ Tp φ
                  ((((Quotient.out c : parabolicRationalSubgroup F
                    (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                      rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
                (ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
                  (SP : Set (characterLattice T))
                  (height hi hK hρ
                    ((((Quotient.out c : parabolicRationalSubgroup F
                      (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                        rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) : ℂ)).Finite) ∧
          ∑ S₁ ∈ SP.powerset,
            ∑' c : RelativeCosets (F := F) (i := i) (ν := ν) (S₁ : Set (characterLattice T))
                (SP : Set (characterLattice T)),
              relativeTruncation hG hi D hK hρ S₁ Tp φ
                  ((((Quotient.out c : parabolicRationalSubgroup F
                    (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                      rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
                (ArthurRelative.tau hG hi ν D (S₁ : Set (characterLattice T))
                  (SP : Set (characterLattice T))
                  (height hi hK hρ
                    ((((Quotient.out c : parabolicRationalSubgroup F
                      (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                        rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) : ℂ) =
            constantTerm F i ν (SP : Set (characterLattice T)) φ x

/-- The statements of this module. -/
def ArthurTruncationStatement : Prop :=
  TruncationFinitenessStatement.{u} ∧ TruncationSelfAdjointStatement.{u} ∧
    TruncationProjectionStatement.{u} ∧ TruncationCancellationStatement.{u}

end Langlands.Global.ArthurTruncation
