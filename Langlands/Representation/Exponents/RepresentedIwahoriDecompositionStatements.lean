import Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements
import Langlands.Representation.Exponents.SplitComponentOppositeContractionStatement
import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Smooth.Definitions

/-! # Compact open subgroups with an Iwahori decomposition along an arbitrary parabolic

Statements only. Renard 2026, V.5.2 (ii) (printed p.123 / PDF p.129) for the notion of
Iwahori decomposition, VI.6.1 Théorème (printed p.176 / PDF p.182) and VI.9.1 Théorème
(printed p.195 / PDF p.201). The parabolic data are those of the published
`GeneralizedJacquetContractingRangeStatement`: actual rational parabolics `P = MN` and
`P̄ = M N̄` with the same Levi and `P(F) ∩ P̄(F) = M(F)`. A compact open subgroup `K` of
`G(F)` has an Iwahori decomposition along `P` when `K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))`;
no contraction property is assumed.

* `RepresentedIwahoriContractionStatement` (derived): for such `K` and a split component
  `A` of `M` with a compatible root presentation, `A^{++} = {t ∈ A(F) | |α(t)|_F < 1 for
  α ∈ Δ(P)}` is nonempty, and for every `t₀ ∈ A^{++}` all sufficiently large powers of `t₀`
  satisfy the published Iwahori contraction conditions `Jacquet.IsIwahoriContraction`
  for `(N(F), M(F), N̄(F))`.
* `RepresentedJacquetLemmaStatement` (VI.6.1 Théorème): for such `K` and every admissible
  complex representation `V`, the projection `V → V_N` maps `V^K` onto `(V_N)^{K_M}`.
* `RepresentedGeneralizedJacquetLemmaStatement` (VI.9.1 Théorème): the same surjectivity
  for every smooth complex representation.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Derived from Renard V.5.2 and the first step of the proofs of VI.6.1 and VI.9.1
("On choisit alors `t ∈ C_A^{++}`"). For actual rational parabolics `P = MN` and
`P̄ = M N̄` with the same Levi and `P(F) ∩ P̄(F) = M(F)`, every compact open `K` with
`K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))`, and every split component `a : A → M` with a
compatible root presentation of `P` and restricted simple roots `Δ(P)`:

* there is `t₀ ∈ A(F)` with `|α(t₀)|_F < 1` for every `α ∈ Δ(P)`;
* for every such `t₀` there is `r₀` such that, for every `r ≥ r₀`, the image of `t₀ ^ r`
  in `G(F)` satisfies `Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F)`. -/
def RepresentedIwahoriContractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
        (∀ x ∈ K, ∃ l ∈ K.toSubgroup ⊓ pointImage (nbar ≫ pbar),
          ∃ y ∈ K.toSubgroup ⊓ pointImage (m ≫ p),
            ∃ z ∈ K.toSubgroup ⊓ pointImage (n ≫ p), x = l * y * z) →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
          (pres : ParabolicRootPresentation p m a),
          let Δ : Set (characterLattice A) :=
            (fun α => pres.data.f ≫ α) ''
              (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
          let incG : rationalPoints A.toGrp →* rationalPoints G :=
            rationalPoints.map (a ≫ m ≫ p)
          (∃ t₀ : rationalPoints A.toGrp,
              ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t₀ < 1) ∧
            ∀ t₀ : rationalPoints A.toGrp,
              (∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t₀ < 1) →
              ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
                Jacquet.IsIwahoriContraction K (pointImage (n ≫ p)) (pointImage (m ≫ p))
                  (pointImage (nbar ≫ pbar)) (incG (t₀ ^ r))

/-- Renard VI.6.1, Théorème (Jacquet's lemma), for an arbitrary actual rational parabolic.
For actual rational parabolics `P = MN` and `P̄ = M N̄` with the same Levi and
`P(F) ∩ P̄(F) = M(F)`, every compact open `K` with
`K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))` and every admissible complex representation `V` of
`G(F)`, the Jacquet quotient map `V → V_N` sends `V^K` onto the `K ∩ M(F)`-fixed vectors
of the Jacquet module. -/
def RepresentedJacquetLemmaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
        (∀ x ∈ K, ∃ l ∈ K.toSubgroup ⊓ pointImage (nbar ≫ pbar),
          ∃ y ∈ K.toSubgroup ⊓ pointImage (m ≫ p),
            ∃ z ∈ K.toSubgroup ⊓ pointImage (n ≫ p), x = l * y * z) →
        ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
          (ρ : Representation ℂ (rationalPoints G) V), Langlands.IsAdmissible ρ →
          Function.Surjective
            (Jacquet.fixedJacquetMap ρ (pointImage (n ≫ p)) (pointImage (m ≫ p))
              (pointImage_le_normalizer p m n hn) K.toSubgroup)

/-- Renard VI.9.1, Théorème (generalized Jacquet lemma), for an arbitrary actual rational
parabolic. Same data as `RepresentedJacquetLemmaStatement`, with every smooth (not
necessarily admissible) complex representation `V` of `G(F)`: the Jacquet quotient map
`V → V_N` sends `V^K` onto the `K ∩ M(F)`-fixed vectors of the Jacquet module. -/
def RepresentedGeneralizedJacquetLemmaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
        (∀ x ∈ K, ∃ l ∈ K.toSubgroup ⊓ pointImage (nbar ≫ pbar),
          ∃ y ∈ K.toSubgroup ⊓ pointImage (m ≫ p),
            ∃ z ∈ K.toSubgroup ⊓ pointImage (n ≫ p), x = l * y * z) →
        ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
          (ρ : Representation ℂ (rationalPoints G) V), IsSmooth ρ →
          Function.Surjective
            (Jacquet.fixedJacquetMap ρ (pointImage (n ≫ p)) (pointImage (m ≫ p))
              (pointImage_le_normalizer p m n hn) K.toSubgroup)

end Langlands.Aubert.General.RepresentedParabolic
