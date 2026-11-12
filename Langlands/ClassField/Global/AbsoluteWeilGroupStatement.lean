import Langlands.ClassField.Global.AbsoluteLocalWeilMap
import Langlands.Automorphic.Unramified.AbsoluteWeilAssociation
import Langlands.Automorphic.AssociatedFactorStatement

/-! # Existence statements for the absolute global Weil group

Proposition definitions only, for the arithmetic fundamental-class family: existence of
Weil maps and of transitive systems of Weil maps (Artin–Tate XV, printed pp.168–179),
surjectivity of the projections of the projective limit onto the relative Weil groups
(Artin–Tate XV, Theorem 7 and its proof, printed pp.179–180), existence and conjugacy of
local-to-global Weil maps and the lifting of local-to-relative ones (Tate 1979, (1.6.1)),
and the factorization of continuous finite-dimensional representations through a finite
level (Tate 1979, §2.1). Nothing is proved here.
-/

namespace Langlands.ClassField.Global

open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

universe u uV

/-- Artin–Tate XV, printed p.177 with Theorems 1–3 (printed pp.168–171): for the
arithmetic fundamental-class family, every tower `F ⊆ K ⊆ L` of number fields with `K / F`
and `L / F` Galois has a Weil map `W_{L/F} → W_{K/F}`. -/
def WeilMapExistenceStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, RelativeWeilGroup.IsArithmeticClassFamily c →
    ∀ (h : FundamentalClass.Restriction c) (F K L : Type u) [Field F] [NumberField F]
      [Field K] [NumberField K] [Field L] [NumberField L] [Algebra F K] [Algebra F L]
      [Algebra K L] [IsScalarTower F K L] [IsGalois F K] [IsGalois F L],
      ∃ φ, RelativeWeilGroup.IsWeilMap c F K L h φ

/-- Artin–Tate XV, lemma on printed pp.178–179: for the arithmetic fundamental-class family,
the finite Galois layers of every extension `Ω / F` carry a transitive system of Weil
maps. -/
def WeilMapSystemExistenceStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, RelativeWeilGroup.IsArithmeticClassFamily c →
    ∀ (h : FundamentalClass.Restriction c) (F : Type u) [Field F] [NumberField F]
      (Ω : Type u) [Field Ω] [Algebra F Ω],
      Nonempty (WeilMapSystem c F Ω h)

/-- Artin–Tate XV, proof of Theorem 7, printed pp.179–180: for the arithmetic
fundamental-class family, the projection `W_F → W_{K/F}` of the projective limit of every
transitive system of Weil maps is surjective. -/
def WeilLevelSurjectiveStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, RelativeWeilGroup.IsArithmeticClassFamily c →
    ∀ (h : FundamentalClass.Restriction c) (F : Type u) [Field F] [NumberField F]
      (Ω : Type u) [Field Ω] [Algebra F Ω] (S : WeilMapSystem c F Ω h)
      (K : FiniteGaloisIntermediateField F Ω),
      Function.Surjective (S.toLevel K)

/-- Tate 1979, (1.6.1), existence: for the arithmetic fundamental-class family, every
transitive system of Weil maps and every finite place `v` of `F`, there is a local-to-global
Weil map `W_{F_v} → W_F`. -/
def LocalWeilMapExistenceStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, RelativeWeilGroup.IsArithmeticClassFamily c →
    ∀ (h : FundamentalClass.Restriction c) (F : Type u) [Field F] [NumberField F]
      (Ω : Type u) [Field Ω] [Algebra F Ω] (S : WeilMapSystem c F Ω h)
      (v : Langlands.Global.FinitePlace F),
      ∃ θ, S.IsLocalWeilMap v θ

/-- Tate 1979, (1.6.1), uniqueness, together with a change of embedding through
(1.4.4): for the arithmetic fundamental-class family, any two local-to-global Weil maps at
the same finite place are conjugate by an element of the projective limit `S.WeilGroup`. -/
def LocalWeilMapConjugacyStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, RelativeWeilGroup.IsArithmeticClassFamily c →
    ∀ (h : FundamentalClass.Restriction c) (F : Type u) [Field F] [NumberField F]
      (Ω : Type u) [Field Ω] [Algebra F Ω] (S : WeilMapSystem c F Ω h)
      (v : Langlands.Global.FinitePlace F) (θ θ'),
      S.IsLocalWeilMap v θ → S.IsLocalWeilMap v θ' →
        ∃ y : S.WeilGroup, θ' = S.conjMap y θ

/-- Derived from Tate 1979, (1.6.1): for the arithmetic fundamental-class family, every
local-to-relative Weil map `W_{F_v} → W_{K/F}` at a finite Galois layer `K` is, up to
conjugation in `W_{K/F}`, the composite of a local-to-global Weil map with the projection
`W_F → W_{K/F}`. -/
def LocalWeilMapLiftStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, RelativeWeilGroup.IsArithmeticClassFamily c →
    ∀ (h : FundamentalClass.Restriction c) (F : Type u) [Field F] [NumberField F]
      (Ω : Type u) [Field Ω] [Algebra F Ω] (S : WeilMapSystem c F Ω h)
      (v : Langlands.Global.FinitePlace F) (K : FiniteGaloisIntermediateField F Ω)
      (w : FinitePlacesAbove K v)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
      (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e ι →
        ∃ θ, S.IsLocalWeilMap v θ ∧
          ∃ x : RelativeWeilGroup c F K, ∀ g, S.toLevel K (θ g) = x * ι g * x⁻¹

/-- Tate 1979, §2.1: for the arithmetic fundamental-class family, every continuous
finite-dimensional complex representation of the projective limit `W_F` of a transitive
system of Weil maps is equivalent to the inflation of a continuous representation of some
relative Weil group `W_{K/F}`. -/
def WeilRepresentationFactorizationStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, RelativeWeilGroup.IsArithmeticClassFamily c →
    ∀ (h : FundamentalClass.Restriction c) (F : Type u) [Field F] [NumberField F]
      (Ω : Type u) [Field Ω] [Algebra F Ω] (S : WeilMapSystem c F Ω h)
      (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup), A.IsContinuous →
        ∃ (K : FiniteGaloisIntermediateField F Ω)
          (B : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)),
          B.IsContinuous ∧ Nonempty (FiniteRepresentation.Equiv A (S.inflate K B))

/-- The existence statements for the absolute global Weil group and its local-to-global
maps. -/
def AbsoluteWeilGroupStatement : Prop :=
  WeilMapExistenceStatement.{u} ∧ WeilMapSystemExistenceStatement.{u} ∧
    WeilLevelSurjectiveStatement.{u} ∧ LocalWeilMapExistenceStatement.{u} ∧
    LocalWeilMapConjugacyStatement.{u} ∧ LocalWeilMapLiftStatement.{u} ∧
    WeilRepresentationFactorizationStatement.{u, uV}

end Langlands.ClassField.Global
