import Langlands.LocalFactor.Ramification.Galois
import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Finite-Galois conductor inflation and common-refinement statements

These proposition definitions use actual p-adic fields, algebra towers,
Galois restriction maps, and the published rational conductor sums.
-/

namespace Langlands.Ramification.Padic

universe uK uE uE' uL uV uW

/-- Inflation preserves the actual inertia-fixed subspace and its codimension. -/
def FiniteGaloisInertiaInflationStatement
  {p : ℕ} [Fact p.Prime]
  {E : PadicField.{uE} p} {L : PadicField.{uL} p}
  (TE : E.TopologicalData) (TL : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K E.Carrier] [Algebra K L.Carrier] [Algebra E.Carrier L.Carrier]
  [IsScalarTower (Padic p) K E.Carrier]
  [IsScalarTower (Padic p) K L.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier]
  [IsScalarTower K E.Carrier L.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] : Prop :=
  ∀ [IsGalois K E.Carrier] [IsGalois K L.Carrier]
    (ρ : Representation ℂ (E.Carrier ≃ₐ[K] E.Carrier) V),
    let π := AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E.Carrier
    fixedVectors (ρ.comp π) (inertia TL K) = fixedVectors ρ (inertia TE K) ∧
    fixedCodimension (L.Carrier ≃ₐ[K] L.Carrier) (ρ.comp π) (inertia TL K) =
      fixedCodimension (E.Carrier ≃ₐ[K] E.Carrier) ρ (inertia TE K)

/-- Both actual rational conductor sums are invariant under Galois inflation. -/
def FiniteGaloisConductorInflationStatement
  {p : ℕ} [Fact p.Prime]
  {E : PadicField.{uE} p} {L : PadicField.{uL} p}
  (TE : E.TopologicalData) (TL : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K E.Carrier] [Algebra K L.Carrier] [Algebra E.Carrier L.Carrier]
  [IsScalarTower (Padic p) K E.Carrier]
  [IsScalarTower (Padic p) K L.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier]
  [IsScalarTower K E.Carrier L.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] : Prop :=
  ∀ [IsGalois K E.Carrier] [IsGalois K L.Carrier]
    (ρ : Representation ℂ (E.Carrier ≃ₐ[K] E.Carrier) V),
    let π := AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E.Carrier
    artinConductor TL K (ρ.comp π) = artinConductor TE K ρ ∧
    swanConductor TL K (ρ.comp π) = swanConductor TE K ρ

/-- Two finite Galois presentations agree when their inflations to an actual
common finite Galois refinement are equivalent representations. -/
def FiniteGaloisConductorCommonRefinementStatement
  {p : ℕ} [Fact p.Prime]
  {E : PadicField.{uE} p} {E' : PadicField.{uE'} p} {L : PadicField.{uL} p}
  (TE : E.TopologicalData) (TE' : E'.TopologicalData) (_TL : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K E.Carrier] [Algebra K E'.Carrier] [Algebra K L.Carrier]
  [Algebra E.Carrier L.Carrier] [Algebra E'.Carrier L.Carrier]
  [IsScalarTower (Padic p) K E.Carrier]
  [IsScalarTower (Padic p) K E'.Carrier]
  [IsScalarTower (Padic p) K L.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier]
  [IsScalarTower (Padic p) E'.Carrier L.Carrier]
  [IsScalarTower K E.Carrier L.Carrier]
  [IsScalarTower K E'.Carrier L.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] : Prop :=
  ∀ [IsGalois K E.Carrier] [IsGalois K E'.Carrier] [IsGalois K L.Carrier]
    (ρ : Representation ℂ (E.Carrier ≃ₐ[K] E.Carrier) V)
    (σ : Representation ℂ (E'.Carrier ≃ₐ[K] E'.Carrier) W),
    let π := AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E.Carrier
    let π' := AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E'.Carrier
    ∀ (_e : Representation.Equiv (ρ.comp π) (σ.comp π')),
      artinConductor TE K ρ = artinConductor TE' K σ ∧
      swanConductor TE K ρ = swanConductor TE' K σ

/-- The complete inflation and common-refinement family, with independent
universes for the base, the three extension fields, and both vector spaces. -/
def FiniteGaloisConductorInflationAndIndependenceStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime]
    (E : PadicField.{uE} p) (L : PadicField.{uL} p)
    (TE : E.TopologicalData) (TL : L.TopologicalData)
    (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K E.Carrier] [Algebra K L.Carrier] [Algebra E.Carrier L.Carrier]
    [IsScalarTower (Padic p) K E.Carrier]
    [IsScalarTower (Padic p) K L.Carrier]
    [IsScalarTower (Padic p) E.Carrier L.Carrier]
    [IsScalarTower K E.Carrier L.Carrier]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    FiniteGaloisInertiaInflationStatement TE TL K (V := V) ∧
    FiniteGaloisConductorInflationStatement TE TL K (V := V)) ∧
  (∀ (p : ℕ) [Fact p.Prime]
    (E : PadicField.{uE} p) (E' : PadicField.{uE'} p) (L : PadicField.{uL} p)
    (TE : E.TopologicalData) (TE' : E'.TopologicalData) (TL : L.TopologicalData)
    (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K E.Carrier] [Algebra K E'.Carrier] [Algebra K L.Carrier]
    [Algebra E.Carrier L.Carrier] [Algebra E'.Carrier L.Carrier]
    [IsScalarTower (Padic p) K E.Carrier]
    [IsScalarTower (Padic p) K E'.Carrier]
    [IsScalarTower (Padic p) K L.Carrier]
    [IsScalarTower (Padic p) E.Carrier L.Carrier]
    [IsScalarTower (Padic p) E'.Carrier L.Carrier]
    [IsScalarTower K E.Carrier L.Carrier]
    [IsScalarTower K E'.Carrier L.Carrier]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W],
    FiniteGaloisConductorCommonRefinementStatement TE TE' TL K (V := V) (W := W))

end Langlands.Ramification.Padic
