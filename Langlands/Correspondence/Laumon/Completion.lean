import Langlands.Correspondence.Laumon.Traits
import Langlands.LocalField.LaurentSeries
import Langlands.Weil.Local.Assembly
import Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute

/-!
# Henselian end traits and their completions: the bridge (b2)

The fraction field `endField k` of the end trait is dense in `LaurentSeries k`, and its
separable generic closure `endGenericClosure k` is taken inside `SeparableClosure
(LaurentSeries k)`. Restriction of automorphisms gives `completionRestriction k`. This module
states that restriction is an isomorphism of topological absolute Galois groups (Katz 1986,
(1.4.8)), and that it matches the Library's inertia, residue map, Weil degree, wild inertia
and absolute upper ramification groups of `LaurentSeries k` with the corresponding structures
of the henselian field.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Henniart.Laumon

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

section Restriction

variable (k : Type u) [Field k]

/-- The separable generic closure is a separable closure of the end field. -/
instance endGenericClosure_isSepClosure : IsSepClosure (endField k) (endGenericClosure k) :=
  separableClosure.isSepClosure (endField k) (SeparableClosure (LaurentSeries k))

/-- The separable generic closure is Galois over the end field. -/
instance endGenericClosure_isGalois : IsGalois (endField k) (endGenericClosure k) :=
  IsSepClosure.isGalois

/-- The separable generic closure is normal over the end field. -/
instance endGenericClosure_normal : Normal (endField k) (endGenericClosure k) :=
  IsGalois.to_normal

/-- Restriction from the absolute Galois group of `LaurentSeries k`, for its separable closure
`SeparableClosure (LaurentSeries k)`, to that of the end field, for the separable closure
`endGenericClosure k` of the end field inside it. -/
def completionRestriction :
    Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k) →*
      Gal(endGenericClosure k/endField k) :=
  (AlgEquiv.restrictNormalHom (endGenericClosure k)).comp
    (AlgEquiv.restrictScalarsHom (endField k))

end Restriction

open Langlands.LocalGalois.SepClosed Langlands.Weil.Local.SepClosed
  Langlands.Ramification.Local in
/-- **Henselian and complete Galois groups.** For every field `k`, restriction
`completionRestriction k` is a homeomorphism; being a monoid homomorphism, it is an isomorphism
of topological groups between the absolute Galois groups of `LaurentSeries k` and of the end
field. -/
def HenselianCompletionGaloisStatement : Prop :=
  ∀ (k : Type u) [Field k], IsHomeomorph (completionRestriction k)

section HenselianLower

variable (k : Type u) [Field k] [Finite k]

open Langlands.LocalGalois.SepClosed in
/-- The `i`-th lower ramification test on the henselian elements of a finite Galois level `L` of
`LaurentSeries k`: for a uniformizer `ϖ` of the henselian elements of `L` (an element of
valuation less than one whose valuation is maximal among such elements), `g` moves every
henselian integer `b` of `L` by an element of valuation at most `v(ϖ)^(i+1)`, i.e. acts
trivially modulo the `(i+1)`-st power of the maximal ideal. The valuation is the Library's
`closureValuation`, the unique extension of the valuation of `LaurentSeries k`. -/
def HenselianLowerTest
    (L : FiniteGaloisIntermediateField (LaurentSeries k) (SeparableClosure (LaurentSeries k)))
    (i : ℕ) (g : Gal(endGenericClosure k/endField k)) : Prop :=
  ∃ ϖ : endGenericClosure k,
    (ϖ : SeparableClosure (LaurentSeries k)) ∈ L.toIntermediateField ∧
    closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ϖ < 1 ∧
    (∀ x : endGenericClosure k, (x : SeparableClosure (LaurentSeries k)) ∈ L.toIntermediateField →
      closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k)) x < 1 →
        closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k)) x ≤
          closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ϖ) ∧
    ∀ b : endGenericClosure k, (b : SeparableClosure (LaurentSeries k)) ∈ L.toIntermediateField →
      closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k)) b ≤ 1 →
        closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k))
            (((g b : endGenericClosure k) : SeparableClosure (LaurentSeries k)) - b) ≤
          closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ϖ ^ (i + 1)

end HenselianLower

open Langlands.LocalGalois.SepClosed Langlands.Weil.Local.SepClosed
  Langlands.Ramification.Local in
/-- **Ramification across the completion.** For a finite field `k`, restriction
`completionRestriction k` sends the Library's absolute inertia of `LaurentSeries k` onto the
automorphisms fixing the maximal unramified subextension `endUnramifiedField k`; it is
compatible with the Library's residue map through an identification of the constants
`endConstants k` with the algebraic closure of the residue field; an element of the local
Weil group of degree `n` acts on the constants as the `n`-th power of geometric Frobenius
`a ↦ a ^ (1/q)`; it sends wild inertia onto the inertia automorphisms that fix every `N`-th
root of the uniformizer for `N` prime to `p`; at every finite Galois level `L` of
`LaurentSeries k`, the Library's lower ramification groups of `L` are given by the congruences
`HenselianLowerTest` on the henselian integers of `L`; and the image of the absolute upper
ramification group of every level `v ≥ -1` consists of the automorphisms passing, at every
finite level `L`, the henselian lower test of index `⌈ψ_L(v)⌉` given by the inverse Herbrand
function of `L`. -/
def HenselianCompletionRamificationStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k],
    (absoluteInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k))).map
        (completionRestriction k) = (endUnramifiedField k).fixingSubgroup ∧
    (∃ φ : endConstants k ≃+* AlgebraicClosure (localResidueField (LaurentSeries k)),
      ∀ (σ : Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k)) (a b : endConstants k),
        (b : endGenericClosure k) = completionRestriction k σ a →
          AlgEquiv.toAlgHom
              (absoluteResidueHom (LaurentSeries k) (SeparableClosure (LaurentSeries k)) σ)
              (φ a) =
            φ b) ∧
    (∀ (w : localWeilGroup (LaurentSeries k) (SeparableClosure (LaurentSeries k)))
        (a : endConstants k),
      (completionRestriction k
          (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k)) w) a) ^
          (Nat.card k ^ (localDegreeInt (LaurentSeries k) (SeparableClosure (LaurentSeries k))
            w).toNat) =
        (a : endGenericClosure k) ^ (Nat.card k ^ (-localDegreeInt (LaurentSeries k)
          (SeparableClosure (LaurentSeries k)) w).toNat)) ∧
    (∀ τ : Gal(endGenericClosure k/endField k),
      τ ∈ (localWildInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k))).map
          (completionRestriction k) ↔
        τ ∈ (endUnramifiedField k).fixingSubgroup ∧
          ∀ (N : ℕ), ¬ ringChar k ∣ N → ∀ ϖ : endGenericClosure k,
            ϖ ^ N = algebraMap (endField k) (endGenericClosure k)
              ((endUniformizer k .zero : endRing k) : endField k) → τ ϖ = ϖ) ∧
    (∀ (L : FiniteGaloisIntermediateField (LaurentSeries k) (SeparableClosure (LaurentSeries k)))
        (σ : Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k)) (i : ℕ),
      absoluteFiniteRestriction (LaurentSeries k) (SeparableClosure (LaurentSeries k)) L σ ∈
          lowerRamificationGroup (localTopologicalData (LaurentSeries k) L) (LaurentSeries k) i ↔
        HenselianLowerTest k L i (completionRestriction k σ)) ∧
    ∀ (v : ℝ), -1 ≤ v → ∀ τ : Gal(endGenericClosure k/endField k),
      τ ∈ (localAbsoluteUpperRamificationGroup (LaurentSeries k)
          (SeparableClosure (LaurentSeries k)) v).map (completionRestriction k) ↔
        ∀ L : FiniteGaloisIntermediateField (LaurentSeries k) (SeparableClosure (LaurentSeries k)),
          ⌈herbrandPsi (localTopologicalData (LaurentSeries k) L) (LaurentSeries k) v⌉ < 0 ∨
            HenselianLowerTest k L
              (⌈herbrandPsi (localTopologicalData (LaurentSeries k) L) (LaurentSeries k) v⌉).toNat τ

end Langlands.Henniart.Laumon
