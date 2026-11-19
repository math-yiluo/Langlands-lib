import Langlands.Correspondence.HenniartTwistSwanStatement
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport
import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Langlands.ClassFieldTheory.Local.Norms
import Langlands.ClassFieldTheory.Local.PrimeRamifiedDifferentStatement
import Langlands.Weil.Local.ExtensionResidue
import Langlands.Weil.Local.ExtensionGalois
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Local cyclic base change of prime degree for supercuspidal classes

Cyclic prime-degree steps `M/L` of p-adic fields, their numerical invariants,
Herbrand function, Galois action on supercuspidal classes and norm characters,
and the weak local base-change premise (I3) of Option II of the operator's
numerical LLC route note (§6.4, Theorem `thm:BC`; §7.1 item 6).
Definitions and a proposition only.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uV

open Langlands.Correspondence

namespace Numerical

/-- A cyclic extension `M/L` of prime degree of p-adic fields: `top` is an
extension of `base` through `embedding`, Galois for the induced algebra
structure, with Galois group of prime order. -/
structure CyclicPrimeStep (p : ℕ) [Fact p.Prime] where
  /-- The base field `L`. -/
  base : PadicField.{uK} p
  /-- The extension field `M`. -/
  top : PadicField.{uK} p
  /-- The embedding of `L` into `M` over `ℚ_p`. -/
  embedding : base.Carrier →ₐ[Padic p] top.Carrier
  /-- `M/L` is Galois for the algebra structure given by `embedding`. -/
  isGalois :
    letI := Weil.Local.extensionAlgebra base top embedding
    IsGalois base.Carrier top.Carrier
  /-- The Galois group of `M/L` has prime order. -/
  card_prime :
    letI := Weil.Local.extensionAlgebra base top embedding
    (Nat.card (top.Carrier ≃ₐ[base.Carrier] top.Carrier)).Prime

namespace CyclicPrimeStep

variable {p : ℕ} [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)

/-- The algebra structure of `M` over `L` given by the embedding. -/
abbrev algebra : Algebra S.base.Carrier S.top.Carrier :=
  Weil.Local.extensionAlgebra S.base S.top S.embedding

/-- The Galois group `Γ = Gal(M/L)`. -/
abbrev Gal : Type uK :=
  letI := S.algebra
  S.top.Carrier ≃ₐ[S.base.Carrier] S.top.Carrier

/-- The degree `ℓ = [M : L]`. -/
def degree : ℕ :=
  Weil.Local.extensionDegree S.base S.top S.embedding

/-- The residue degree `f(M|L)`. -/
def residueDegree : ℕ :=
  Weil.Local.extensionResidueDegree S.base S.top S.embedding

/-- The ramification index `e(M|L)`: the normalized `M`-valuation of a
uniformizer of `L`. -/
def ramificationIndex : ℕ :=
  (S.top.canonicalTopologicalData.ord
    (S.embedding S.base.canonicalTopologicalData.uniformizer)).toNat

/-- The different exponent `d(M|L)`: the exponent `d` with
`𝔇(𝒪_M/𝒪_L) = 𝔭_M ^ d`, for Mathlib's different ideal of the canonical
integer rings. -/
def differentExponent : ℕ :=
  letI := S.algebra
  haveI := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  let TL := S.base.canonicalTopologicalData
  let TM := S.top.canonicalTopologicalData
  letI := TL.topology
  letI := TL.valuativeRel
  letI := TL.localField
  letI := TM.topology
  letI := TM.valuativeRel
  letI := TM.localField
  letI := PadicField.TopologicalData.relativeIntegerAlgebra TL TM
  letI := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := S.top) TL
  haveI := PadicField.TopologicalData.relativeIntegerFieldTower (E := S.top) TL
  haveI := PadicField.TopologicalData.relativeIntegerTower TL TM
  haveI := PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree TL TM
  sInf {d : ℕ | differentIdeal TL.Integers TM.Integers =
    IsLocalRing.maximalIdeal TM.Integers ^ d}

/-- The wild part `c(M|L) = d(M|L) - e(M|L) + 1` of the different exponent,
computed in `ℤ`. -/
def wildDifferentExponent : ℤ :=
  (S.differentExponent : ℤ) - S.ramificationIndex + 1

/-- The Herbrand function `ψ_{M/L}`: the Library's `herbrandPsi` of `M` over
`L`, for the canonical realization of `M` and the algebra structure of the
embedding. -/
def herbrandPsi : ℝ → ℝ :=
  letI := S.algebra
  haveI := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  Ramification.Padic.herbrandPsi S.top.canonicalTopologicalData S.base.Carrier

/-- An element of `Γ`, viewed as an automorphism of `M` over `ℚ_p`. -/
def galoisAutomorphism (g : S.Gal) : S.top.Carrier ≃ₐ[Padic p] S.top.Carrier :=
  letI := S.algebra
  haveI := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  g.restrictScalars (Padic p)

/-- The Galois conjugate `Π ↦ Π^g` on rank-`k + 1` supercuspidal classes of `M`,
with `Π^g(x) = Π(g(x))`, `g` applied to every matrix entry of `x ∈ GL_{k+1}(M)`. -/
def galoisConjugate (g : S.Gal) (k : ℕ) :
    SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat ≃
      SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat :=
  letI := S.top.canonicalTopologicalData.topology
  GeneralLinear.SupercuspidalClass.fieldPullbackEquiv
    (S.galoisAutomorphism g).toRingEquiv
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv S.top S.top
      (S.galoisAutomorphism g))
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv S.top S.top
      (S.galoisAutomorphism g).symm)
    (k.succPNat : ℕ)

/-- `Π ↦ Π^g` on supercuspidal classes of `M` of any positive rank, keeping the rank. -/
def galoisConjugateSigma (g : S.Gal)
    (ρ : Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) :
    Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat :=
  ⟨ρ.1, S.galoisConjugate g ρ.1 ρ.2⟩

/-- The `Γ`-orbit `{Π₁^g : g ∈ Γ}` of a rank-`k₁ + 1` class, as the multiset
indexed by `Γ`. -/
def galoisOrbit {k₁ : ℕ} (τ₁ : SupercuspidalAutomorphicClass.{uK, uV} S.top k₁.succPNat) :
    Multiset (Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) :=
  letI : Fintype S.Gal :=
    @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero S.card_prime.ne_zero)
  (Finset.univ : Finset S.Gal).val.map fun g => ⟨k₁, S.galoisConjugate g k₁ τ₁⟩

/-- The set `Ξ` of characters of `L^×` trivial on the norm group `N_{M/L}(M^×)`. -/
def normCharacters : Set (QuasiCharacter S.base) :=
  letI := S.algebra
  haveI := Weil.Local.extensionAlgebra_finiteDimensional S.base S.top S.embedding
  letI := S.base.canonicalTopologicalData.topology
  {η | LocalClassField.normSubgroup S.base.Carrier S.top.Carrier ≤ η.toMonoidHom.ker}

end CyclicPrimeStep

/-- A candidate cyclic base change: for every rank `k + 1`, a map from
supercuspidal classes over `L` to multisets of supercuspidal classes over `M`
of arbitrary positive ranks (meant as the cuspidal support of the base change). -/
abbrev CyclicBaseChangeMap {p : ℕ} [Fact p.Prime] (S : CyclicPrimeStep.{uK} p) :=
  ∀ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat →
    Multiset (Σ k' : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top k'.succPNat)

/-- The Swan exponent of a supercuspidal class: its conductor, read through
`WithTop.untopD` (formerly `WithTop.untop'`) with default `0`, minus the rank, with truncated subtraction. -/
def supercuspidalSwanExponent {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {k : ℕ}
    (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) : ℕ :=
  WithTop.untopD 0 (Langlands.Henniart.Numerical.conductor K π) - (k + 1)

/-- The weak form of local cyclic base change (route note §7.1 item 6):
(W1) rank and `Γ`-invariance, (W2) invariance under `Ξ`, (W3a)–(W3c) the
fibres and the image (BC3), and (W4) the conductor identity (BC4). -/
def IsWeakCyclicBaseChange {p : ℕ} [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S) : Prop :=
  ∀ k : ℕ,
    (∀ π : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat,
      -- (W1)
      ((Ch k π).map fun ρ => ρ.1 + 1).sum = k + 1 ∧
      (∀ g : S.Gal, (Ch k π).map (S.galoisConjugateSigma g) = Ch k π) ∧
      -- (W2)
      (∀ η ∈ S.normCharacters,
        Ch k (supercuspidalCharacterTwist S.base k η π) = Ch k π) ∧
      -- (W3a)
      ((∀ η ∈ S.normCharacters, η ≠ 1 → supercuspidalCharacterTwist S.base k η π ≠ π) →
        (∃ τ : SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat,
          Ch k π = {⟨k, τ⟩}) ∧
        ∀ π' : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat,
          Ch k π' = Ch k π ↔
            ∃ η ∈ S.normCharacters, π' = supercuspidalCharacterTwist S.base k η π) ∧
      -- (W3b)
      ((∀ η ∈ S.normCharacters, supercuspidalCharacterTwist S.base k η π = π) →
        S.degree ∣ k + 1 ∧
        (∃ (k₁ : ℕ) (τ₁ : SupercuspidalAutomorphicClass.{uK, uV} S.top k₁.succPNat),
          k₁ + 1 = (k + 1) / S.degree ∧
          (∀ g : S.Gal, g ≠ 1 → S.galoisConjugate g k₁ τ₁ ≠ τ₁) ∧
          Ch k π = S.galoisOrbit τ₁) ∧
        ∀ π' : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat,
          Ch k π' = Ch k π → π' = π) ∧
      -- (W4)
      (S.residueDegree : ℤ) *
          ((Ch k π).map fun ρ => (supercuspidalSwanExponent S.top ρ.2 : ℤ)).sum =
        (∑ᶠ η ∈ S.normCharacters,
            (supercuspidalSwanExponent S.base
              (supercuspidalCharacterTwist S.base k η π) : ℤ)) -
          (S.residueDegree : ℤ) * S.wildDifferentExponent * ((k : ℤ) + 1)) ∧
    -- (W3c)
    (∀ τ : SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat,
      (∀ g : S.Gal, S.galoisConjugate g k τ = τ) →
        ∃ π : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat,
          Ch k π = {⟨k, τ⟩}) ∧
    (∀ (k₁ : ℕ) (τ₁ : SupercuspidalAutomorphicClass.{uK, uV} S.top k₁.succPNat),
      S.degree ∣ k + 1 → k₁ + 1 = (k + 1) / S.degree →
        (∀ g : S.Gal, g ≠ 1 → S.galoisConjugate g k₁ τ₁ ≠ τ₁) →
          ∃ π : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat,
            Ch k π = S.galoisOrbit τ₁)

end Numerical

/-- Input (I3) of Option II of the operator's numerical LLC route note, in the
weak form of its §7.1 item 6: every cyclic prime-degree step of p-adic fields
has a weak cyclic base change on supercuspidal classes. -/
def LocalCyclicBaseChangeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : Numerical.CyclicPrimeStep.{uK} p),
    ∃ Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S, Numerical.IsWeakCyclicBaseChange S Ch

end Langlands.Henniart
