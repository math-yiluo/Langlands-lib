import Langlands.LocalFactor.EpsilonOneStatement
import Langlands.LocalFactor.CommonClosureWeilDeligne

/-!
# Tate's `ε₁` over coefficient fields of characteristic zero

Tate (1979), the paragraph after (3.6.11): in the nonarchimedean case `ε₁(V, ψ) ∈ Kˣ`
is defined for `V` and `ψ` over any field `K` of characteristic zero (an open subgroup
of inertia acting trivially on `V`, and `ψ` trivial on some `π^n O`), in a unique way
such that `ε₁(V^α, ψ^α) = ε₁(V, ψ)^α` for every field homomorphism `α : K → K'` and
such that `ε₁` is the old `ε₁` of (3.6.10) when `K = ℂ`. So defined, it is inductive
in degree zero for every such `K`, and (3.6.11) gives it on rank-one representations.

No coefficient-field `ε₁` is constructed here. An assignment is any unit-valued
function on the inputs over every intermediate field of the common closure and every
characteristic-zero field in one universe; the clauses are propositions about every
supplied local-constant system. Conjugates along field homomorphisms, and the
comparison with complex representations, are described relationally.
-/

noncomputable section

universe uF uV uK uK' uG uA uB

namespace Langlands.LocalFactor.EpsilonOneCoefficient

open CommonClosure VirtualRepresentation

section Conjugate

variable {K : Type uK} {K' : Type uK'} [Field K] [Field K'] {G : Type uG} [Monoid G]

/-- `B` is a conjugate `A^α = K' ⊗_(α, K) A` of `A` along the field homomorphism
`α : K → K'`: an `α`-semilinear intertwiner maps some basis of `A` onto a basis of
`B`. -/
def IsConjugate (α : K →+* K') (A : FiniteRepresentation.{uK, uG, uA} K G)
    (B : FiniteRepresentation.{uK', uG, uB} K' G) : Prop :=
  ∃ f : A →ₛₗ[α] B,
    (∀ (g : G) (v : A), f (A.representation g v) = B.representation g (f v)) ∧
      ∃ (n : ℕ) (b : Module.Basis (Fin n) K A) (b' : Module.Basis (Fin n) K' B),
        ∀ i, f (b i) = b' i

end Conjugate

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section Inputs

variable {E : Extension F} {K : Type uK} [Field K]

/-- Tate's condition on `V`: some open subgroup of the inertia subgroup of `W_E` acts
trivially. -/
def TrivialOnOpenInertia (A : FiniteRepresentation.{uK, uF, uA} K (weilSubgroup F E)) :
    Prop :=
  ∃ U : Subgroup (CommonClosureWeilDeligne.inertia F E),
    IsOpen (U : Set (CommonClosureWeilDeligne.inertia F E)) ∧
      ∀ u ∈ U, A.representation (u : weilSubgroup F E) = 1

/-- Tate's condition on `ψ`: a nontrivial `K`-valued additive character of `E`, trivial
on some fractional ideal; `additiveLattice n` is `π^(-n) O`. -/
def IsAdmissibleCharacter (ψ : AddChar E.field K) : Prop :=
  (∃ x, ψ x ≠ 1) ∧ ∃ n : ℤ, ∀ x ∈ (fieldData F E).additiveLattice n, ψ x = 1

/-- Tate's `n(ψ)` for a `K`-valued character: the largest `n` such that `ψ` is trivial
on `π^(-n) O`. -/
def AdditiveConductorAt (ψ : AddChar E.field K) (n : ℤ) : Prop :=
  IsGreatest {m : ℤ | ∀ x ∈ (fieldData F E).additiveLattice m, ψ x = 1} n

/-- Tate's `a(χ)` for a `K`-valued character of `Eˣ`: the least `a` such that `χ` is
trivial on `U^a`, where `U⁰ = Oˣ`. -/
def ConductorAt (χ : E.fieldˣ →* Kˣ) (a : ℕ) : Prop :=
  IsLeast {b : ℕ | ∀ u ∈ (fieldData F E).principalUnits b, χ u = 1} a

/-- `A` is the rank-one representation of `W_E` over `K` attached to `χ : Eˣ → Kˣ`
through the supplied reciprocity component. -/
def IsCharacterLine (e : ReciprocityFamily F) (χ : E.fieldˣ →* Kˣ)
    (A : FiniteRepresentation.{uK, uF, uA} K (weilSubgroup F E)) : Prop :=
  letI := (fieldData F E).topology
  A.rank = 1 ∧ ∀ (g : weilSubgroup F E) (v : A),
    A.representation g v = ((χ (reciprocityUnits F e E g) : Kˣ) : K) • v

end Inputs

section Nested

variable (E L : Extension F) (h : E.field ≤ L.field) {K : Type uK} [Field K]

/-- Induction from `W_L` to `W_E` over `K`: restriction along the rebracketing of `W_L`
as a subgroup of `W_E`, followed by finite-index induction, as in
`CommonClosure.inducedRepresentation`. -/
def induced (A : FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F L)) :
    FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F E) :=
  FiniteRepresentation.induce ((weilSubgroup F L).subgroupOf (weilSubgroup F E))
    (FiniteRepresentation.restrict (nestedWeilEquiv F E L h : _ →ₜ* _).toMonoidHom A)

/-- The `K`-valued additive character `ψ ∘ Tr_(L/E)` of `L`. -/
def traceAddChar (ψ : AddChar E.field K) : AddChar L.field K :=
  ψ.compAddMonoidHom
    (@Algebra.trace E.field L.field _ _ (IntermediateField.inclusion h).toAlgebra).toAddMonoidHom

end Nested

/-- An unvalidated unit-valued `ε₁` over every intermediate field `E` and every field
`K` of characteristic zero in the universe `uK`, on `K`-valued additive characters of
`E` and finite-dimensional representations of `W_E` over `K`. Values on inputs that
violate Tate's conditions are unconstrained. -/
abbrev Assignment :=
  ∀ (E : Extension F) (K : Type uK) [Field K] [CharZero K],
    AddChar E.field K → FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F E) → Kˣ

/-- `ε₁(V^α, ψ^α) = ε₁(V, ψ)^α` for every homomorphism `α : K → K'` of fields of
characteristic zero, where `ψ^α = α ∘ ψ` and `B` is a conjugate of `A` along `α`. -/
def Compatible (ε₁ : Assignment.{uF, uK} F) : Prop :=
  ∀ (E : Extension F) (K K' : Type uK) [Field K] [CharZero K] [Field K'] [CharZero K']
    (α : K →+* K') (ψ : AddChar E.field K)
    (A : FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F E))
    (B : FiniteRepresentation.{uK, uF, max uF uK} K' (weilSubgroup F E)),
    IsAdmissibleCharacter F ψ → TrivialOnOpenInertia F A → IsConjugate α A B →
      (ε₁ E K' (α.toMonoidHom.compAddChar ψ) B : K') = α (ε₁ E K ψ A : K)

/-- `ε₁` is the old `ε₁` of (3.6.10) when the coefficient field is `ℂ`: for every field
`K` with an isomorphism `κ : K ≃ ℂ`, `κ(ε₁(V, ψ))` is the supplied constant at a Haar
measure giving the ring of integers volume one, evaluated at the `κ`-conjugates of
`ψ` and of `V`. -/
def Normalized (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (ε₁ : Assignment.{uF, uK} F) : Prop :=
  ∀ (E : Extension F) (K : Type uK) [Field K] [CharZero K] (κ : K ≃+* ℂ)
    (ψ : AddChar E.field K)
    (A : FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F E)),
    IsAdmissibleCharacter F ψ → TrivialOnOpenInertia F A →
    letI := (fieldData F E).topology
    ∀ ψ' : AdditiveCharacter F E, (∀ y : E.field, ψ'.complex y = κ (ψ y)) →
    ∀ μ : HaarMeasure F E, (fieldData F E).integerVolume μ = 1 →
    ∀ (A' : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
      (hA' : A'.IsContinuous), IsConjugate κ.toRingHom A A' →
      κ (ε₁ E K ψ A : K) =
        (ε E ψ' μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E)
          ⟨A', hA'⟩) : ℂ)

/-- Two assignments agree on every input satisfying Tate's conditions. -/
def AgreeOnAdmissible (ε₁ ε₁' : Assignment.{uF, uK} F) : Prop :=
  ∀ (E : Extension F) (K : Type uK) [Field K] [CharZero K] (ψ : AddChar E.field K)
    (A : FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F E)),
    IsAdmissibleCharacter F ψ → TrivialOnOpenInertia F A → ε₁ E K ψ A = ε₁' E K ψ A

/-- Additivity over `K` (Tate (2.3.2)): `ε₁(V) = ε₁(V') ε₁(V'')` for every short exact
sequence `0 → V' → V → V'' → 0` of representations satisfying Tate's condition. -/
def Additive (ε₁ : Assignment.{uF, uK} F) : Prop :=
  ∀ (E : Extension F) (K : Type uK) [Field K] [CharZero K] (ψ : AddChar E.field K)
    (A B C : FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F E))
    (f : A.representation.IntertwiningMap B.representation)
    (g : B.representation.IntertwiningMap C.representation),
    IsAdmissibleCharacter F ψ → TrivialOnOpenInertia F A → TrivialOnOpenInertia F B →
      TrivialOnOpenInertia F C → FiniteRepresentation.IsShortExact f g →
      ε₁ E K ψ B = ε₁ E K ψ A * ε₁ E K ψ C

/-- Inductivity in degree zero over `K` (Tate (2.3.2)), on the generators `[A] - [B]`
with `rank A = rank B` of the degree-zero virtual representations of `W_L`: for
`E ⊆ L`, `ε₁(Ind A, ψ) ε₁(Ind B, ψ)⁻¹ = ε₁(A, ψ ∘ Tr) ε₁(B, ψ ∘ Tr)⁻¹`. -/
def InductiveInDegreeZero (ε₁ : Assignment.{uF, uK} F) : Prop :=
  ∀ (E L : Extension F) (h : E.field ≤ L.field) (K : Type uK) [Field K] [CharZero K]
    (ψ : AddChar E.field K)
    (A B : FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F L)),
    IsAdmissibleCharacter F ψ → TrivialOnOpenInertia F A → TrivialOnOpenInertia F B →
      A.rank = B.rank →
      ε₁ E K ψ (induced F E L h A) * (ε₁ E K ψ (induced F E L h B))⁻¹ =
        ε₁ L K (traceAddChar F E L h ψ) A * (ε₁ L K (traceAddChar F E L h ψ) B)⁻¹

/-- Tate (3.6.11) over `K`: if `A` corresponds to `χ : Eˣ → Kˣ` of conductor exponent
`a = a(χ)`, `n = n(ψ)` and `ord c = n + a`, then
`ε₁(A, ψ) = χ(c) q^n ∑_(u ∈ Oˣ mod U^a) χ⁻¹(u) ψ(u/c)`, the sum running over any system
of representatives. The printed display omits `ψ` and the inverse on `χ(u)`; this is
the formula that follows from (3.2.6.1) and (3.2.6.2), as Tate says. -/
def RankOneFormula (e : ReciprocityFamily F) (ε₁ : Assignment.{uF, uK} F) : Prop :=
  ∀ (E : Extension F) (K : Type uK) [Field K] [CharZero K] (χ : E.fieldˣ →* Kˣ)
    (ψ : AddChar E.field K)
    (A : FiniteRepresentation.{uK, uF, max uF uK} K (weilSubgroup F E)) (n : ℤ) (a : ℕ),
    IsAdmissibleCharacter F ψ → AdditiveConductorAt F ψ n → ConductorAt F χ a →
    IsCharacterLine F e χ A →
    ∀ c : E.fieldˣ, (fieldData F E).ord (c : E.field) = n + a →
    ∀ r : EpsilonOne.UnitQuotient (fieldData F E) a → (fieldData F E).principalUnits 0,
      (∀ x, (r x : EpsilonOne.UnitQuotient (fieldData F E) a) = x) →
      (ε₁ E K ψ A : K) =
        (χ c : K) * ((fieldData F E).residueCardinality : K) ^ n *
          ∑ᶠ x : EpsilonOne.UnitQuotient (fieldData F E) a,
            (χ (r x : E.fieldˣ) : K)⁻¹ * ψ (((r x : E.fieldˣ) : E.field) / (c : E.field))

end Langlands.LocalFactor.EpsilonOneCoefficient

namespace Langlands.LocalFactor

open CommonClosure EpsilonOneCoefficient

/-- Tate (1979), the paragraph after (3.6.11), for every p-adic field `F` and every
supplied local-constant system `ε` on its common closure: some assignment of `ε₁`
over the characteristic-zero fields of the universe `uK` is compatible with every
field homomorphism and agrees with the old `ε₁` over `ℂ`; any two such assignments
agree on every input satisfying Tate's conditions; and every such assignment is
additive, inductive in degree zero and given on rank-one representations by
(3.6.11). -/
def EpsilonOneCoefficientStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F), NonabelianSystem.IsSystem F e ε →
    (∃ ε₁ : EpsilonOneCoefficient.Assignment.{uF, uK} F,
      Compatible F ε₁ ∧ Normalized F ε ε₁) ∧
    (∀ ε₁ ε₁' : EpsilonOneCoefficient.Assignment.{uF, uK} F,
      Compatible F ε₁ → Normalized F ε ε₁ → Compatible F ε₁' → Normalized F ε ε₁' →
        AgreeOnAdmissible F ε₁ ε₁') ∧
    ∀ ε₁ : EpsilonOneCoefficient.Assignment.{uF, uK} F,
      Compatible F ε₁ → Normalized F ε ε₁ →
        Additive F ε₁ ∧ InductiveInDegreeZero F ε₁ ∧ RankOneFormula F e ε₁

end Langlands.LocalFactor
