import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.AdditiveDual
import Langlands.Group.GL.CompactOpen
import Langlands.HarmonicAnalysis.Basic
import Langlands.Representation.Category.ClassInvariants
import Langlands.Representation.Category.Twist
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # Normalized level and containment of strata for `GL_n` over a p-adic field

Bushnell (1987), (3.1)–(3.3), printed pp. 196–197, and Bushnell–Kutzko (1993), Introduction,
printed pp. 8–10: the normalized level `ℓ(π) = min {m / e(𝔄) : π^{U^{m+1}(𝔄)} ≠ 0}` of an
irreducible admissible representation `π` of `GL_n(K)`, and "`π` contains the stratum
`[𝔄, m, m - 1, b]`". The lattice chains, the lattices `𝔓^j = End^j(𝓛)`, the unit groups
`U^j(𝔄(𝓛))` and the period `e(𝓛)` are those of `Langlands.BushnellKutzko.LatticeChain`.

Throughout, `K : PadicField p` carries its canonical topology and valuation
(`K.canonicalTopologicalData`) and `GL_n(K)` its canonical topology
(`K.canonicalGeneralLinearTopology n`). Subgroups of `Aut(V)`, `V = Fin n → K`, are moved to
`GeneralLinear n K.Carrier` along Mathlib's `Matrix.GeneralLinearGroup.toLin`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u uK uV

section Instances

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- An additive character `ψ_F` of `K` has *level one* if it is trivial on `𝔭_K` but not on
`𝔬_K` (Bushnell–Kutzko 1993, Introduction, printed p. 8, and notation, printed p. 19). These are
the hypotheses on `ψ_F` in `AdditiveDualityStatement`. -/
def IsLevelOne (ψ : AddChar F.Carrier ℂ) : Prop :=
  (∀ a ∈ 𝓂[F.Carrier], ψ (a : F.Carrier) = 1) ∧ ∃ a : 𝒪[F.Carrier], ψ (a : F.Carrier) ≠ 1

/-- The image in `GL_n(K)` of the unit group `U^j(𝔄(𝓛))`: the matrices `g` whose linear map
`Matrix.GeneralLinearGroup.toLin g` lies in `U^j(𝔄(𝓛))`. -/
def unitSubgroup {n : ℕ} (𝓛 : LatticeChain 𝒪[F.Carrier] F.Carrier (Fin n → F.Carrier))
    (j : ℕ) : Subgroup (GeneralLinear n F.Carrier) :=
  (𝓛.unitFiltration j).comap Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem mem_unitSubgroup {n : ℕ} (𝓛 : LatticeChain 𝒪[F.Carrier] F.Carrier (Fin n → F.Carrier))
    (j : ℕ) (g : GeneralLinear n F.Carrier) :
    g ∈ unitSubgroup F 𝓛 j ↔ Matrix.GeneralLinearGroup.toLin g ∈ 𝓛.unitFiltration j :=
  Iff.rfl

/-- The set of normalized levels attained by a class `a` of irreducible admissible
representations of `GL_n(K)`: the rationals `m / e(𝓛)` with `𝓛` an `𝔬_K`-lattice chain in
`K^n`, `m : ℕ`, and `a` having a nonzero vector fixed by `U^{m+1}(𝔄(𝓛))`
(Bushnell 1987, (3.3), printed p. 196). -/
def normalizedLevelValues (n : ℕ)
    (a : SmoothDualClass.{0, u, uV} (k := ℂ) (G := GeneralLinear n F.Carrier)) : Set ℚ :=
  {x | ∃ (𝓛 : LatticeChain 𝒪[F.Carrier] F.Carrier (Fin n → F.Carrier)) (m : ℕ),
    x = (m : ℚ) / 𝓛.period ∧ SmoothDualClass.HasFixedVector (unitSubgroup F 𝓛 (m + 1)) a}

/-- `x` is the normalized level `ℓ(a)` of the class `a`: the least element of
`normalizedLevelValues F n a` (operator route note, §4.4). -/
def IsNormalizedLevel (n : ℕ)
    (a : SmoothDualClass.{0, u, uV} (k := ℂ) (G := GeneralLinear n F.Carrier)) (x : ℚ) : Prop :=
  IsLeast (normalizedLevelValues F n a) x

/-- The class `a` contains the stratum `[𝔄(𝓛), m, m - 1, b]` with respect to `ψ`
(Bushnell–Kutzko 1993, Introduction, printed pp. 8–10; Bushnell 1987, (3.1), printed p. 196):
`m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)`, and some representative of `a` has a nonzero vector `v` with
`g • v = ψ(tr(b (g - 1))) v` for every `g` in the image of `U^m(𝔄(𝓛))`. The conditions
`m ≥ 1` and `b ∈ 𝔓^{-m}(𝓛)` are conjuncts. -/
def ContainsStratum (n : ℕ) (ψ : AddChar F.Carrier ℂ)
    (a : SmoothDualClass.{0, u, uV} (k := ℂ) (G := GeneralLinear n F.Carrier))
    (𝓛 : LatticeChain 𝒪[F.Carrier] F.Carrier (Fin n → F.Carrier)) (m : ℕ)
    (b : Module.End F.Carrier (Fin n → F.Carrier)) : Prop :=
  1 ≤ m ∧ b ∈ 𝓛.endFiltration (-(m : ℤ)) ∧
    ∃ A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := GeneralLinear n F.Carrier),
      Quotient.mk _ A = a ∧ ∃ v : A.obj, v ≠ 0 ∧
        ∀ g ∈ unitSubgroup F 𝓛 m,
          A.obj.representation g v =
            elementCharacter (traceCharacter ψ) b (Matrix.GeneralLinearGroup.toLin g) • v

/-- The character `χ ∘ det` of `GL_n(K)` attached to a quasicharacter `χ` of `K^×` has an open
kernel, so twisting by it preserves smoothness. -/
theorem isOpen_ker_determinantCharacter (n : ℕ)
    (χ : HarmonicAnalysis.Quasicharacter F.Carrier) :
    IsOpen ((χ.toMonoidHom.comp (GeneralLinear.determinant (n := n))).ker :
      Set (GeneralLinear n F.Carrier)) := by
  let := F.canonicalGeneralLinearNonarchimedean n
  exact isOpen_ker_of_continuous_complex_character _
    (χ.continuous.comp (F.canonicalTopologicalData.generalLinearDeterminant n).continuous)

end Instances

end Langlands.BushnellKutzko
