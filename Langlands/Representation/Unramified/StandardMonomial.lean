import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Group.GL.CartanProof

/-! # Standard monomials in the spherical Hecke algebra and their triangularity -/

noncomputable section

namespace Langlands.Unramified

open Correspondence

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance monomialFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance monomialFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance monomialFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance monomialGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance monomialGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance monomialGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance monomialGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance monomialGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

/-- The uniformizer used by the standard diagonal elements. -/
abbrev standardUniformizer : F.Carrierˣ := F.canonicalTopologicalData.uniformizerUnit

/-- The diagonal torus element `diag(ϖ ^ ν 0, …, ϖ ^ ν r)` for the standard uniformizer. -/
abbrev standardTorus {r : ℕ} (ν : Fin (r + 1) → ℤ) : GeneralLinear (r + 1) F.Carrier :=
  GeneralLinear.Iwasawa.torus (standardUniformizer F) ν

/-- The double-coset element of `K ϖ^ν K` in the spherical corner. -/
abbrev torusHeckeElement {r : ℕ} (ν : Fin (r + 1) → ℤ) : SphericalHeckeAlgebra F r :=
  Hecke.HeckeAlgebra.Corner.doubleCoset (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r) (standardTorus F ν)

/-- The exponent of the monomial `∏ T_i ^ a i`: entry `j` is `∑_{i > j} a i`, so that
`∏ standardDiagonal i ^ a i = ϖ ^ monomialExponent a`. -/
def monomialExponent {r : ℕ} (a : Fin (r + 2) → ℕ) : Fin (r + 1) → ℤ :=
  fun j => ∑ i : Fin (r + 2), if j.val < i.val then (a i : ℤ) else 0

/-- The standard monomial `T_0 ^ a 0 * T_1 ^ a 1 * ⋯ * T_n ^ a n`. -/
def standardMonomial {r : ℕ} (a : Fin (r + 2) → ℕ) : SphericalHeckeAlgebra F r :=
  (List.ofFn fun i => standardHeckeElement F r i ^ a i).prod

/-- Triangularity of the standard monomials with respect to dominance: the support of
`∏ T_i ^ a i` lies in double cosets `K ϖ^ν K` with `ν` antitone, dominated by
`λ = monomialExponent a` (every tail sum of `ν` is at least that of `λ`, with the same
total), and its value at `ϖ^λ` is nonzero. -/
def StandardMonomialTriangularity : Prop :=
  ∀ (r : ℕ) (a : Fin (r + 2) → ℕ),
    (∀ x : GeneralLinear (r + 1) F.Carrier, standardMonomial F a x ≠ 0 →
      ∃ ν : Fin (r + 1) → ℤ, Antitone ν ∧
        x ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r) (standardTorus F ν) ∧
        (∀ k, GeneralLinear.Cartan.tailSum (monomialExponent a) k ≤
          GeneralLinear.Cartan.tailSum ν k) ∧
        ∑ j, ν j = ∑ j, monomialExponent a j) ∧
    standardMonomial F a (standardTorus F (monomialExponent a)) ≠ 0

end Langlands.Unramified
