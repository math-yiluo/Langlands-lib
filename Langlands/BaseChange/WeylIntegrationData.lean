import Langlands.BaseChange.OrbitalIntegral
import Langlands.LocalField.ResidueNormalization
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Weyl integration data for `GL_n`

The adjoint discriminant, torus subgroups, integration domains, and common weight
for the ordinary and cyclically twisted formulas in Henniart–Lemaire, II.2.10.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u v

variable {F : Type u} [Field F] {n : ℕ}

/-- Conjugation on the matrix Lie algebra, with the orientation used in the Weyl
discriminant. -/
def linearAdjoint (γ : GeneralLinear n F) : Module.End F (Matrix (Fin n) (Fin n) F) :=
  (LinearMap.mulLeft F (γ : Matrix (Fin n) (Fin n) F)).comp
    (LinearMap.mulRight F ((γ⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F))

/-- The coefficient of `X^n` in the characteristic polynomial of `Ad(γ) - 1`.
This is `D_G(γ)` of Henniart–Lemaire, II.2.10. -/
noncomputable def weylDiscriminant (γ : GeneralLinear n F) : F :=
  (LinearMap.charpoly (linearAdjoint γ - LinearMap.id)).coeff n

/-- A maximal torus of `GL_n` described by its rational point group, the
centralizer of a regular semisimple matrix over `F`. -/
abbrev WeylTorus (F : Type u) [Field F] (n : ℕ) :=
  {T : Subgroup (GeneralLinear n F) // ∃ γ, IsRegularSemisimple γ ∧ glCentralizer γ = T}

namespace WeylTorus

/-- Conjugacy of the rational point subgroups by `GL_n(F)`. -/
def IsConjugate (T U : WeylTorus F n) : Prop :=
  ∃ g : GeneralLinear n F, T.val.map (MulAut.conj g).toMonoidHom = U.val

/-- Exactly one representative for each rational conjugacy class of maximal tori. -/
def IsRepresentativeSet (S : Set (WeylTorus F n)) : Prop :=
  ∀ T : WeylTorus F n, ∃! U : WeylTorus F n, U ∈ S ∧ IsConjugate T U

/-- The rational normalizer modulo the rational points of the torus. -/
abbrev RationalWeylGroup (T : WeylTorus F n) :=
  (Subgroup.normalizer (T.val : Set (GeneralLinear n F))) ⧸
    T.val.subgroupOf (Subgroup.normalizer (T.val : Set (GeneralLinear n F)))

/-- The torus over `E` given by the commutant in `GL_n(E)` of the image of its
rational point subgroup under base change. -/
def points (T : WeylTorus F n) (E : Type v) [CommRing E] [Algebra F E] :
    Subgroup (GeneralLinear n E) :=
  Subgroup.centralizer (T.val.map (baseChange F E n) : Set (GeneralLinear n E))

/-- The regular semisimple points of the torus over the base field. -/
def regularPoints (T : WeylTorus F n) : Set T.val :=
  {γ | IsRegularSemisimple (γ : GeneralLinear n F)}

/-- The image of the cyclic norm on the torus, expressed using equality in
`GL_n(E)` at the base change of a rational torus point. -/
def normImage (T : WeylTorus F n) {E : Type v} [CommRing E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (l : ℕ) : Set T.val :=
  {γ | ∃ δ : T.points E, cyclicNorm σ l (δ : GeneralLinear n E) =
      baseChange F E n (γ : GeneralLinear n F)}

/-- The common real Weyl factor on the rational torus. -/
noncomputable def integrationWeight [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (T : WeylTorus F n) (γ : T.val) : ℝ :=
  LocalField.residueNormalizedAbsoluteValue F (weylDiscriminant (γ : GeneralLinear n F)) /
    (Nat.card T.RationalWeylGroup : ℝ)

end WeylTorus

end Langlands.BaseChange
