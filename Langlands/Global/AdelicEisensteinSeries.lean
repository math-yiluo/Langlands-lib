import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.AdelicComplexParameters

/-! # Eisenstein series on actual adelic points

Bernstein–Lapid §2.2 (2.1): for a parabolic `p : P → G`, a compact `K` with
`P(𝔸)K = G(𝔸)`, a function `φ` on `G(𝔸)` and `λ ∈ X^*(P) ⊗ ℂ`,
`φ_λ(g) = φ(g) m_P(g)^λ` with `m_P(g)^λ = exp ⟨λ, H_P(g)⟩`, and
`E(g, φ, λ) = ∑_{γ ∈ P(F) \ G(F)} φ_λ(γ g)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- `m_P(g)^λ = exp ⟨λ, H_P(g)⟩` for `λ ∈ X^*(P) ⊗ ℂ`, with the Iwasawa height `H_P`
of `K`. -/
def IsIwasawaCompact.heightPower (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) : ℂ :=
  Complex.exp (complexParameterPairing F P lam (hK.height g))

/-- The twist `φ_λ(g) = φ(g) m_P(g)^λ` of a function `φ` on `G(𝔸)`. -/
def IsIwasawaCompact.parameterTwist (hK : IsIwasawaCompact p K)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) : ℂ :=
  φ g * hK.heightPower lam g

variable (F) (p) in
/-- The rational points `P(F)`, as the subgroup of the rational points `G(F)` given by the
image of the principal points of `P` under `p`. -/
def parabolicRationalSubgroup : Subgroup (rationalSubgroup F G) :=
  ((rationalSubgroup F P).map (map F P G p).toMonoidHom).subgroupOf (rationalSubgroup F G)

variable (F) (p) in
/-- The coset space `P(F) \ G(F)` of right cosets `P(F) γ`. -/
abbrev ParabolicRationalCosets :=
  Quotient (QuotientGroup.rightRel (parabolicRationalSubgroup F p))

/-- The terms `γ ↦ φ_λ(γ g)` of the Eisenstein series, evaluated at the chosen
representative `γ ∈ G(F)` of each coset in `P(F) \ G(F)`. -/
def IsIwasawaCompact.eisensteinTerm (hK : IsIwasawaCompact p K)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) (c : ParabolicRationalCosets F p) : ℂ :=
  hK.parameterTwist φ lam (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g)

/-- The Eisenstein series `E(g, φ, λ) = ∑_{γ ∈ P(F) \ G(F)} φ_λ(γ g)`, as the unconditional
sum of the terms; it is `0` where the terms are not summable. -/
def IsIwasawaCompact.eisensteinSeries (hK : IsIwasawaCompact p K)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) : ℂ :=
  ∑' c : ParabolicRationalCosets F p, hK.eisensteinTerm φ lam g c

end Langlands.Global.AdelicGroupPoints
