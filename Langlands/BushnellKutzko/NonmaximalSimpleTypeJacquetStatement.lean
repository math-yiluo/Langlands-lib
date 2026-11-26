import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Classification.Supercuspidal

/-! # Jacquet modules of representations containing a non-maximal simple type -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uρ uπ

/-- **BK93 (7.3.2), the first remark after it, and (7.3.6)(i), kind (a).** A smooth
representation of `GL_n(F)` containing a simple type of kind (a) whose centralizer order
has period `e(𝔅_β | 𝔬_E) ≥ 2` has a nonzero Jacquet module along a proper block parabolic
subgroup, that is, along a conjugate of the unipotent radical of a proper standard upper
block parabolic subgroup. No irreducibility or admissibility of the representation is
assumed. -/
def PositiveDepthNonmaximalTypeJacquetStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n → ∀ (ψF : AddChar F ℂ)
    (J : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ J)
    (S : Stratum 𝒪[F] F (Fin n → F)) (q : S.DefiningSequenceChoice) (e : ℕ),
    IsSimpleTypeData (W := (ρ : Type uρ)) ψF S q e (glRepresentationToAut ρ) → 2 ≤ e →
    ∀ π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F), ContainsType π ρ →
      ∃ (B : GeneralLinear.BlockShape n) (g : GeneralLinear n F), B.parabolic F ≠ ⊤ ∧
        ¬ Subsingleton (Jacquet.Coinvariants π.representation (B.conjugateUnipotent g))

end Langlands.BushnellKutzko
