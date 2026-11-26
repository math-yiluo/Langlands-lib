import Langlands.BushnellKutzko.GLSimpleTypes

/-! # Maximal simple type pairs at a prescribed period and level -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uρ

/-- A subgroup of `GL_N(F)` and a smooth complex representation on a carrier in `Type uρ`.
The two maximal simple type sets specify which pairs have the required data. -/
abbrev GLRepresentationPair (N : ℕ) (F : Type uF) [Field F] [TopologicalSpace F] :=
  Σ J : Subgroup (GeneralLinear N F), SmoothRep.{0, uF, uρ} ℂ J

variable (N : ℕ) (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The pairs exhibited by kind (a) data at level `m`, with original order period `t`
and centralizer order period one. -/
def glMaximalSimpleTypesAt (t m : ℕ) : Set (GLRepresentationPair.{uF, uρ} N F) :=
  {x | ∃ (ψF : AddChar F ℂ) (S : Stratum 𝒪[F] F (Fin N → F))
        (q : S.DefiningSequenceChoice),
    S.chain.period = t ∧ S.n = (m : ℤ) ∧
      IsSimpleTypeData ψF S q 1 (glRepresentationToAut x.2)}

/-- The pairs exhibited by kind (b) data on an order of period one. -/
def glMaximalLevelZeroSimpleTypes : Set (GLRepresentationPair.{uF, uρ} N F) :=
  {x | ∃ L : LatticeChain 𝒪[F] F (Fin N → F),
    IsLevelZeroSimpleTypeData L 1 (glRepresentationToAut x.2)}

end Langlands.BushnellKutzko
