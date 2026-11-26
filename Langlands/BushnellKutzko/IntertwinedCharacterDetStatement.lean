import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.CharacterIntertwining

/-! # Characters of `U^{m+1}(𝔄)` intertwined by all of `G` (Bushnell–Kutzko 1993, (2.4.11))

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Lemma (2.4.11),
second assertion, printed p. 73 (PDF p. 85), proved in §2.5 on printed p. 78 (PDF p. 90): a
character of `U^{m+1}(𝔄)`, `m ≥ 0`, which is intertwined by every element of `G = Aut_F(V)`
factors through the determinant `det : G → F^×`.
-/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.4.11), character part.** Let `F` be a nonarchimedean local field, `V` an
`F`-vector space, `L` an `𝔬_F`-lattice chain in `V` with hereditary order `𝔄 = 𝔄(L)`, and
`m ≥ 0`. Let `χ : U^{m+1}(𝔄) → ℂˣ` be a group homomorphism on `L.unitFiltration (m + 1)` that is
intertwined by every `g ∈ G = (Module.End F V)ˣ`, i.e. `g ∈ characterSelfIntertwining χ` for all
`g`. Write `d : U^{m+1}(𝔄) → F^×` for the restriction of `Units.map LinearMap.det` to this
subgroup. Then `χ = φ ∘ d.rangeRestrict` for some homomorphism `φ` from the image `d.range` of
the determinant to `ℂˣ`. -/
def IntertwinedCharacterDetStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (L : LatticeChain 𝒪[F] F V) (m : ℕ) (χ : L.unitFiltration (m + 1) →* ℂˣ),
    (∀ g : (Module.End F V)ˣ, g ∈ characterSelfIntertwining χ) →
      let d := (Units.map (LinearMap.det : Module.End F V →* F)).comp
        (L.unitFiltration (m + 1)).subtype
      ∃ φ : d.range →* ℂˣ, χ = φ.comp d.rangeRestrict

end Langlands.BushnellKutzko
