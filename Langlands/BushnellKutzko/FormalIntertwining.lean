import Langlands.BushnellKutzko.Stratum

/-! # Formal intertwining of strata (BK93 (1.5.7), (1.5.11), pp. 44, 46) -/

namespace Langlands.BushnellKutzko

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

namespace Stratum

/-- Formal two-stratum intertwining: `g⁻¹ (b₁ + 𝔓₁^{−r₁}) g` meets
`b₂ + 𝔓₂^{−r₂}` (BK93 (1.5.11), p. 46). -/
def formalIntertwining (S T : Stratum O K V) : Set (Module.End K V)ˣ :=
  {g | ∃ y ∈ S.coset,
    ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) * y *
      (g : Module.End K V) ∈ T.coset}

/-- Formal intertwining of a stratum with itself (BK93 (1.5.7), p. 44). -/
def formalSelfIntertwining (S : Stratum O K V) : Set (Module.End K V)ˣ :=
  S.formalIntertwining S

end Stratum

end Langlands.BushnellKutzko
