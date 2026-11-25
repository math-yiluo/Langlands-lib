import Langlands.GaloisCohomology.Global.RealPlaces.VanishingStatement
import Langlands.GaloisCohomology.Global.RealPlaces.VanishingMackey

/-!
# The vanishing of `Ĥ_cʳ(G_S, M)` in degrees `≥ 4`: proof

`tateCompactSupportVanishingStatement : TateCompactSupportVanishingStatement`. Let `r ≥ 4`. By the
dévissage `subsingleton_compactCohomology_of_coind`, it suffices that `Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0` for
every open subgroup `W` of `G_S` when `S` contains the places above `2`, which is
`subsingleton_compactCohomology_coind_zmodRep_two`.

The steps, in the modules of `Langlands.GaloisCohomology.Global.RealPlaces`:

* `VanishingCriterion`: `Ĥ_cʳ⁺¹ = 0` as soon as the localization to the real places is surjective in
  degree `r` and injective in degree `r + 1` (`r ≥ 3`; the finite local terms vanish), and the
  vanishing passes to extensions and retracts;
* `VanishingDevissage`: reduction to `M` killed by a prime; odd primes; for `2`, `M` is a retract of
  `Coind_W Res_W M` for `W` of odd index acting through a `2`-group, filtered by copies of `ℤ/2`;
* `VanishingUnits`: `H³(G_S, μ₂) → ∏_{w real} H³(K_w, μ₂)` is bijective, through the `S`-units;
* `VanishingTwo`: the same for `ℤ/2` in every degree `≥ 3`, by the dimension shift;
* `VanishingPlaces`, `VanishingMackey`: Shapiro's lemma and the Mackey formula at the real places,
  the top double cosets as the real places of the fixed field of `W`, and the case `Coind_W(ℤ/2)`.
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

/-- **Vanishing of `Ĥ_cʳ(G_S, M)` for `r ≥ 4`.** -/
theorem tateCompactSupportVanishingStatement : TateCompactSupportVanishingStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι M _ _ n hn hM hS r hr
  exact subsingleton_compactCohomology_of_coind ι hr
    (fun h2 W => subsingleton_compactCohomology_coind_zmodRep_two ι h2 W hr) n hn hS M hM

end Langlands.GaloisCohomology
