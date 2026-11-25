import Langlands.GaloisCohomology.Global.Localization
import Langlands.GaloisCohomology.Global.PoitouTate.Trace

/-!
# The global Euler characteristic formula: statement

For a number field `K`, a separable closure `Ω`, a finite set `S` of finite places of `K`,
`G_S = Gal(K_S/K)` and a finite smooth `G_S`-module `M` whose order is a unit outside `S`, Tate's
global Euler characteristic formula is
`#H⁰(G_S, M) · #H²(G_S, M) / #H¹(G_S, M) = ∏_{w real} #H⁰(K_w, M) / (#M)^{#∞}`,
`#∞` the number of infinite places of `K` (`GlobalEulerCharacteristicStatement`; the left side is
`eulerCharacteristic M`). It is proved in
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Proof`.
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

/-- **Tate's global Euler characteristic formula** for `G_S`: for every finite smooth module `M`
whose order is invertible outside `S`,
`χ(G_S, M) = ∏_{w real} #H⁰(K_w, M) / (#M)^{#∞}`. -/
def GlobalEulerCharacteristicStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
    (∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    eulerCharacteristic M =
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)) /
        (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K)

end Langlands.GaloisCohomology
