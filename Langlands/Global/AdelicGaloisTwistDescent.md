# Canonical descent of Galois-twisted adelic points

Helper module for the proof of `GaloisBorelTwistingStatement` (Task 5268).

`adeleTest L` is `Spec 𝔸_L` as a scheme over `Spec L`; its morphisms to `H.X` are the adelic
points of an `L`-group `H`. `adeleTestIso F L σ` is the isomorphism over `Spec L` between the
pullback of `adeleTest L` along `Spec σ` and `adeleTest L`, with underlying morphism
`Spec σ̃` (`adeleTestIso_hom_left`), where `σ̃` is the adele automorphism of
`AdeleGaloisAction`.

Main results:

- `galoisTwist_left_fst` (scheme-level formula) and `descentPoint_galoisTwist`: under the
  Library's canonical descent `descentPoint` (used in the definition of
  `galoisTransport` / `radicalGaloisHom`), the twist `φ_σ x` corresponds to
  `(adeleTestIso σ).hom ≫ x`. This mirrors the Library lemma
  `descentPoint_rationalConjugate` for rational points.
- `twistPoint F L σ H p`: the Galois translate of an adelic point `p` of an `L`-group `H`, a
  point of the base change `H^σ` of `H` along `Spec σ`.
- `twistPoint_comp_radicalGaloisHom` (D1): for a subgroup `j : H ⟶ G_L`,
  `twistPoint p ≫ radicalGaloisHom j σ = φ_σ (p ≫ j)`: the twist of a point of a subgroup is
  the twisted point of the canonical Galois translate of the subgroup.

Generic lemmas (over any base): `descentPoint_comp_descentBaseChangeIso`,
`comp_descentHom_of_descentPoint`, and `comp_eq_of_descentPoint`, which takes the composite
morphism `φ` as a parameter with an equation `hφ` (this avoids a kernel timeout: when the
declared conclusion differs syntactically from the lemma output under `≫`, the kernel unfolds
the `eqToIso` inside `descentBaseChangeIso`).
