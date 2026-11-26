# Characters of `U^{m+1}(𝔄)` intertwined by all of `G` factor through the determinant

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
Lemma (2.4.11), second assertion, printed pp. 72–73 (PDF pp. 84–85; PDF page = printed page
+ 12). BK93 proves it in §2.5, printed p. 78 (PDF p. 90).

BK93 states: let `χ` be a character of `U^{m+1}(𝔄)`, where `m ≥ 0`, which is intertwined by
every element of `G`. Then `χ` factors through the determinant mapping `det : G → F^×`. Here
`𝔄` is a hereditary `𝔬_F`-order in `A = End_F(V)` and `G = A^×`. The first assertion of
(2.4.11), on cosets `b + 𝔓^{1+n}`, is not part of this file.

## The proposition

`IntertwinedCharacterDetStatement` quantifies over:

- a nonarchimedean local field `F` (`[Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`, with ring of integers `𝒪[F]`) in universe `uF`;
- an `F`-vector space `V` in an independent universe `uV`;
- an `𝒪[F]`-lattice chain `L : LatticeChain 𝒪[F] F V`, whose order `L.order` is the hereditary
  order `𝔄 = 𝔄(L)`;
- a natural number `m`;
- a group homomorphism `χ : L.unitFiltration (m + 1) →* ℂˣ`.

It asserts: if `g ∈ characterSelfIntertwining χ` for every `g : (Module.End F V)ˣ`, then, with

```
d := (Units.map (LinearMap.det : Module.End F V →* F)).comp (L.unitFiltration (m + 1)).subtype
```

the determinant on the subgroup `L.unitFiltration (m + 1)`, there is a group homomorphism
`φ : d.range →* ℂˣ` from the image of `d` with `χ = φ.comp d.rangeRestrict`.

This file states the proposition and does not prove it.

## Correspondence with the source

- **Hereditary order.** The Library describes hereditary orders by lattice chains
  (`IsHereditaryOrder` in `Langlands.BushnellKutzko.LatticeChain`: the orders `𝔄(L)`), as BK93
  does on printed p. 20. The proposition takes the chain `L` itself.
- **`U^{m+1}(𝔄)`.** `L.unitFiltration (m + 1)` is BK93's `U^{m+1}(𝔄) = 1 + 𝔓^{m+1}` as a
  subgroup of `G`; `coe_image_unitFiltration` in `Langlands.BushnellKutzko.UnitFiltration` proves
  that its image in `A` is `{y : y - 1 ∈ 𝔓^{m+1}}`. The natural number `m` is BK93's `m ≥ 0`.
- **The group `G`.** `G = Aut_F(V)` is `(Module.End F V)ˣ`. A lattice chain forces `V` to be
  finite-dimensional (`LatticeChain.finiteDimensional`), so `LinearMap.det` is the usual
  determinant of `G`, and `Units.map LinearMap.det : G →* Fˣ` is BK93's `det : G → F^×`.
- **Intertwining.** `characterSelfIntertwining χ` (`Langlands.BushnellKutzko.CharacterIntertwining`)
  is the set of `g ∈ G` with `χ(g h g⁻¹) = χ(h)` for every `h ∈ U^{m+1}(𝔄)` such that
  `g h g⁻¹ ∈ U^{m+1}(𝔄)`. "Intertwined by every element of `G`" is the hypothesis that every `g`
  lies in this set. As the hypothesis covers both `g` and `g⁻¹`, the side on which the
  conjugation is written does not matter.
- **Factoring through the determinant.** BK93's conclusion is that `χ = χ₀ ∘ det` on
  `U^{m+1}(𝔄)`; in its proof on p. 78, `χ₀` is a character of `F^×` restricted to
  `det(U^{m+1}(𝔄))`. The proposition asks for `φ` on the actual image `d.range` of the
  determinant on `U^{m+1}(𝔄)` and nothing more: `φ` need not extend to `Fˣ` and no continuity is
  asked of it. The existence of such a `φ` is equivalent to `χ` being trivial on the elements of
  `U^{m+1}(𝔄)` of determinant `1`.

## Scope

Characters in BK93 are continuous; `χ` here is any group homomorphism into `ℂˣ`, as for the
other characters of the Library (for instance `characterIntertwining`). BK93's proof on p. 78
starts from the least `n ≥ m` such that `χ` is trivial on `U^{n+1}(𝔄)`, which exists for a
continuous `χ`, and descends one layer at a time using the first assertion of (2.4.11). The
proposition does not assume that `χ` is trivial on any `U^{n+1}(𝔄)`, so a proof of it cannot
use that descent unless it establishes such a triviality first.
