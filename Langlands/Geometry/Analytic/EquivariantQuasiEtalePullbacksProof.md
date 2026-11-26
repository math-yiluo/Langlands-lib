# Pullbacks in the equivariant quasi-étale site

The module `Langlands.Geometry.Analytic.EquivariantQuasiEtalePullbacksProof`
proves

```lean
theorem equivariantQuasiEtalePullbacks :
    EquivariantQuasiEtalePullbacksStatement.{u, v, z}
```

in the namespace `Langlands.Analytic.SaturatedAtlasPresentation`, the
statement of `Langlands.Geometry.Analytic.EquivariantSitePullbacksStatement`.
Let `K` be a complete ultrametric normed field, `G` a group with a topology
and `X` a `G`-space. Every cospan `U₁ → U₃ ← U₂` in
`EquivariantQuasiEtaleSite X` is completed by arrows `W → U₁` and `W → U₂` of
the site. After forgetting the action, the square of analytic spaces is a
pullback in the localized analytic category. The object `W` carries the
continuous diagonal action of `G`. The universes `u` (field), `v` (spaces and
atlas indices) and `z` (group) are independent.

## Auxiliary results

- `quasiEtale_of_over_of_t2Space`: let `f : A ⟶ U` and `h : U ⟶ X` be
  arrows of the localized analytic category with `A` and `U` Hausdorff. If
  `h` and `f ≫ h` are quasi-étale, then `f` is quasi-étale. This is the
  Hausdorff case of Berkovich 1994, Lemma 3.1(ii).
- `EquivariantQuasiEtaleSite.quasiEtale_map_left`: the analytic map
  underlying an arrow of `EquivariantQuasiEtaleSite X` is quasi-étale.
- `quasiEtale_common_of_isPullback_over`: let `p : P ⟶ A` and `q : P ⟶ B`
  exhibit `P` as a pullback of `f : A ⟶ U` and `g : B ⟶ U`, with `A`, `B`
  and `U` Hausdorff. If `b : U ⟶ X`, `f ≫ b` and `g ≫ b` are quasi-étale,
  then `q ≫ g ≫ b : P ⟶ X` is quasi-étale.

## Right cancellation

Fix a point `z` of `A`. Since `A` and `U` are Hausdorff,
`hasLocalDomainEtaleFactorizations_of_quasiEtale` gives two finite families
of analytic domains. The first covers a neighbourhood of `z`, and on each of
its members `S` the restriction of `f ≫ h` factors as a domain inclusion
followed by an étale map. The second does the same for `h` near the image of
`z`, with members `T`. The intersections `S ∩ f⁻¹(T)` form a finite family
of domains of `A` covering a neighbourhood of `z`. On such an intersection,
`f` factors through the analytic domain embedding of `T`. The local graph
factorization `HasDomainEtaleFactorization.of_comp_of_factor` combines the
factorization of `f ≫ h` on `S` with that of `h` on `T` into a factorization
of `f` on `S ∩ f⁻¹(T)`. `HasLocalDomainEtaleFactorizations.quasiEtale` then
gives that `f` is quasi-étale.

Objects of `EquivariantQuasiEtaleSite X` have Hausdorff underlying spaces
and quasi-étale structure maps to `X`. An arrow `U → V` of the site commutes
with these structure maps, so right cancellation applies with `h` the
structure map of `V`. This proves
`EquivariantQuasiEtaleSite.quasiEtale_map_left`.

## The pullback over the original base

Fix a point `x` of `P`. The private lemma `exists_compact_domain_nhds`
takes a finite union of atlas charts from the net of `U`. This gives a
compact analytic domain `D` of `U` whose carrier is a neighbourhood of the
image of `x`. Let `S = f⁻¹(D)` and `T = g⁻¹(D)`. The domain
`E = p⁻¹(S) ∩ q⁻¹(T)` of `P` is the inverse image of `D`, hence a
neighbourhood of `x`. By `isPullback_domainPreimage_inf` it is a pullback of
the restrictions `S → D ← T`. The restricted maps to `X` stay quasi-étale.
Thus the compact case below shows that `E → X` has local domain–étale
factorizations. `HasLocalDomainEtaleFactorizations.of_domain_cover` assembles
these neighbourhoods into quasi-étaleness of `P → X`.

The compact case is the private lemma `common_of_pullback_over_compact`. Let
`C` be the localized pullback of `f ≫ b` and `g ≫ b` over `X`, and `Q` the
localized pullback of `b` with itself. By
`HasLocalDomainEtaleFactorizations.of_isPullback_common`, the common map
`C → X` has local domain–étale factorizations. These come from products of
the local étale envelopes. Since `U` is compact and Hausdorff and `b` is
quasi-étale, `compactQuasiEtaleDiagonalDomain` makes the diagonal
`U → Q` an analytic domain embedding. Its inverse image under the induced
map `C → Q` is a domain of `C`. The lemma `isPullback_of_relative_diagonal`
shows that this domain, with its projections to `A` and `B`, is a pullback
of `f` and `g`. The proof is a formal argument with the pullback squares of
`C` and `Q`. Hence `P` is isomorphic to this domain over `B`. Restricting the
local factorizations of `C → X` to it gives those of `P → X`.

## Proof of the statement

Write `f₁`, `f₂` for the given arrows. By
`EquivariantQuasiEtaleSite.quasiEtale_map_left`, the analytic map under `f₁`
is quasi-étale. Then `exists_localizedPullback_of_quasiEtale` gives a pullback
`P` of the underlying cospan in the localized analytic category. The
structure maps of `U₁` and `U₂` to `X` factor through the structure map of
`U₃`. So `quasiEtale_common_of_isPullback_over` shows that `P → U₂ → X` is
quasi-étale. Finally `exists_equivariantSitePullback_of_isPullback` puts the
continuous diagonal action on `P`. It makes the two projections arrows of
`EquivariantQuasiEtaleSite X` and keeps the given pullback square.

## Sources

V. G. Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115
(1994), §3, the definition of quasi-étale morphisms and of the quasi-étale
site, and Lemma 3.1, printed pp. 543–544 (PDF pp. 5–6). Literature ID
`berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.

V. G. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
unfinished manuscript (1995–1996), §1.2, printed/PDF p. 3. It defines
`Qét(X(G))` and uses these equivariant pullbacks for morphisms of sites.
Literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The proof follows neither source's argument. Berkovich derives Lemma 3.1
from étale morphisms and Theorem 3.4.1 of his *Étale cohomology for
non-Archimedean analytic spaces*, Publ. Math. IHES 78, cited there as
[Ber2]. The Lean proof works with the
Library's local domain–étale factorizations and compact analytic diagonals.
