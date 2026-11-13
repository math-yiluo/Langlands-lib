# V 6 and V 5 at the Galois-fixed points of an unramified apartment

Author: Worker 4707.

Lean module: `Langlands.Geometry.Building.UnramifiedFixedLocusStatement`.

This module states, without proof, two inputs for the published
`UnramifiedValuationDescentStatement` (Kaletha–Prasad, Construction 9.6.1, Lemma 9.6.3 and
Theorem 9.6.5). The descended family must satisfy V 6 on the actual centralizer `Z_G(S)(F)`
and V 5 for every relative root. Neither follows from the class `D` over `K` alone: `Z(F)`
does not normalize `T_K`, and V 5 at multipliable roots needs the reflections `m(u)` of the
building. KP obtain both from the building of `G_K` and its Galois-fixed locus. The module
defines two `Prop`s and contains no theorem.

## Common data

Both statements use exactly the binders and instances of `UnramifiedValuationDescentStatement`:

- `F` is a nonarchimedean local field and `K = inertiaFixedField F` its maximal unramified
  extension;
- `G` is a connected reductive group over `Spec F` (`hG`), with affine and smooth instances
  from `hG`; `iS : S.toGrp ⟶ G` is a maximal split torus (`hiS`);
- `iT : T.toGrp ⟶ G` and `f : S ⟶ T` satisfy `CommGroupScheme.groupHom f ≫ iT = iS`, and
  `hiT` says that the scalar extension `iT_K` is a maximal split torus of `G_K`;
- `hE` gives opposite factor pairs for `iT_K`;
- `D : KPApartmentData iT_K ω` is an equipollence class of valuations of the root datum of
  `(G_K, T_K)`, where `ω` is the order of `MaximalUnramified.valuation F`, and `C` is a
  centralizer datum with full V 6 (`IntegerValuation.IsOmegaCompatible`).

As in the target, `fixed x` says that `x : D.Apartment` is fixed by
`RootFunctionFamily.galoisAction F K T G σ` for every `σ : K ≃ₐ[F] K`. `φ x` is the published
torus-then-field restriction `torusFieldRestrictedRootFunctionFamily … (D.isRootDatumValuation_of_mem x.mem) f_K`,
a root-function family for `(G, S)`. Both are introduced by `let`, with the same bodies as in
the target.

## `UnramifiedFixedCentralizerCompatibilityStatement` (V 6 on `Z(F)`)

For every `CS : CentralizerDatum iS` and every `x` with `fixed x`, the family `φ x`
satisfies `IsCentralizerCompatible iS CS.j CS.s CS.bijective`. This is the full axiom V 6 of
KP Definition 6.1.2 on the actual centralizer: for every relative root `a`, every
`z ∈ Z(F)` and every `u ∈ U_a(F)`,
`φ_a(z⁻¹ u z) = φ_a(u) + a(ν(z))`, with `ν = -ω_Z` the translation of the centralizer datum.

KP source. In the proof of Theorem 9.6.5, V 6 is obtained by "taking `n ∈ Z(k)`" in the
`N(k)`-equivariance `ϕ^{n·x} = n·ϕ^x` and applying Proposition 9.3.16. That proposition
says that `A(S) = B(G_K)^Γ_S` satisfies Axiom 4.1.4: `z ∈ Z(k)` acts on `A(S)` by the
translation `ν(z)`. Its proof uses a fixed point of the bounded group `Z(k)_b` (Theorem
1.1.15) and the comparison on `S(k)`, where `s T s⁻¹ = T`. By Lemma 9.4.15,
`ψ^{z u z⁻¹}_a(z·x) = ψ^u_a(x)`. Together with `z·x = x + ν(z)` this is V 6 for `ϕ^x`.

The statement quantifies over every centralizer datum `CS` of `iS`, not over one chosen
datum. V 6 does not depend on the datum, because `ν` does not.

## `UnramifiedFixedOppositeStatement` (V 5)

For every `x` with `fixed x`, every relative root `a`, every `g ∈ U_a(F)` with `g ≠ 1` and
all `g', g'' ∈ U_{-a}(F)` with `g' g g'' ∈ N(F)`, the family `φ x` satisfies
`φ_{-a}(g') + φ_a(g) = 0`. This is axiom V 5 of KP Definition 6.1.2. It is the hypothesis
`hopposite` of the published constructor `torusFieldRestrictedValuationOfOriginalPointShifts`.

KP source. The proof of Theorem 9.6.5 derives V 5 from Corollary 9.4.10:
`ψ^{u'}_{-a} = -ψ^u_a = ψ^{u''}_{-a}` for `m(u) = u' u u''`. Corollary 9.4.10 follows
from Proposition 9.4.9: `m(u)` acts on `A` by the reflection in the wall `H_{ψ^u_a}`, which
is proved with the Bruhat–Tits group schemes `G^0_z`. The elements `g', g''` of the Lean
statement are the `u', u''` of KP Proposition 2.11.17. The Library already proves V 5 for
non-multipliable roots in the quasi-split case (`QuasiSplitApartmentOpposite`). That
argument does not cover multipliable roots.

## How the statements are used

`UnramifiedValuationDescentReduction` proves
`unramifiedValuationDescent_of_fixedLocus`: the published
`UnramifiedGaloisFixedApartmentStatement` and the Levi transport statement
`UnramifiedFixedLeviTransportStatement`, together with these two statements, imply
`UnramifiedValuationDescentStatement`. V 6 gives clause 1 of the target. V 5 is the last
input of the valuation constructor.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Definition 6.1.2 (V 0–V 7), printed p. 199 / PDF p. 230; Proposition 2.11.17 for `m(u)`,
  printed p. 136 / PDF p. 167.
- Proposition 9.3.13, §9.3.14 and Proposition 9.3.16, printed pp. 338–340 / PDF
  pp. 369–371.
- Proposition 9.4.9 and Corollary 9.4.10, printed pp. 349–350 / PDF pp. 380–381;
  Lemma 9.4.15, printed p. 352 / PDF p. 383.
- Theorem 9.6.5 and its proof, printed pp. 366–367 / PDF pp. 397–398.

The *Corrections and additions* (1 November 2024), `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 39–41, do not change Proposition 9.3.16, Proposition 9.4.9, Corollary 9.4.10 or
Theorem 9.6.5.

## Provenance and scope

The provenance is derived. KP work over Henselian discretely valued fields with perfect
residue field; here `F` is a nonarchimedean local field. KP phrase both facts for the
descended building `B(G_K)^Γ` and its valuation `ϕ^x`. The Lean statements use the
Library's `D.Apartment`, its Galois action and the published restriction, which equals
`ϕ^x` by Lemma 9.6.3 as recorded in the Markdown of `UnramifiedValuationDescentStatement`.

Neither statement is proved here. Their proofs need the building of `G_K` over `K`, its
Galois-fixed locus (Propositions 9.3.13 and 9.3.16), the bounded-group fixed point
theorem, and the Bruhat–Tits group schemes `G^0_z` (Proposition 9.4.9). The Library has a
bounded-subgroup fixed-point theorem on supplied building data
(`boundedSubgroupFixedPoint`, in `BoundedSubgroupFixedPointProof`); constructing the
building over `K` and the comparisons needed here remains an obligation.
