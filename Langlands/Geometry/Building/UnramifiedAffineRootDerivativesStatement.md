# Derivatives of the affine roots over the maximal unramified field

`Langlands.Geometry.Building.UnramifiedAffineRootDerivativesStatement.{u}` is a
Prop-valued statement of the derivative part of Kaletha–Prasad Proposition 6.3.13
("`∇Ψ = Φ`"), specialized to the maximal unramified extension `K` of a nonarchimedean
local field. The unit only defines the proposition. Its proof is a separate obligation.

Authors: Worker 1407 (original draft, Task 6579 draft revision 1) and Worker 367
(source verification and revised Markdown, Task 6608).

## Quantifiers and hypotheses

At every universe `u`, the proposition ranges over:

- `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
  `IsNonarchimedeanLocalField F`, of equal or mixed characteristic;
- every group scheme `H` over `Spec K`, where
  `K = Langlands.LocalGalois.Separable.inertiaFixedField F`, with
  `IsAffineHom H.X.hom`;
- every `C : MaximalUnramified.BuildingData F H`.

There are no other premises. In particular, no topology, local-field instance or
quasi-splitness hypothesis on `K` and no Axiom V 7 is assumed.

`MaximalUnramified.BuildingData F H` abbreviates
`IntegerValuationBuildingData (MaximalUnramified.valuation F) H`. A datum `C`
supplies:

- connected reductivity of `H`;
- a maximal split torus `C.S` with inclusion `C.i`;
- an `N(K)`-stable equipollence class `C.apartment : KPApartmentData C.i ω`, where
  `ω = IntegerValuation.order (MaximalUnramified.valuation F)`;
- a centralizer datum `C.centralizer` for the actual centralizer `Z_H(C.S)`;
- full compatibility V 6 with `ω` (`IntegerValuation.IsOmegaCompatible`).

The members of the class satisfy `IsRootDatumValuation`, whose fields are exactly the
axioms V 0–V 5 of KP Definition 6.1.2, together with the normalization `φ_a = ∞` off
`U_a(K)` and for non-roots. Axiom V 7 (compatibility with the topology on `H(K)`) is
not part of the data.

## Conclusion

```lean
AffineRootSystem.derivativeRoots C.affineRoots = Set.range (rootForm C.i)
```

This is an equality of subsets of `Module.Dual ℝ (TranslationSpace C.i)`.

- `C.affineRoots` is `KPApartmentData.affineRoots`, the set `Ψ` of KP Definition 6.3.4
  (printed p. 218, PDF p. 249). It consists of the affine functionals `ψ` on the
  apartment whose derivative is `rootForm C.i a` for a relative root `a` and for which
  `U_ψ ⊈ U_{ψ+} · U_{2a}(K)`, with `U_{2a}(K) = {1}` when `2a` is not a root
  (`doubleRootGroupPoints`). This matches KP's
  `Ψ = {ψ ∈ A* | ψ̇ ∈ Φ, U_ψ ⊈ U_{ψ+} · U_{2a}(k)}` (the line above Remark 6.3.5),
  where `a = ψ̇` as the 2024 corrections (p. 32) clarify.
- `AffineRootSystem.derivativeRoots Ψ` is the image of `Ψ` under `ψ ↦ ψ.linear`. This
  is KP's `∇Ψ` (Definition 1.3.1).
- `rootForm C.i a` is the linear form on `V(C.S)/V(C.S)^Φ` induced by the relative
  root `a`. So `Set.range (rootForm C.i)` is the relative root system
  `Φ = Φ(C.S, H)` in the dual of the translation space, multipliable roots and their
  doubles included.

So every relative root of `(H, C.S)` is the derivative of some affine root in
`C.affineRoots`, and every affine root has a relative root as its derivative.

The body, including the binder order `F`, the four instances on `F`, `H`,
`[IsAffineHom H.X.hom]`, `C`, is identical to the hypothesis `hder` of
`unramifiedSharpFixerRootGeneration_of_derivativeRoots`. So a proof of this statement
can be passed as `hder`.

## Comparison with the source

KP Proposition 6.3.13 (printed p. 221, PDF p. 252) reads: "The sets `Ψ` and `Ψ′`
constitute affine root systems in `A*` with derivative root system equal to `Φ`. They
have the same Weyl group. …" This unit states only "the derivative root system of `Ψ`
is `Φ`". It does not state that `Ψ` or `Ψ′` satisfies the affine root system axioms,
the claims about `Ψ′`, or the Weyl group assertions.

The inclusion `∇Ψ ⊆ Φ` is immediate from Definition 6.3.4. The content is the reverse
inclusion: every relative root `a` is the derivative of at least one `ψ ∈ Ψ`.

- **Non-multipliable `a` (`2a ∉ Φ`).** `U_{2a}(K) = {1}`, so `ψ ∈ Ψ` iff
  `U_{ψ+} ≠ U_ψ`. By V 0 and V 1 some `u ∈ U_a(K)` has finite value `r`. The functional
  with derivative `a` and value `r` at the base point then lies in `Ψ`. This uses only
  V 0–V 1. The Library proves this case over any field as
  `KPApartmentData.derivativeRoots_affineRoots_of_no_double`
  (`Langlands.Geometry.Building.ReducedRelativeApartmentRoots`).
- **Multipliable `a` (`2a ∈ Φ`).** The claim is that some `ψ` with derivative `a`
  satisfies `U_ψ ⊈ U_{ψ+} · U_{2a}(K)`. V 0–V 5 alone do not give this. Bruhat–Tits I
  (6.2.2) (printed p. 117, PDF p. 114) define, for a valuation `φ`, the set `Γ'_a` of
  values `φ_a(u)` with `φ_a(u) = sup φ_a(u U_{2a})`. They note that `Γ'_a` can be empty:
  it suffices that `U_{2a}` be dense in `U_a`, and this is also necessary when `Γ_a` is
  discrete. Example (6.2.3) d) (printed p. 118, PDF p. 115) gives such a valuation of
  `SL_2` with root system `{±a, ±2a}` over an imperfect field of characteristic 2.

## Where KP use Axiom V 7

Definition 6.1.2 (printed p. 199, PDF p. 230) lists V 0–V 5 (valuation of the root
datum), V 6 (compatibility with `ω`) and V 7 (compatibility with the topology:
the `U_{a,φ,r}` are bounded open subgroups forming a neighbourhood basis of `1` in
`U_a(k)`). The proof of Proposition 6.3.13 cites Proposition 6.3.8(1)(2): for every
`a ∈ Φ` there are infinitely many `ψ ∈ Ψ` with derivative `a`. Proposition 6.3.8
(printed p. 219, PDF p. 250) explicitly assumes that the class consists of valuations
satisfying V 7. Its part (2), for multipliable `a`, is proved with Lemma 6.3.9
(printed pp. 219–220, PDF pp. 250–251), which uses V 7 twice:

- `U_ψ ∖ U_{ψ+}` is a nonempty open subset of `U_a(k)` and so is not contained in the
  Zariski-closed `U_{2a}(k)`;
- if `x_a(u_i) → ∞` then `u_i → 1`, and `U_{2a}(k)` is closed in `U_a(k)`.

Corollary 6.3.10 (printed p. 220, PDF p. 251), `Ψ′_a = Ψ_a ∪ ½Ψ_{2a}`, is deduced from
Proposition 6.3.8 in the same setting. The Library's
`ValuationBuildingData.derivativeRoots_affineRoots_of_isTopologyCompatible`
(`Langlands.Geometry.Building.ValuationDerivativeAffineRoots`) formalizes this V 7
route over a nonarchimedean local field `F`. It does not apply over `K`, which carries
no topology instance here.

## Why the statement holds for every supplied datum over `K`

This section explains why the proposition is expected to be true. It is not a proof
and is not formalized.

1. **KP's setting covers `K`.** Chapter 6 (opening, printed p. 195, PDF p. 226) works
   over a Henselian field with a discrete valuation `ω`, with `ω(k^×) = ℤ` (except in
   §6.5) and with no perfectness assumption on the residue field. `K`, the maximal
   unramified extension of `F`, is Henselian. Its valuation extends the normalized
   valuation of `F` with value group `ℤ`, and its residue field is an algebraic closure
   of that of `F`.
2. **`H` is quasi-split.** KP Corollary 2.3.8 (printed p. 81, PDF p. 112): every
   connected reductive `K`-group is quasi-split, for `K` discretely valued and
   Henselian with algebraically closed residue field (§2.3). Example 2.3.2(2) (printed
   p. 79, PDF p. 110) names the maximal unramified extension of a local field
   explicitly. `K` need not be perfect.
3. **The canonical class satisfies V 6 and V 7.** For quasi-split groups KP construct
   the canonical apartment `A(S)` (Definition 6.1.27, printed p. 210, PDF p. 241; the
   2024 corrections, p. 32, replace `S′` by `S_ad` and `G_der` by `G_ad` there). After
   Definition 6.1.2 (printed p. 199, PDF p. 230) KP state: "All the valuations
   constructed in this book have the properties V 6 and V 7."
4. **The supplied class is the canonical one.** KP Proposition 6.2.6 (printed p. 216,
   PDF p. 247): any two `ω`-compatible valuations of the root datum of `(G, S)` are
   equipollent. The supplied class satisfies V 6, so it equals the canonical class.
   In the Library this uniqueness is
   `IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus`
   (`Langlands.Geometry.Building.IntegerOmegaApartmentUniqueness`), over any field, for
   two classes with the same centralizer datum.

Hence `C.apartment` satisfies V 7, and Proposition 6.3.13 applies to it. `Ψ` depends
only on the class, since Definition 6.3.4 uses only the filtrations `U_{a,x,r}` for
`x` in the class. So `∇Ψ = Φ`.

KP also give a second argument that avoids Proposition 6.3.8. Remark 6.3.5 (printed
p. 218, PDF p. 249) announces it, and Proposition 6.4.8 (printed p. 225, PDF p. 256)
proves it. For quasi-split `G` and the apartment `A = A(S)` of Definition 6.1.27
(§6.4, opening, printed p. 223, PDF p. 254), it computes `Ψ` and `Ψ′` explicitly
from the jump sets of an adjusted Chevalley valuation. It shows that they are affine
root systems with derivative root system `Φ`. Steps 1, 2 and 4 make this argument
apply to `C.apartment` as well.

## Provenance

Derived. KP state Proposition 6.3.13 for classes satisfying V 7 (and Proposition 6.4.8
for the canonical class of a quasi-split group). This unit states the derivative part
for every supplied V 0–V 6 class over `K = inertiaFixedField F`, with the Library's
data types. The reduction to KP's setting is the argument above (Chapter 6 opening,
Corollary 2.3.8, Definition 6.1.27, the remark after Definition 6.1.2,
Proposition 6.2.6). The statement is not verbatim in the source.

Sources:

- `kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`);
- `kaletha-prasad-2024-corrections` (version of 1 November 2024, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`), p. 32, for
  Definition 6.1.27 and the line above Remark 6.3.5;
- `bruhat-tits-1972-reductive-local-groups-i` (Publ. Math. IHÉS 41, Numdam scan,
  SHA-256 `02718a362e1ddd17ea73ffb026309c4519b0632fcc07cb06affe739fc26c6609`).

## Consumer

`unramifiedSharpFixerRootGeneration_of_derivativeRoots` in
`Langlands.Geometry.Building.IntegerValuationNonnegativeRootGenerators` (candidate
`c757a942-3d8a-46d3-8c7d-36f67e0f2103`, Task 6579) derives the published
`UnramifiedSharpFixerRootGenerationStatement` (KP Lemma 7.4.4(3) over `K`) from a
hypothesis `hder` whose body is this proposition's body.
