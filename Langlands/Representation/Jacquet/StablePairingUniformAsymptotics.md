# Uniform asymptotics of stable pairings (abstract Propositions I.4.3 and I.6.2)

Author: Worker 249.

This module extends `Langlands.Representation.Jacquet.StablePairingAsymptotics` in
three ways. The asymptotic formula of the stable pairing is proved for elements that
need not commute with `M`. A single depth threshold is then obtained for finitely
many pairing data at once. Finally, the constant term of a coefficient is defined,
shown to satisfy the defining property of Waldspurger's Proposition I.6.2, and shown to
lie in `A(M)` (see the section on Proposition I.6.2 below). The source statement is J.-L. Waldspurger, *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), Proposition I.4.3, p. 245 (`waldspurger-2003-plancherel`), which
Waldspurger attributes to Casselman ([C, Théorème 4.3.3]):

> Pour `m ∈ M̄_0^+` et `t ∈ ℝ`, définissons un sous-groupe parabolique standard
> `P_{m,t} = M_{m,t} U_{m,t}` par l'égalité
> `Δ_0^{M_{m,t}} = {α ∈ Δ_0 ; ⟨α, H_0(m)⟩ ⩽ t}`.
>
> Proposition I.4.3. Soit `(v, v̌) ∈ V × V̌`. Il existe `t > 0` tel que pour tout
> `m ∈ M̄_0^+`, on ait l'égalité
> `δ_P(m)^{-1/2} ⟨π(m)v, v̌⟩ = ⟨π_P(m) j_P(v), ǰ_P̄(v̌)⟩_P`, où `P = P_{m,t}`.

Waldspurger's convention for `H_0` is `q^{-⟨χ, H_0(m)⟩} = |χ(m)|_F` (p. 240). Thus
`⟨α, H_0(m)⟩ > t` means `|α(m)|_F < q^{-t}`, and `m` contracts the root subgroups of
the simple roots outside `M_{m,t}`. `M̄_0^+` is `H_0^{-1}` of the closed positive
chamber.

The abstraction, its hypotheses and the proof are internal to this project. The
conventions (`Nbar` for the unipotent radical `U` of `P`, `N` for the opposite
radical, the arguments of the pairing in the opposite order to the source) are those
of `StablePairingAsymptotics`. That module also explains the Library's
`StablePairingData`, `Admits` and `IsStablePairing`.

## Helpers

- `mem_stableImage_of_commute`: an endomorphism `T` of the `K`-fixed vectors that
  commutes with compression by `g` maps the stable image of compression by `g` into
  itself. `K` is a compact open subgroup and `ρ` is smooth.
- `compressedAction_commute_of_factor` (Casselman's commutation). Let `K` be a
  compact open subgroup with `K = (K ∩ Nbar)(K ∩ M)(K ∩ N)` for subgroups `N`, `M`,
  `Nbar`. Let `a` and `c` be two commuting elements. Assume that each `x ∈ {a, c}`
  satisfies the three conditions `x (K ∩ N) x⁻¹ ⊆ K`, `x⁻¹ (K ∩ Nbar) x ⊆ K` and
  `x⁻¹ (K ∩ M) x ⊆ K`. Then the compressions by `a` and by `c` commute. Both products
  are compression by `ac = ca`, by the Library's `compressedAction_mul_of_factor`.
  The subgroups here are arbitrary: in the application to Proposition I.4.3 they
  come from the minimal parabolic, `N = U_0`, `M = M_0`, `Nbar = Ū_0`.
- `IsStablePairing.apply_action_of_mem`: `hA : D.Admits ρ hρ` and
  `hb : D.IsStablePairing ρ hρ b`. If `ℓ` is fixed by an open subgroup `K` and
  `m ∈ M ∩ K`, then `b [ℓ] (m · y) = b [ℓ] y` for the unnormalized action on
  the opposite quotient. This follows from the Library's `IsStablePairing.map_action`.
- `IsStablePairing.apply_mk_averageMap`: `hA`, `hb`, `K` good and `ℓ` `K`-fixed.
  If `u` is fixed by `K ∩ N`, then `b [ℓ]` takes the same value at the class of the
  `K`-average of `u` and at `[u]`. Write `k = l m x` by the factorization. Then the
  class of `ρ(k) u` is `m · [u]`, and the previous helper removes `m`. No
  invariance of `u` under `K ∩ M` is needed.
- `apply_mk_eq_sqrt_mul_normalized`: for any bilinear `b`, a character
  `δ : M →* ℝ≥0ˣ`, `m ∈ M` and `v`,
  `b x [ρ(m) v] = δ(m)^{1/2} b x (J_δ(m) [v])`. Here `J_δ` is the Library's
  `normalizedActionOfModulus`, with `J_δ(m) [v] = δ(m)^{-1/2} [ρ(m) v]`.

## Asymptotics without commutation with `M`

`IsStablePairing.exists_finset_asymptotics_of_commute`. Assume
`hA : D.Admits ρ hρ` and `hb : D.IsStablePairing ρ hρ b`. Let `K` be good, `v` a
`K`-fixed vector and `ℓ` a `K`-fixed smooth functional. Then there is a finite set
`F ⊆ Nbar` with the following property. Let `a ∈ G` satisfy three conditions:
`a⁻¹ (K ∩ N) a ⊆ K`; the compressions by `a` and by `g⁻¹` on `K`-fixed vectors
commute; and `a n a⁻¹ ∈ K` for all `n ∈ F`. Then `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]`.

The proof follows `IsStablePairing.exists_finset_asymptotics` of
`StablePairingAsymptotics`. A stable `t` with `[t] = [v]` and the finite set `F`
make the `K`-average of `ρ(a) v` equal to compression by `a` of `t`. That vector is
stable by `mem_stableImage_of_commute`, and the stable-pairing property applies to
it. Finally, `apply_mk_averageMap` with `u = ρ(a) v` (fixed by `K ∩ N` by the first
condition) replaces the class of the average by `[ρ(a) v]`.

Compared with `StablePairingAsymptotics`, the element `a` need not commute with `M`
or `g`, and no condition on `a (K ∩ Nbar) a⁻¹` is imposed directly. The commutation
of compressions replaces them. In Proposition I.4.3, `m ∈ M̄_0^+` lies in `M_0` but
is in general not central in `M_{m,t}`.

## Constant term of a coefficient (Proposition I.6.2, existence)

Waldspurger, Proposition I.6.2, p. 249:

> Soient `f ∈ A(G)` et `P = MU` un sous-groupe parabolique semi-standard de `G`.
> Il existe un unique élément `f_P ∈ A(M)` vérifiant la propriété suivante: pour tout
> `m ∈ M`, il existe `ε > 0` tel que pour tout `a ∈ A_M` vérifiant `|α(a)|_F < ε`
> pour tout `α ∈ Σ(P)`, on ait l'égalité `δ_P(ma)^{-1/2} f(ma) = f_P(ma)`.

Its existence proof takes `f(g) = ⟨π(g)v, v̌⟩` and
`f_P(m) = ⟨π_P(m) j_P(v), ǰ_P̄(v̌)⟩_P`, and applies Theorem I.4.1.

`coefficientConstantTerm D ρ b δ ℓ v` (definition) is the function
`m ↦ b [ℓ] (J_δ(m) [v])` on `M`, for a bilinear form `b`, a character
`δ : M →* ℝ≥0ˣ`, a smooth functional `ℓ` and a vector `v`.

`HasAsymptotics.exists_coefficientConstantTerm` has these hypotheses: `ρ` is smooth;
`b` has the asymptotic property `D.HasAsymptotics ρ b` of
`StablePairingAsymptotics`; `δ : M →* ℝ≥0ˣ`; `ℓ`, `v` and `m ∈ M` are arbitrary.
It concludes that there are a good `K` and a finite set `F ⊆ Nbar` such that
`δ(m a)^{-1/2} ℓ(ρ(m a) v) = coefficientConstantTerm D ρ b δ ℓ v (m a)` for every
`a ∈ M` with `D.IsContractingElement a` and `a n a⁻¹ ∈ K` for all `n ∈ F`.

Proof. A good `K` fixes `ρ(m) v` and `ℓ`. `HasAsymptotics.normalized` applied to
`ρ(m) v` gives `F`. A contracting `a` commutes with `m`, so `ρ(m a) v = ρ(a) ρ(m) v`.
Moreover `[ρ(m) v] = δ(m)^{1/2} J_δ(m) [v]` and `J_δ(a) J_δ(m) = J_δ(m a)`.
Finally, `δ(m a)^{1/2} = δ(m)^{1/2} δ(a)^{1/2}`.

With `δ = δ_P`, this is the defining property of `f_P` in Proposition I.6.2, in the
abstract setting and with the cone replaced by contracting elements as in
`StablePairingAsymptotics`.

`f_P ∈ A(M)`. Here `A(π)` is the Library's `coefficientFunctionSpace` (the span of the
coefficients `m ↦ λ(π(m) y)` with `λ` a smooth functional).

- `normalizedActionOfModulus_apply_of_eq_one`: for any representation `ρ` of a group `G`,
  subgroups `N`, `M` with `M` normalizing `N`, a character `δ : M →* ℝ≥0ˣ` and `m ∈ M`
  with `δ(m) = 1`, `J_δ(m) y = m · y` (unnormalized action) on the coinvariants.
- `isAdmissible_normalizedActionOfModulus`: `G` is a group with a topology, `ρ` smooth,
  `δ` has open kernel, and the unnormalized action of `M` on the coinvariants is
  admissible. Then `J_δ` is admissible: its fixed vectors under an open `L ⊆ M` lie in
  the fixed vectors of the unnormalized action under the open `L ∩ ker δ`.
- `IsStablePairing.mem_smoothVectors_normalized`: under `hA`, `hb` and `δ` with open
  kernel, `b x` is a smooth functional for `J_δ` on the opposite quotient, for every
  class `x`. The Library's `IsStablePairing.exists_open_invariant` gives an open `U` with
  `b x (m · y) = b x y` for `m ∈ M ∩ U`, and `J_δ(m) = m ·` on `ker δ`.
- `IsStablePairing.coefficientConstantTerm_mem_coefficientFunctionSpace`: under `hA`,
  `hb` and `δ` with open kernel, `coefficientConstantTerm D ρ b δ ℓ v` is the coefficient
  of `J_δ` at the vector `[v]` and the smooth functional `b [ℓ]`. Hence it lies in
  `A(J_δ)`, for `J_δ` bundled as a smooth representation of `M` (`SmoothRep.of`, smooth
  by the Library's `isSmooth_normalizedActionOfModulus`).
- `IsStablePairing.exists_admissible_coefficientConstantTerm` (`f_P ∈ A(M)`): assume
  `hA`, `hb`, `δ` with open kernel, `ρ` admissible and
  `HasIwahoriContractionBasis Nbar M N` (Library: for every open subgroup `L` of `M` a
  compact open `K` with `K ∩ M ⊆ L` and some `g` with `IsIwahoriContraction K Nbar M N g`:
  `g ∈ M`, `K = (K ∩ N)(K ∩ M)(K ∩ Nbar)`, and conjugation by `g` contracting `K ∩ Nbar`
  with the further conditions of that Library structure). Then there is an admissible smooth representation `π` of `M`
  with `coefficientConstantTerm D ρ b δ ℓ v ∈ A(π)`. Admissibility of the unnormalized
  action is the Library's `isAdmissible_action_of_iwahoriContraction` (Jacquet's lemma
  in abstract form).

The following parts of Proposition I.6.2 are not proved here: that `f_P` depends only
on `f` and not on the choice of `(v, ℓ)`, and its uniqueness.

## Uniform threshold

`DepthControls Nbar K A depth` (definition) holds for a subgroup `Nbar`, an open
subgroup `K`, a set `A ⊆ G` and a function `depth : G → ℝ` if the following is
true. For every finite set `F ⊆ Nbar` there is `T ∈ ℝ` with `a n a⁻¹ ∈ K` for
every `a ∈ A` with `T < depth a` and every `n ∈ F`.

`exists_uniform_asymptotics` (abstract form of Proposition I.4.3) has the
following hypotheses:

- `ι` is a finite index type, `ρ` is smooth, and `D i` (`i : ι`) are pairing data;
- `b i` are bilinear forms with `hA i : (D i).Admits ρ hρ` and
  `hb i : (D i).IsStablePairing ρ hρ (b i)`;
- `K` is an open subgroup that is good for every `D i`;
- `v` is a `K`-fixed vector and `ℓ` a `K`-fixed smooth functional;
- `A ⊆ G` and `depth : ι → G → ℝ`, with `DepthControls (D i).Nbar K A (depth i)`
  for every `i`;
- for every `i` and `a ∈ A`: `a⁻¹ (K ∩ (D i).N) a ⊆ K`;
- for every `i` and `a ∈ A`: the compressions by `a` and by `(D i).g⁻¹` on
  `K`-fixed vectors commute.

Conclusion: there is `T ∈ ℝ` such that `ℓ(ρ(a) v) = b i [ℓ] [ρ(a) v]` for every
`i` and every `a ∈ A` with `T < depth i a`.

Proof: `exists_finset_asymptotics_of_commute` gives a finite set `F i` for each `i`.
`DepthControls` gives a threshold `T i` for `F i`, and `T = Σ_i |T i|` bounds all
of them.

`exists_uniform_normalized_asymptotics` adds two hypotheses to the previous ones:
every element of `A` lies in every `(D i).M`, and `δ i : (D i).M →* ℝ≥0ˣ` are
characters. It concludes that there is `T` with
`ℓ(ρ(a) v) = (δ i)(a)^{1/2} b i [ℓ] (J_{δ i}(a) [v])` for every `i` and every
`a ∈ A` with `T < depth i a`. It combines `exists_uniform_asymptotics` with
`apply_mk_eq_sqrt_mul_normalized`.

## Relation to the source

The intended specialization is the following. `ι` indexes the proper standard
parabolic subgroups `P = M_P U_P ⊇ P_0`. `D P` has `Nbar = U_P`, `N = Ū_P`,
`M = M_P` and a strictly contracting `g_P` in the split centre `A_{M_P}`, and
`δ P = δ_P`. `A` is `M̄_0^+`, and `depth P m` is `min ⟨α, H_0(m)⟩` over the
nonempty set of simple roots `α ∈ Δ_0 ∖ Δ_0^{M_P}`. Since every
`α ∈ Δ_0 ∖ Δ_0^{M_{m,t}}` has `⟨α, H_0(m)⟩ > t`, `depth P_{m,t} m > t` whenever
`P_{m,t} ≠ G`. So for `t > max(T, 0)` and `P_{m,t} ≠ G`, the normalized conclusion
at `i = P_{m,t}` is the displayed identity of Proposition I.4.3, read through the
order of arguments of the pairing. When `P_{m,t} = G` the unipotent radical is
trivial and the source identity reduces to `⟨π(m)v, v̌⟩ = ⟨π(m)v, v̌⟩`; this case is
not covered by the module.

None of the following inputs is constructed or proved here; they remain
obligations for actual groups:

- the pairing data `D P` with `Admits`, with one good subgroup `K` for all `P`;
- for `m ∈ M̄_0^+`, the inclusion `m⁻¹ (K ∩ Ū_P) m ⊆ K`;
- for `m ∈ M̄_0^+`, the commutation of the compressions by `m` and by `g_P⁻¹`. For
  example, this follows from `compressedAction_commute_of_factor` for the Iwahori
  factorization of `K` relative to `P_0`, once `m` and `g_P⁻¹` satisfy its three
  conditions;
- `DepthControls U_P K M̄_0^+ (depth P)`.
