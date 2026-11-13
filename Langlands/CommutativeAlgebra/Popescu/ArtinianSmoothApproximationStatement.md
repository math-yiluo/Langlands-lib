# Essentially smooth approximation of truncated local rings in positive characteristic

`Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothApproximationStatement` (universe `u`).

Notation: for a prime `q` of a ring `Λ`, `Λ_q = Localization.AtPrime q`, `𝔪_q` is its
maximal ideal, and `localTruncation q n = Λ_q ⧸ 𝔪_qⁿ` (see `EssentiallySmooth.md`).
`k[y] = MvPolynomial (Fin m) k`. `toLocalTruncation q n : Λ →+* localTruncation q n` is the
canonical map `x ↦ x/1 mod 𝔪_qⁿ` (see `EssentiallySmooth.md`).

**Hypotheses.**
- `k : Type u` is a field of characteristic `p`, with `p` prime (`Fact p.Prime`,
  `CharP k p`).
- `Λ : Type u` is a `k`-algebra with `GeometricallyRegular k Λ`. This includes that `Λ` is
  Noetherian.
- `q` is a prime of `Λ`, `n > 0`, and `E` is a finite subset of `localTruncation q n`.

**Conclusion.** There are `m : ℕ`, a `k`-algebra map `φ : k[y] →ₐ[k] Λ` and a prime
`𝔭` of `k[y]` with `h𝔭 : 𝔭 = q.comap φ` such that:

1. `𝔭.map (algebraMap Λ Λ_q ∘ φ) = 𝔪_q`, i.e. `𝔭Λ_q = qΛ_q`;
2. the local homomorphism `Localization.localRingHom 𝔭 q φ h𝔭 : k[y]_𝔭 → Λ_q` is flat;
3. there are a local Artinian ring `D : Type u`, an algebra structure of
   `localTruncation 𝔭 n` on `D`, and a ring map `ψ : D →+* localTruncation q n`, with
   - `EssentiallySmooth (localTruncation 𝔭 n) D`,
   - `ψ` local (`IsLocalHom ψ`) and flat (`ψ.Flat`),
   - for every `y ∈ k[y]`,
     `ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)) =
     toLocalTruncation q n (φ y)`: `ψ` maps the image of `y` in `D` to the image of `φ y`
     in `localTruncation q n`, and
   - `E ⊆ Set.range ψ`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 11.2 (Tag 07FH, printed p. 27):

> Let k be a field of characteristic p > 0. Let Λ be a Noetherian geometrically regular
> k-algebra. Let q ⊂ Λ be a prime ideal. Let n ≥ 1 be an integer and let
> E ⊂ Λ_q/qⁿΛ_q be a finite subset. Then we can find m ≥ 0 and
> φ : k[y₁, …, y_m] → Λ with the following properties
> (1) setting p = φ⁻¹(q) we have qΛ_q = pΛ_q and k[y₁, …, y_m]_p → Λ_q is flat,
> (2) there is a factorization by homomorphisms of local Artinian rings
> k[y₁, …, y_m]_p/pⁿk[y₁, …, y_m]_p → D → Λ_q/qⁿΛ_q
> where the first arrow is essentially smooth and the second is flat,
> (3) E is contained in D modulo qⁿΛ_q.

## Encoding and scope

- **The prime.** The source calls `φ⁻¹(q)` "p", which is also the characteristic. Here it
  is `𝔭`. Lean gives it as a bound prime ideal with an equation `𝔭 = q.comap φ`, not as the
  expression `q.comap φ`. The two forms are equivalent (take `𝔭 = q.comap φ`). The bound
  form keeps the elaborated statement small.
- **`pⁿk[y]_p`.** `pk[y]_p` is the maximal ideal of `k[y]_p`, so
  `k[y]_p/pⁿk[y]_p` is `localTruncation 𝔭 n`. Likewise `qΛ_q = 𝔪_q`.
- **Property (1).** `qΛ_q = pΛ_q` is stated as `𝔭.map (algebraMap Λ Λ_q ∘ φ) = 𝔪_q`.
  Flatness of `k[y]_p → Λ_q` is flatness of `Localization.localRingHom 𝔭 q φ h𝔭`, the map
  induced by `φ`.
- **Property (2).** "Factorization" means that `ψ` composed with `localTruncation 𝔭 n → D`
  is the map `localTruncation 𝔭 n → localTruncation q n` induced by `φ`. Lean states this
  on the elements `toLocalTruncation 𝔭 n y` with `y ∈ k[y]`. That suffices: every element
  of `localTruncation 𝔭 n` is the class of some `y/s` with `y ∈ k[y]` and `s ∉ 𝔭`, the class
  of `s` is a unit, and ring maps preserve inverses. "Homomorphisms of local Artinian
  rings" is encoded as `D` local Artinian and `ψ` a local homomorphism. The first arrow is
  then local automatically: if an element of `localTruncation 𝔭 n` maps to a unit of `D`,
  then it maps to a unit of `localTruncation q n`. Its image `x/1` in `Λ_q` is then a
  unit, so it is not in the maximal ideal of `localTruncation 𝔭 n`. "Essentially smooth" is
  `EssentiallySmooth`, a localization of a smooth algebra (see `EssentiallySmooth.md`).
- **Property (3).** "E is contained in D" means that `E` lies in the image of `ψ`.
- **Characteristic.** "Characteristic p > 0" is `CharP k p` with `p` prime.
- **Geometric regularity.** "Noetherian geometrically regular k-algebra" is
  `GeometricallyRegular k Λ` (Library, `Langlands/CommutativeAlgebra/RegularRingMaps`),
  whose definition includes `IsNoetherianRing Λ`.
- **Use.** Step (9) of the proof of Lemma 11.4 (Tag 07FJ, printed p. 28) applies this lemma
  ("Ad (9). This follows by applying Lemma 11.2").
- **Universe.** `k`, `Λ` and `D` are in one universe `u`.
