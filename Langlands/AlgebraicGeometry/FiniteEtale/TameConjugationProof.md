# Proof of tame conjugation along a regular local divisor

The module `Langlands.AlgebraicGeometry.FiniteEtale.TameConjugationProof`
proves `regularDivisorTameConjugation :
RegularDivisorTameConjugationStatement.{u, v}`, the statement of
`Langlands.AlgebraicGeometry.FiniteEtale.TameConjugationStatement`. That
statement is the finite `ℓ`-group form of the conjugation law for tame inertia
along a regular divisor (SGA 7 I, Exposé I, written by P. Deligne, (0.4.1) and
its use in Variante 1.4).

The proof does not identify the tame inertia group. It works with one finite
Kummer level `n = |G|`, where `G` is the Galois group of a cover realizing
`ρ`. The relation `σ jg σ⁻¹ = jg ^ q` is checked on a geometric point of a
Kummer cover, and the cover's Galois property carries it to `ρ`.

## Notation

`R` is a Henselian regular local domain with maximal ideal `𝔪`, and
`t ∈ 𝔪 \ 𝔪²` is a regular parameter with `R/(t)` regular. `ℓ` is a prime
that is a unit of `R` (`IsUnit (ℓ : R)`). `U = Spec R[1/t]`, and `W` is a
strictly Henselian discrete valuation ring with a local homomorphism
`R → W` and fraction field `L`, in which `t` is a uniformizer.
`s : Spec Ω ⟶ Spec L` is a geometric point, `j = traitGenericMorphism L t _`,
and `x = s ≫ j`. `q` satisfies `CyclotomicPowerCondition (ResidueField R) ℓ q`,
and `ρ : π₁(U, x) →* H` is continuous with `H` a finite discrete `ℓ`-group.
For `g` in `π₁(Spec L, s)`, `jg` is its image in `π₁(U, x)`.

## Auxiliary results in this module

- `fundamentalGroupMap_congr` transports `fundamentalGroupMap f` along an
  equality `f = f'` of morphisms.
- `traitGenericRingHom_comp` and `traitGenericMorphism_comp`: the composite
  `Spec L ⟶ U ⟶ Spec R` equals `Spec L ⟶ Spec W ⟶ Spec R`.
- `smul_coverU_eq`: for a finite étale `R`-algebra `R'`, every element
  `jg` (the image of some `g`) acts trivially on `Fiber x (coverU t R')`,
  the geometric fibre of `Spec R'[1/t]`. Proof: let `i : U ⟶ Spec R` be the
  open immersion. By the Library's composition law `fundamentalGroupMap_comp`
  and `traitGenericMorphism_comp`, the image of `jg` in
  `π₁(Spec R, x ≫ i)` is the image of an element of `π₁(Spec W, _)`. The
  Library theorem `subsingleton_fundamentalGroup_of_strictLocal` says that
  `π₁(Spec W, _)` is trivial, since `W` is strictly Henselian, so this image
  is `1`. The cover `Spec R'[1/t]` of `U` maps to the cover `Spec R'` of
  `Spec R` by `φ = Spec(R' → R'[1/t])`, over `i`. The Library lemma
  `fundamentalGroupMap_smul_left_of_comp` gives
  `i₍*₎(jg) • (ψ ≫ φ) = (jg • ψ) ≫ φ` on underlying morphisms. The left side
  is `ψ ≫ φ` because `i₍*₎(jg) = 1`, and `φ` is a monomorphism (it is `Spec`
  of a localization), so `jg • ψ = ψ`.
- `exists_coverX_hom`: let `S` be an étale `R`-algebra, and let
  `sB : V ⟶ WA.P` be a section of a Galois cover `WA` of `U` over the basic
  open `V = D(t)` of `Spec S[X]/(X ^ n - t)`, compatible with the maps to
  `Spec R`. Then every `R`-algebra map `b : S → R'` gives a map of covers
  `coverX t R' n ⟶ toCover WA`. Proof: the ring map
  `S[X]/(X ^ n - t) → R'[1/t][X]/(X ^ n - t)` sends `X` to the root and
  `S` through `b`. Its spectrum lands in `V`, because `t` becomes a unit, so
  it factors through `V` (`IsOpenImmersion.lift`). Composing with `sB` gives
  a morphism to `WA.P`. It lies over `U`: this can be checked after
  composing with the monomorphism `U ⟶ Spec R`, where it is an identity of
  ring maps out of `R`.
- `fib_comp` reassociates a fibre element followed by two maps of covers.
- `exists_conj_fixed` is the core computation. Let `R'` be a finite étale
  `R`-algebra that is a domain, with `R → R'` injective, `t ≠ 0` in `R'`,
  `U` connected and locally Noetherian. Let `ζ : R'` satisfy `ζ ^ n = 1`
  with `ζ ^ l - 1` a unit for `0 < l < n`, and let `α` be an `R`-algebra
  endomorphism of `R'` with `α ζ = ζ ^ q`. If `γ` in `π₁(U, x)` acts
  trivially on the fibre of `coverU t R'`, then there are `σ` in `π₁(U, x)`
  and `p` in the fibre of the Kummer cover `coverX t R' n` with
  `((γ ^ q)⁻¹ * (σ * γ * σ⁻¹)) • p = p`.

## Proof of `exists_conj_fixed`

Write `K c` for the automorphism multiplying the Kummer root by `ζ ^ c`, and
`AX`, `AU` for the maps induced by `α`
(`Langlands.AlgebraicGeometry.FiniteEtale.KummerCover`).

1. The fibre of `coverX` is nonempty (`KummerCover.nonempty_fiber`); pick
   `p`.
2. `γ • p` and `p` have the same image in `coverU`, because `γ` acts
   trivially there. By `KummerCover.exists_eq_comp_K`,
   `γ • p = p ≫ K c` for some `c`. By induction,
   `γ ^ m • p = p ≫ K (m * c)` (using `K_comp_K` and `K_zero`).
3. `R'[1/t]` is a domain, so `Spec R'[1/t]` is irreducible, hence connected.
   By `exists_smul_eq_of_connectedSpace` there is `σ` with
   `σ • (p ≫ proj) = p ≫ proj ≫ AU`.
4. `σ • p` and `p ≫ AX` have the same image in `coverU` (`AX_comp_proj`), so
   `σ • p = p ≫ AX ≫ K d` for some `d`.
5. Put `p' = σ • p`. Using naturality of the action on fibres,
   `(σ * γ * σ⁻¹) • p' = σ • γ • p = σ • (p ≫ K c) = p ≫ AX ≫ K d ≫ K c`,
   while `γ ^ q • p' = (γ ^ q • p) ≫ AX ≫ K d = p ≫ K (q * c) ≫ AX ≫ K d`.
   The two agree by `AX_comp_K` (`AX ≫ K c = K (q * c) ≫ AX`) and
   `K_comp_K` (the `K` maps commute). So
   `((γ ^ q)⁻¹ * (σ * γ * σ⁻¹)) • p' = p'`.

## Proof of `regularDivisorTameConjugation`

1. `t ≠ 0`, since `t ∉ m ^ 2`. `R[1/t]` is a domain, so `U` is connected,
   and it is Noetherian.
2. `TameGaloisRealization.exists_galoisCover` applied to `ρ` gives a Galois
   cover `WA` of `U` with group `G`, `|G|` dividing `|H|`, such that any
   element of `π₁(U, x)` fixing a point of the fibre of `WA` is in the
   kernel of `ρ`. Since `H` is an `ℓ`-group, `n = |G| = ℓ ^ k` for some `k`,
   and `n` is a unit of `R` because `ℓ` is.
3. `TameRootSection.exists_root_section` gives an étale `R`-algebra `S`, a
   prime `z` over the maximal ideal, and a section `sB` of `WA` over the
   punctured Kummer cover `D(t) ⊆ Spec S[X]/(X ^ n - t)`.
4. `CyclotomicPowerCondition` at level `k` gives a residue automorphism `φ`
   with `φ ζ = ζ ^ q` on `ℓ ^ k`-th roots of unity.
   `CommutativeAlgebra.HenselianCyclotomicExtension.exists_extension` gives a
   finite étale `R`-algebra `R'` that is a domain with `R → R'` injective,
   `ζ : R'` of exact order `n` in the sense above, `α` with `α ζ = ζ ^ q`,
   and an `R`-algebra map `b : S → R'`. `t ≠ 0` in `R'` by injectivity.
5. `exists_coverX_hom` gives a map of covers `τ : coverX t R' n ⟶ toCover WA`.
6. `smul_coverU_eq` shows that `jg` acts trivially on the fibre of
   `coverU t R'`, so `exists_conj_fixed` gives `σ` and `p` with
   `δ • p = p`, where `δ = (jg ^ q)⁻¹ * (σ * jg * σ⁻¹)`.
7. Then `δ • (p ≫ τ) = (δ • p) ≫ τ = p ≫ τ`, so `ρ δ = 1` by step 2, that
   is, `ρ (σ * jg * σ⁻¹) = ρ (jg ^ q) = ρ jg ^ q`.

The element `σ` is an element of the Library's pointed fundamental group
`FundamentalGroup x (geometricFiberFinite x)` of `U` itself. The exponent
`q` is the given one, and only the level `k` with `ℓ ^ k = |G|` of the
cyclotomic condition is used.

## Dependencies

The proof imports the modules
`Langlands.AlgebraicGeometry.FiniteEtale.TameRootSection`,
`TameGaloisRealization`, `ConnectedCoverFiber`, `KummerCover` and
`StrictLocalCover`, and
`Langlands.CommutativeAlgebra.HenselianCyclotomicExtension`; the
fundamental group maps and their composition law come from
`Langlands.AlgebraicGeometry.FiniteEtale.Pullback`. Through these it
also uses the pinned `weil-conjectures` package: Galois covers, the
strictly Henselian root section and its étale descent (Stacks Project, Tag
0EYG), and the étaleness of `X ^ n - t`.
