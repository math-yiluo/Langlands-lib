# ℓ-adic slopes and the Swan conductor `s(V)`

Laumon (1987), (2.1.1)–(2.1.2.5), pp. 151–152, following Serre, *Local Fields*, IV §§2–3, and
Katz 1983, pp. 211–213. Let `K` be a local field with Galois group `G`, inertia `I` and wild
inertia `P` (the pro-`p` Sylow subgroup of `I`, the closure of the union of the upper
ramification groups `I^(λ)`, `λ > 0`), and write `I^(λ+)` for the closure of the union of the
`I^(λ+ε)`, `ε > 0`. A `G`-, `I`- or `P`-module is a finite-dimensional `ℚ̄_ℓ`-vector space with
an action defined over a finite extension of `ℚ_ℓ` and continuous for the `ℓ`-adic topology
(2.1.2). Then:

- Lemma (2.1.2.2): `P` acts on a `P`-module through a finite quotient, and `I^(λ)` acts
  trivially for `λ` large (Serre–Tate, p. 515, for the first assertion; `P` is pro-`p` and
  `ℓ ≠ p`).
- Corollary (2.1.2.3): every `P`-module is semisimple. A simple `P`-module `W` has a unique
  slope `λ ≥ 0` with `W^(I^(λ)) = 0` (if `λ > 0`) and `W^(I^(λ+)) = W`.
- (2.1.2.4): grouping the simple constituents by slope gives a canonical decomposition
  `V = ⊕_{λ ∈ Λ(V)} V_λ` with `V_λ` purely of slope `λ`, over the finite set `Λ(V)` of slopes.
- (2.1.2.5): the Swan conductor is `s(V) = Σ_λ λ · r(V_λ)`, `r` the dimension. For an `I`- or
  `G`-module the slopes and `s(V)` are those of its restriction to `P`, and the decomposition is
  one of `I`- or `G`-modules.

Katz describes the same data by the multiplicity function (p. 212): `φ(r) = 0` for `r < 0`,
`φ(0) = dim V^P` and, for `r > 0`, `φ(r) = lim_{ε→0+} dim (V^(I^(r+ε)) / V^(I^(r−ε)))`, with
`Swan(V) = Σ r φ(r)`. Here the lower invariants may be taken at `r` itself. Since `P` acts
through a finite quotient, the subgroups `I^(r−ε)` (for `0 < ε < r`) act through the images of
the finite upper groups `Gal(L/K)^(r−ε)` (Serre IV §3, Proposition 14, p. 74). This finite
upper filtration is left-continuous with finitely many jumps (it is `G_ψ(v)`, with lower groups
`G_u = G_⌈u⌉` and `ψ` continuous increasing, Serre IV §3, pp. 73–74). So for small `ε > 0`
the image of `I^(r−ε)` is that of `I^(r)`, `V^(I^(r−ε)) = V^(I^(r))`, and
`φ(r) = lim_{ε→0+} dim V^(I^(r+ε)) − dim V^(I^(r))`. This is the form used below.

## Place in the design

This module carries out the row `Slopes` of §4.1 of the [design note for Laumon's local Fourier bijection](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md), with its declarations
`WildImageFiniteStatement`, `slopeSummand`, `slopeSupport`, `ladicSwan` and
`SlopesExactStatement`. The definitions `upperPlusRamificationGroup`, `finiteLevelUpperGroup` and
`finiteSlopeSummand` are added: the groups `G^(u+)` of Laumon (2.1.1), and the finite-level form of
the summands used to state their independence of the finite quotient.

## Conventions

`K` is a nonarchimedean local field in the Library's sense (either characteristic),
`Ω` a separable closure, `ℓ` a prime and `E = PadicAlgCl ℓ`. The upper ramification groups are
the Library's `Langlands.Ramification.Local.localAbsoluteUpperRamificationGroup K Ω u`
(written `G^u`) and wild inertia is `Langlands.Ramification.Local.localWildInertia K Ω`
(written `P`), both of `Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute`.

A representation is a `Langlands.FiniteRepresentation E H` of a group `H` together with a
homomorphism `f : H →* (Ω ≃ₐ[K] Ω)`; the groups `G^u` act through `f`, that is, as their
preimages `(G^u).comap f`. The statements take `f` to be a topological embedding whose image
contains `P` (and, where Laumon works with `I`-modules, the inertia group
`Langlands.LocalGalois.SepClosed.absoluteInertia K Ω`). The two cases used are `G`-modules
(`H = Ω ≃ₐ[K] Ω`, `f = MonoidHom.id _`) and `I`-modules (`H` the inertia subgroup, `f` its
inclusion). Continuity and the finite model are the Library's
`Langlands.Henniart.LocalNumerical.IsLadicContinuous` and
`Langlands.Henniart.LocalNumerical.IsLadicDefinedOverFiniteExtension`. The hypothesis
`ℓ ≠ p` is written `((ℓ : ℕ) : 𝓀[K]) ≠ 0`, as in `Langlands.Henniart.LadicFiniteInertiaStatement`.

## Definitions

- `upperPlusRamificationGroup K Ω u` is `G^(u+)`, the topological closure of the supremum of
  the `G^v`, `v > u`. At `u = 0` it is, by unfolding the definitions, the Library's
  `localWildInertia K Ω` (the equation holds by `rfl`).
- `finiteLevelUpperGroup K Ω L v`, for a finite Galois subextension `L` of `Ω`, is the subgroup
  of elements of `P` whose restriction to `L` (`absoluteFiniteRestriction K Ω L`) lies in the
  finite upper ramification group `Langlands.Ramification.Local.localUpperRamificationGroup K L v`
  of `Gal(L/K)`.
- `slopeSummand f A μ`, for real `μ`, is the slope-`μ` summand `V_μ` of `V = A`:
  - `V^P`, the vectors fixed by `P` (through `f`), at `μ = 0`;
  - for `μ > 0`, the intersection of the vectors fixed by `G^(μ+)` with
    `Representation.Coinvariants.ker` of the restriction of the action to `G^μ`, the span of
    the vectors `g v − v`, `g ∈ G^μ`;
  - `0` for `μ < 0`.
  Fixed vectors are the Library's `Langlands.fixedVectors`.
- `finiteSlopeSummand f L A μ` is the same construction with `finiteLevelUpperGroup K Ω L v`
  in place of `G^v` and the supremum over `v > μ` without closure.
- `slopeSupport f A` is the set `Λ(V)` of real `μ` with `V_μ ≠ 0`.
- `ladicSwan f A` is Laumon's `s(V) = Σ_μ μ · dim V_μ`, as the real `finsum` over all `μ`
  of `μ · finrank V_μ`. A `finsum` with infinitely many nonzero terms is `0`; that the support is
  finite is the first clause of `SlopesExactStatement`.

### Comparison with Laumon's definition

Laumon defines the slope of a simple `P`-module and groups constituents; the definition here
gives each summand directly as a subspace, so that no finiteness or semisimplicity is needed to
form it. When `P` acts through a finite group, as `WildImageFiniteStatement` asserts, the
characteristic-zero averaging projector of a finite group `Q` splits `V = V^Q ⊕ (Σ (g v − v))`,
and on a simple `P`-module `W` of slope `ν` the vectors fixed by `G^(μ+)` are `W` if `ν ≤ μ`
and `0` otherwise, while the span of the `g w − w`, `g ∈ G^μ` (`μ > 0`), is `W` if `ν ≥ μ`
and `0` otherwise. So the summand at `μ` collects exactly the constituents of slope `μ`.
`SlopesExactStatement` states the resulting properties: the summands form a direct sum
decomposition into `H`-stable subspaces, `V_μ` is fixed by `G^(μ+)` by definition and has no
nonzero vector fixed by `G^μ` for `μ > 0`. A decomposition with these properties is unique, so
it is Laumon's (2.1.2.4); its dimensions are Katz's multiplicities.

The slopes are indexed by real numbers, as in Laumon (2.1.2.3), p. 152, where `λ ∈ ℝ₊`. For
inertia modules, Laumon's Théorème (2.1.2.6), p. 153, proves that the slopes are rational and
that the product of each slope and its multiplicity is an integer; by restriction this also
applies to Galois modules. This module states no rationality result.

## `WildImageFiniteStatement`

Laumon (2.1.2.2). For `ℓ ≠ p`, `f` an embedding with image containing `P`, and `A`
continuous with a finite model:

1. there is a finite Galois subextension `L` such that every `h` with `f h ∈ P` and trivial
   restriction to `L` acts trivially: the action of `P` factors through the finite quotient
   `P / (P ∩ Gal(Ω/L))`;
2. the image of `P` (through `f`) in the endomorphisms of `V` is finite;
3. some `G^u`, `u > 0`, acts trivially.

## `SlopesExactStatement`

Laumon (2.1.2.3)–(2.1.2.5) and the paragraph after Théorème (2.1.2.6), pp. 152–153, for
`ℓ ≠ p` and `f` an embedding with image containing `P`:

1. For every continuous `A` with a finite model:
   - the set of slopes is finite;
   - `V = ⊕_μ V_μ`, an internal direct sum (`DirectSum.IsInternal`) over all real `μ`;
   - every `V_μ` is stable under all of `H` (for `G`-modules, under the whole Galois group);
   - for `μ > 0`, `V_μ` meets the vectors fixed by `G^μ` only in `0`;
   - for every finite Galois subextension `L` through which the action of `P` factors (as in
     clause 1 of `WildImageFiniteStatement`), `finiteSlopeSummand f L A μ = slopeSummand f A μ`
     for all `μ`: the summands do not depend on the finite quotient of `P` used to compute
     them, and are computed from the finite upper groups `Gal(L/K)^v`;
   - `V` is tame, that is, `P` acts trivially, if and only if its slopes lie in `{0}`
     (Laumon (2.1.4), (i) ⇔ (ii)).
2. Every intertwiner `A → B` between such representations maps `A_μ` into `B_μ`.
3. For a short exact sequence `0 → A → B → C → 0` of such representations (intertwiners
   `i`, `q` with `i` injective, `q` surjective and `range i = ker q`) and every `μ`:
   `i(A_μ) = B_μ ∩ i(A)`, `q(B_μ) = C_μ` and `dim B_μ = dim A_μ + dim C_μ`; and
   `s(B) = s(A) + s(C)`. These are the exactness of Laumon's projectors `V ↦ V_Λ` and the
   additivity of `r` and `s`.

The definitions involve no finite quotient. The clause on finite levels is the form taken here
by the independence of the finite model of the wild action; it rests on the surjectivity of
`G^v → Gal(L/K)^v` (Serre IV §3, Proposition 14, p. 74).

## Generality

The definitions and both statements are for all nonarchimedean local fields, of either
characteristic, and every `ℓ ≠ p`. Laumon (2.1.1) works with henselian traits of equal
characteristic; the completed end traits of `Langlands.Correspondence.Laumon.Traits`, with
`K = LaurentSeries k`, are a case of these statements.

## Inputs of the proofs

This module states the results and does not prove them. The proof route of Laumon and of the
sources above uses the following, none of which this module's Lean refers to:

- for `WildImageFiniteStatement`, a stable lattice of the finite model over the ring of integers
  of a finite extension of `ℚ_ℓ` (weil-conjectures `PadicAlgCl.exists_finiteDimensional_forall_mem`
  and `PadicAlgCl.exists_lattice_of_forall_mem`), the open-kernel theorem
  `exists_isOpen_forall_eq_one_of_tendsto_pow_prime_pow` of weil-conjectures for a continuous
  action of a group in which `g^(p^n) → 1`, applied on wild inertia, which is pro-`p` (at finite
  levels the first lower group is a `p`-group,
  `Langlands.Ramification.isPGroup_lowerGroup_one`), and compactness of `P`;
- for `SlopesExactStatement`, the finite-image theorem
  `Langlands.Ramification.Wintenberger.localAbsoluteUpperFiniteImage` (the absolute `G^v` maps
  onto `Gal(L/K)^v` for `v ≥ −1`), the finite-to-finite compatibility
  `Langlands.Ramification.Local.upperQuotientCompatibility`, and averaging projectors over the
  finite images, whose multiplicity calculation is that of
  `Langlands.Ramification.Local.upperBreakMultiplicities` (with complex coefficients) in
  `Langlands.LocalFactor.Ramification.Breaks`.

These weil-conjectures declarations are at commit `a25955cde4f85f67bef3149a6efc3efe20c22132`;
under `#print axioms` each of the three weil-conjectures declarations listed reports only
`propext`, `Classical.choice` and `Quot.sound`, as do the four Library declarations named.

## Declarations used

The module imports `Langlands.Correspondence.HenniartLadicClasses`,
`Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute`,
`Langlands.Representation.Smooth.Definitions` and Mathlib. It uses the Library's
`localAbsoluteUpperRamificationGroup`, `localWildInertia`, `localUpperRamificationGroup`,
`absoluteFiniteRestriction`, `Langlands.fixedVectors`, `Langlands.FiniteRepresentation`,
`IsLadicContinuous` and `IsLadicDefinedOverFiniteExtension`, and Mathlib's
`Representation.Coinvariants.ker`, `finsum` and `DirectSum.IsInternal`. It uses no declaration
of weil-conjectures. Every declaration of this module depends at most on `propext`,
`Classical.choice` and `Quot.sound`.
