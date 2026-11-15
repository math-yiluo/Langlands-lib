# Proof: rational surjectivity of torus quotients with torus kernel

Worker 175.

`Langlands.GroupScheme.torusQuotientRationalSurjectivity` proves exactly
[`TorusQuotientRationalSurjectivityStatement.{u}`](QuotientRationalSurjectivityStatement.md)
for an arbitrary universe `u`. Let `k : Type u` be a field with
`HasTrivialTorusCocycles k`. Let `B` and `C` be group schemes over `Spec k`
that are tori, and let `q : B ⟶ C` be a homomorphism whose underlying scheme
map is surjective and whose full scheme-theoretic kernel `kernel q` is a
torus. Then `rationalPoints.map q : B(k) → C(k)` is surjective. The theorem
adds no hypothesis to the published proposition. The proof uses only
published Library results and Mathlib.

## Route

The source argument is the cohomology sequence
`B(k) → C(k) → H^1(k, kernel q) = 1` (Kaletha–Prasad, proof of Corollary
B.8.6). The Lean proof carries out this argument directly with actual
cocycles on the cover `Spec L → Spec k`, where `L` is one finite Galois
splitting field of `B` and `C`. It does not construct the fibre of `q` as a
torsor. It first lifts the given point of `C` to an `L`-point of `B`. The
coboundary of this lift is a cocycle valued in `kernel q`, which is trivial
by `HasTrivialTorusCocycles`. Correcting the lift by the trivializing point
gives an `L`-point that descends to `k`.

## Helper 1: split tori (`rationalPoints_surjective_of_split`)

Let `K` be a field, let `T` and `Q` be commutative group schemes over
`Spec K` whose underlying group schemes are split tori, and let `f : T ⟶ Q`
be a homomorphism whose group-scheme homomorphism is an epimorphism and whose
kernel is smooth with connected underlying space. Then `f` is surjective on
rational points.

By `IsSplitTorus.exists_cocharacterPoints_prod`, there are finitely many
cocharacters `ν_j` of `Q` such that every rational point `t` of `Q` is a
product `∏ ν_j(x_j)` with units `x_j ∈ Kˣ`. The published lemma
`IsSplitTorus.cocharacter_surjective_of_smooth_connected_kernel`, in the
chosen form `IsSplitTorus.cocharacterLiftOfSmoothConnectedKernel` with
`..._comp`, gives cocharacters `μ_j` of `T` with `μ_j ≫ f = ν_j`. The point
`∏ μ_j(x_j)` of `T` maps to `t`: `rationalPoints.map f` is a monoid
homomorphism (`map_prod`), and on each factor the identity `μ_j ≫ f = ν_j`
gives `f(μ_j(x_j)) = ν_j(x_j)` after unfolding
`CocharacterUniformizer.cocharacterPoints`.

## Helper 2: base change to a splitting field (`baseChange_rationalPoints_surjective`)

Let `B`, `C` be tori over `Spec k`, let `q : B ⟶ C` be scheme-surjective
with torus kernel, and let `L` be a field extension of `k` over which `B` and
`C` split (`IsSplitTorus` of `GaloisPointComparison.baseChanged k L B` and
`... C`). Then the base change of `q` along
`b = GaloisPointComparison.baseMap k L : Spec L ⟶ Spec k` is surjective on
`L`-rational points.

The proof applies Helper 1 over `L`:

- `B` and `C` become commutative group schemes `Bc`, `Cc` via
  `IsTorus.isCommMonObj`. The homomorphism `q` becomes `f : Bc ⟶ Cc`, and
  `fL` is its image under `CommGroupScheme.baseChange b`.
- The base-changed scheme map is surjective. By `baseChange_map_isPullback`
  it is a pullback of `q`'s scheme map, and surjectivity is stable under
  base change (`MorphismProperty.of_isPullback`).
- `fL` is an epimorphism by `IsTorus.epi_of_surjective_hom`. The two base
  changes are tori because they are split.
- The kernel of the base-changed map is a torus. The base change of
  `kernel q` is a torus (`IsTorus.baseChange`), and `kernelBaseChangeIso`
  identifies it with the kernel of the base-changed map
  (`IsTorus.of_iso`). A torus is smooth (`IsTorus.smooth`) and connected
  (`IsTorus.connectedSpace`), which gives the instances Helper 1 needs.

## Main theorem (`torusQuotientRationalSurjectivity`)

Fix `k`, `B`, `C`, `q` and a rational point `c` of `C`.

1. **Splitting field.** `IsTorus.commonFiniteGaloisSplitting` chooses a
   finite Galois extension `L/k` over which both `B` and `C` split. Write
   `b : Spec L ⟶ Spec k` and `U = Over.mk b`, with structure map
   `π : U ⟶ Spec k` over `Spec k`.
2. **A lift over `L`.** Helper 2 gives an `L`-rational point `bL` of the base
   change of `B` mapping to the base change `baseChangeSectionHom b C c` of
   `c`. The equivalence `baseChangeBasePointsEquiv b B` turns it into a point
   `b₁ : U ⟶ B` over `Spec k`. Naturality (`baseChangeBasePointsEquiv_comp`)
   gives `b₁ ≫ q = π ≫ c`.
3. **The kernel cocycle.** Any two points `a, a' : Z ⟶ U` over a test scheme
   `Z` satisfy `a ≫ π = a' ≫ π`, because both are morphisms over `Spec k`.
   So the coboundary `(a, a') ↦ (a ≫ b₁)(a' ≫ b₁)⁻¹` (`Cocycle.coboundary b₁`)
   is killed by `q`. By `mem_range_kernelι_iff`, each value factors through
   `kernelι q`. `Cocycle.lift` turns the coboundary into a cocycle `ξ` of
   `kernel q` on `U`.
4. **Triviality.** `kernel q` is a torus and `L/k` is finite Galois, so
   `HasTrivialTorusCocycles k` makes `ξ` trivial: there is `g : U ⟶ kernel q`
   with `ξ(a, a') = (a ≫ g)(a' ≫ g)⁻¹`. Put `fk = g ≫ kernelι q`. Then
   `Cocycle.lift_toFun` gives
   `(a ≫ b₁)(a' ≫ b₁)⁻¹ = (a ≫ fk)(a' ≫ fk)⁻¹`, and `fk ≫ q = 1`.
5. **Corrected lift.** Let `b₂ = fk⁻¹ * b₁`. A group calculation from step 4
   gives `a ≫ b₂ = a' ≫ b₂` for all `a, a' : Z ⟶ U`. Since `fk ≫ q = 1`, also
   `b₂ ≫ q = π ≫ c`.
6. **Descent.** `Spec L ⟶ Spec k` is surjective, flat and quasi-compact
   (`fieldExtension_fpqc`). Mathlib's instance in
   `Mathlib.AlgebraicGeometry.Sites.Fpqc` therefore makes it an effective
   epimorphism. `exists_section_of_forall_eq` (in
   `Langlands.GroupScheme.TorsorCocycle`) descends `b₂` to a section
   `s : Spec k ⟶ B` with `b ≫ s = b₂.left`. This section is the required
   rational point of `B`. Its image under `q` equals `c`, by cancelling the
   epimorphism `b` and using `b₂ ≫ q = π ≫ c`.

## Verification

The module compiles with 0 errors and 0 warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. Declaration inspection reports only
the axioms `propext`, `Classical.choice` and `Quot.sound`. The published
statement pair and its imports are unchanged.
