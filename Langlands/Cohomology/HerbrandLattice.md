# Herbrand quotients of full lattices in a real representation

This module proves that two `G`-stable full lattices in the same finite-dimensional real
representation of a finite cyclic group `G` have the same Herbrand quotient. This is Milne,
*Class Field Theory*, Chapter VII, Lemma 3.5. It is infrastructure for the cyclic unit
calculation `[E : F] · h(O_E^×) = ∏ n_w`. That calculation is part of the first fundamental
inequality (Library targets `CyclicUnitHerbrandQuotient` and `CyclicIdeleClassHerbrandQuotient`)
in global class field theory (task fb66219f). This module proves no Library proposition by
itself. Its main theorem is meant for the content of statement task e92da4ea ("State
invariance of the cyclic Herbrand quotient for full invariant real lattices").

All declarations are in the namespace `Langlands.Cohomology.Herbrand`. The module builds on
`Langlands.Cohomology.HerbrandQuotient`, which supplies `HasHerbrandQuotient` and the
finite-cokernel invariance theorem `hasHerbrandQuotient_iff_of_injective`.

## Mathematical content and sources

Milne, *Class Field Theory* v4.03, Chapter VII §3, printed pp. 208–209 (PDF pp. 217–218),
has three lemmas.

- **Lemma 3.2.** Let `k ⊆ Ω` be fields with `k` infinite, and `M`, `N` finite-dimensional
  `k[G]`-modules. If `M ⊗ Ω ≅ N ⊗ Ω` over `Ω[G]`, then `M ≅ N` over `k[G]`. The proof writes
  `G`-homomorphisms as matrices `A` with `A B(σ) = C(σ) A`. A real isomorphism makes the
  polynomial `det(Σ aᵢ αᵢ)` nonzero, and a nonzero polynomial over an infinite field has a
  non-root.
- **Lemma 3.4.** If `M ⊗ ℚ ≅ N ⊗ ℚ` as `G`-modules, with `M`, `N` finitely generated over `ℤ`,
  then `h(M)` is defined iff `h(N)` is, and they are equal. The proof scales a rational
  isomorphism so that `α(M) ⊆ N` with finite index.
- **Lemma 3.5.** If `M`, `N` are `G`-stable full lattices in a real `G`-representation `V`,
  then `h(M)` is defined iff `h(N)` is, and they are equal. The canonical maps
  `M ⊗ ℝ → V ← N ⊗ ℝ` are `G`-isomorphisms, so Lemmas 3.2 and 3.4 apply.

Milne's footnote 2 on p.208 says that a full lattice in `V` is the `ℤ`-span of a basis of `V`.
Equivalently, it is finitely generated and `ℝ ⊗ M → V` is an isomorphism.

**The route of the Lean proof.** It combines Lemmas 3.2 and 3.4 into one integral step and
avoids rational base change.

1. Choose `ℤ`-bases `a` of `M` and `b` of `N`. They are also `ℝ`-bases `aR`, `bR` of `V`. Let
   `P(g)` and `Q(g)` be the integer matrices of `g` on `M` and `N`. Let `C` be the real matrix
   of `id_V` from `aR` to `bR`. Then `det C ≠ 0` and `Q(g) C = C P(g)` for all `g`.
2. **Descent** (`exists_intMatrix_det_ne_zero`). Let `c₁, …, c_r` be a `ℤ`-basis of the
   `ℤ`-span of the entries of `C`. That span is a finitely generated torsion-free subgroup of
   `ℝ`, hence free. Write `C = Σ_s c_s Y_s` with integer matrices `Y_s`. Since the `c_s` are
   linearly independent over `ℤ` and `P(g)`, `Q(g)` are integral, each `Y_s` satisfies
   `Q(g) Y_s = Y_s P(g)`. The polynomial `det(Σ_s X_s Y_s) ∈ ℤ[X_s]` takes the value
   `det C ≠ 0` at `X = c`, so it is a nonzero polynomial. Since `ℤ` is an infinite domain, it
   has a non-root `q ∈ ℤ^r` (`MvPolynomial.funext`). Then `X = Σ_s q_s Y_s` is an integer
   matrix with `det X ≠ 0` and `Q(g) X = X P(g)`. This is Milne's Lemma 3.2 argument, applied
   to the coefficients of `C` instead of a `k`-basis of the solution space. It also produces an
   integral solution directly, which is the scaling step of Lemma 3.4.
3. **Finite index** (`exists_injective_finite_coker`). `X` defines a `G`-equivariant map
   `φ : M → N`. Write `ψ` for the map defined by the adjugate `adj X`. Then
   `φ ∘ ψ = det X · id` and `ψ ∘ φ = det X · id`. Hence `φ` is injective because `M` is
   torsion-free. Its cokernel is a finitely generated `ℤ`-module killed by `det X`, hence
   finite (`Module.finite_of_fg_torsion`).
4. By Lemma 3.4's last step, which is `hasHerbrandQuotient_iff_of_injective` from
   `HerbrandQuotient`, `M` and `N` have the same Herbrand quotient.

Provenance: derived. The statement is Milne's Lemma 3.5. The following are internal to this
formalization:

- the coefficient-span form of the descent argument and the adjugate finite-index argument;
- the interface through Mathlib's `IsZLattice`;
- the predicate `IsEquivariantLatticeEquiv`;
- the helper `uliftIntLinearMap`.

## Conventions and scope

- **Groups and coefficients.** `G : Type u` is a group, and lattices are representations
  `A B : Rep (ULift.{u} ℤ) G`. `ULift.{u} ℤ` is the Library's
  `NormalizedTwoCocycle.CoefficientScalars.{u}`. For `G = Gal(E/F) : Type v`, this covers the
  published representations `augmentedFullLogUnitLatticeRepresentation F E` and
  `infinitePlaceCoordinateLatticeRepresentation F E`.
- **The real representation.** `V` is a real normed space of finite dimension, in an
  arbitrary universe. The action is any family `T : G → V →ₗ[ℝ] V` of real-linear maps.
  Neither the representation laws nor invertibility are needed for the theorems, so the
  hypothesis is weaker than "`G` acts on `V` by linear automorphisms".
- **Full lattices.** A full lattice is a `ℤ`-submodule `M ⊆ V` with Mathlib's
  `[DiscreteTopology M] [IsZLattice ℝ M]`: it is discrete and spans `V` over `ℝ`. In finite
  dimension these are exactly Milne's full lattices. Mathlib's `Basis.ofZLatticeBasis` turns
  any `ℤ`-basis of `M` into an `ℝ`-basis of `V`, and `Basis.ofZLatticeBasis_span` shows that
  `M` is its `ℤ`-span. Conversely, the `ℤ`-span of an `ℝ`-basis is an `IsZLattice`.
- **Identification with representations.** `IsEquivariantLatticeEquiv T A M e` (a `Prop`)
  says that the additive isomorphism `e : A ≃+ M` satisfies `e(ρ_A(g) x) = T(g)(e x)` in `V`.
  So `M` is `G`-stable and `A` is `M` with the restricted action. The published lattice
  representations satisfy this with `e = AddEquiv.refl _` and the proof `rfl`. A private
  compile test applied `natCard_of_isZLattice` to them in exactly this way.
- **Herbrand quotients and finiteness.** `HasHerbrandQuotient A q` asserts that `H¹(G, A)`
  and `H²(G, A)` are finite and `|H²(G, A)| = q · |H¹(G, A)|`. The theorems need
  `[Finite G] [IsCyclic G]`; the trivial group is included. `V = 0`, with empty bases, is
  included too.

## Declarations

### `Descent`

- `exists_intMatrix_det_ne_zero (P Q : G → Matrix κ κ ℤ) (C : Matrix κ κ ℝ) (hC : C.det ≠ 0)
  (h : ∀ g, Q_ℝ(g) * C = C * P_ℝ(g))`: there is `X : Matrix κ κ ℤ` with `X.det ≠ 0` and
  `Q g * X = X * P g` for all `g`. Here `Q_ℝ(g)` and `P_ℝ(g)` are the images of the integer
  matrices under `Int.castRingHom ℝ`. `G` is an arbitrary index type and `κ` is a finite type.

### `ULiftLinear`

- `uliftIntLinearMap f` (def) is an additive map between modules over `ULift ℤ`, viewed as a
  `ULift ℤ`-linear map. Linearity follows from `Int.cast_smul_eq_zsmul`.
- `uliftIntLinearMap_apply`: the linear map has the same values as `f`.

### `Bases`

The rest of the module removes the global instance `ULift.module`, the `ULift R`-module
structure induced from an `R`-module. This makes `Module (ULift ℤ) A` resolve to the
representation's own structure. The change is local to this file and does not affect any
statement.

- `repr_apply_eq_of_basis`: suppose `aR i = ι (a i)` for an integral basis `a` and a real
  basis `aR`. Then the real coordinates of `ι x` are the integral coordinates of `x`.
- `exists_injective_finite_coker`: let `A`, `B` have integral bases `a`, `b` indexed by the
  same finite type. Suppose they map, through additive maps `ιA`, `ιB` intertwining the
  actions with `T`, to real bases `aR`, `bR` of `V`. Then there is a morphism `f : A ⟶ B` in
  `Rep (ULift ℤ) G` that is injective and has finite cokernel `B ⧸ range f`.
- `hasHerbrandQuotient_iff_of_bases`: under the same hypotheses, with `G` finite cyclic,
  `HasHerbrandQuotient A q ↔ HasHerbrandQuotient B q` for every `q : ℚ`.

### `ZLattice` (`V` a finite-dimensional real normed space)

- `IsEquivariantLatticeEquiv T A M e` (def, `Prop`): see "Conventions" above.
- `exists_injective_finite_coker_of_isZLattice`: let `M`, `N` be full lattices with
  equivariant identifications `eA : A ≃+ M` and `eB : B ≃+ N`. Then there is an injective
  `f : A ⟶ B` with finite cokernel. The bases come from `Module.Free.chooseBasis`,
  `Basis.ofZLatticeBasis` and a reindexing by `Fintype.equivOfCardEq`; the two ranks are both
  `finrank ℝ V`.
- `hasHerbrandQuotient_iff_of_isZLattice` (Milne VII Lemma 3.5): with `G` finite cyclic,
  `HasHerbrandQuotient A q ↔ HasHerbrandQuotient B q` for every `q : ℚ`. So `h(A)` is defined
  iff `h(B)` is, and then they are equal.
- `natCard_of_isZLattice`: the division-free form required by task e92da4ea. It takes the
  hypotheses of `hasHerbrandQuotient_iff_of_isZLattice`, plus `[Finite (groupCohomology A 1)]`
  and `[Finite (groupCohomology A 2)]`. It concludes that `H¹(G, B)` and `H²(G, B)` are finite
  and `|H²(G, A)| · |H¹(G, B)| = |H²(G, B)| · |H¹(G, A)|` in `ℕ`. Swapping the roles of `A`
  and `B` gives the symmetric statement.
