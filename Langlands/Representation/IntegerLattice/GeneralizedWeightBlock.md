# Generalized-weight blocks and normalized generators

This module constructs the basis-free objects underlying the block step in
the proof of the proposition in David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.III,
printed pages 279–280 / one-based PDF pages 285–286. The governing source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both pages were read directly when writing this module.

All public names below are in `Langlands.IntegerLattice`. The module imports
`Langlands.Representation.IntegerLattice` unchanged and reuses its `Lattice`,
`generator`, `CommutingInvertibleTuple` and `tupleRepresentationEquiv`.

## What the source does

PDF285 starts with a finite-dimensional complex vector space `V` and pairwise
commuting invertible endomorphisms `u₁, ..., u_d`. It identifies them with
the representation `U(n) = u₁^{n₁} ∘ ... ∘ u_d^{n_d}` of `ℤ^d`. On a common
eigenspace with eigenvalues `z₁, ..., z_d`, `U(n)` acts by the character
`χ(n) = z₁^{n₁} ... z_d^{n_d}`. The source lists the distinct characters
`χ₁, ..., χ_l` obtained this way, each given by a tuple of nonzero complex
numbers.

PDF286 chooses a common triangularization basis in which every `U(n)` is
block diagonal, with upper-triangular blocks `A_j(n)` whose diagonal entries
are `χ_j(n)`. For the canonical basis `e_k` of `ℤ^d` it writes
`A_j(e_k) = z_k^{(j)} (Id + N_k^{(j)})`, where the `N_k^{(j)}` are strictly
upper triangular, hence nilpotent, and pairwise commuting. It then expands
`A_j(n)` as `χ_j(n)` times a product of powers of the `Id + N_i^{(j)}` and
uses the binomial series.

## What this module constructs

Fix `d : ℕ`, a type `V : Type u` with `[AddCommGroup V] [Module ℂ V]`, a
published tuple `A : CommutingInvertibleTuple d V` and a label tuple
`c : Fin d → ℂˣ`. Write `ρ = tupleRepresentationEquiv d V A`. This is the
actual representation of the integer lattice from the imported module.

The source's matrix blocks are replaced by the following basis-free
objects.

1. **The block.** `generalizedWeightBlock A c : Submodule ℂ V` is defined as

   ```lean
   ⨅ i : Fin d, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)
   ```

   This is the intersection over all coordinates of the maximal generalized
   eigenspaces of the actual tuple entries. In Mathlib,
   `f.maxGenEigenspace μ` is `genEigenspace f μ ⊤`, and its members are the
   vectors `v` with `((f - μ • 1) ^ k) v = 0` for some `k : ℕ`
   (`Module.End.mem_maxGenEigenspace`). `generalizedWeightBlock_eq` states
   the defining equation as a theorem, proved by `rfl`. Its right side is
   exactly the family written inline in
   `Langlands.CommutingTupleGeneralizedWeightDecompositionStatement` (staged
   statement candidate `769b13a0-1fbe-4050-b5ff-52ba2d69b320`). This module
   does not import that statement. `mem_generalizedWeightBlock` gives
   membership coordinatewise. `generalizedWeightBlock_rank_zero` shows that
   at `d = 0` the empty intersection is `⊤`, the whole space.

2. **Invariance and the restricted representation.**
   `commute_tupleRepresentationEquiv` proves
   `Commute (A.1 i : Module.End ℂ V) (ρ n)` for every coordinate `i` and
   every lattice point `n`. It rewrites `A.1 i` as `ρ (generator d i)` using
   the published `tupleRepresentationEquiv_generator`, and then maps the
   commutation of the two lattice points in the abelian lattice through `ρ`.
   `mapsTo_generalizedWeightBlock` then applies Mathlib's
   `Module.End.mapsTo_maxGenEigenspace_of_comm` in each coordinate and
   intersects. The result is `Set.MapsTo (ρ n) W W` for `W` the block.
   `generalizedWeightBlock_le_comap` restates this as
   `W ≤ W.comap (ρ n)`. The invariance is proved from the supplied commuting
   units themselves. It uses no finite dimension and no decomposition, and the
   caller supplies no invariance proof.

   `generalizedWeightBlockRepresentation A c :
   Representation ℂ (Lattice d) (generalizedWeightBlock A c)` is Mathlib's
   `Representation.subrepresentation` of `ρ` along this invariance. Each
   `ρc n` is the restriction `LinearMap.restrict` of `ρ n`. The ambient
   coercion equation, for every lattice point `n` and every `w` in the block,
   is

   ```lean
   ((generalizedWeightBlockRepresentation A c n w : generalizedWeightBlock A c) : V) =
     tupleRepresentationEquiv d V A n (w : V)
   ```

   (`generalizedWeightBlockRepresentation_apply_coe`, proved by `rfl`). Here
   `n` ranges over all of `Lattice d = Multiplicative (Fin d → ℤ)`, so
   negative and mixed-sign exponents are included. The inverse-action
   equations are about the unit `ρc.asGroupHom n` in
   `(Module.End ℂ (generalizedWeightBlock A c))ˣ`. The coercion to `V` of its
   inverse applied to `w` equals `ρ n⁻¹ (w : V)`
   (`generalizedWeightBlockRepresentation_asGroupHom_inv_apply_coe`). It also
   equals the inverse of the ambient unit `ρ.asGroupHom n` applied to `w`
   (`generalizedWeightBlockRepresentation_asGroupHom_inv_apply_coe'`). The
   two-sided laws `ρc n⁻¹ (ρc n w) = w` and `ρc n (ρc n⁻¹ w) = w` are
   `generalizedWeightBlockRepresentation_inv_self_apply` and
   `generalizedWeightBlockRepresentation_self_inv_apply`. Multiplicativity and
   the value `1` at the identity are the `map_mul` and `map_one` laws of the
   representation, which is a monoid homomorphism.
   `generalizedWeightBlockRepresentation_rank_zero` shows that at `d = 0`
   every restricted action is the identity, which is the empty product.

3. **Block generator units.** `generalizedWeightBlockGenerator A c i`, written
   `G_i`, is the unit `ρc.asGroupHom (generator d i)` in
   `(Module.End ℂ (generalizedWeightBlock A c))ˣ`. Its two-sided inverse is
   the one inherited from the restricted group representation.
   `coe_generalizedWeightBlockGenerator` and
   `coe_generalizedWeightBlockGenerator_inv` identify the underlying map of
   `G_i` with `ρc (generator d i)` and that of `G_i⁻¹` with
   `ρc (generator d i)⁻¹`. In `V`:

   - `generalizedWeightBlockGenerator_apply_coe`: the coercion of `G_i w` is
     `(A.1 i : Module.End ℂ V) (w : V)`;
   - `generalizedWeightBlockGenerator_inv_apply_coe`: the coercion of
     `G_i⁻¹ w` is `(((A.1 i)⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) (w : V)`.
     This uses the published `tupleRepresentationEquiv_asGroupHom_generator`
     to identify the ambient unit at `generator d i` with `A.1 i` itself.

4. **The coordinate character.** `coordinateCharacter c : Lattice d →* ℂˣ` is
   constructed directly. Its function is `n ↦ ∏ i : Fin d, c i ^ n.toAdd i`.
   The identity law holds because the lattice identity has all coordinates
   zero, so every factor is `c i ^ 0 = 1` (closed by `simp`). The
   multiplicativity law uses that lattice multiplication adds coordinates,
   together with `zpow_add` and `Finset.prod_mul_distrib` in the commutative
   group `ℂˣ`. The exponents are
   integers, so negative coordinates use the inverse in `ℂˣ`.

   - `coordinateCharacter_apply` gives the product formula (`rfl`);
   - `coe_coordinateCharacter` gives the same formula for the underlying
     complex number, `∏ i, (c i : ℂ) ^ n.toAdd i`;
   - `coordinateCharacter_generator` gives
     `coordinateCharacter c (generator d i) = c i`;
   - `coordinateCharacter_generator_inv` gives the value `(c i)⁻¹` at
     `(generator d i)⁻¹`;
   - `coordinateCharacter_rank_zero` shows that at `d = 0` the character is
     the empty product `1`.

   This is the source's `χ(n) = z₁^{n₁} ... z_d^{n_d}` with `z = c`. The
   existing `Langlands.IntegerLatticeExponentialPolynomial.consChar` in
   module `Langlands.Representation.MatrixCoefficient.IntegerLatticeProof`
   only adjoins one coordinate to a given character, so it is not reused
   here.

5. **Normalized generators and differences.**
   `normalizedBlockGenerator A c i`, written `U_i`, is the product of units

   ```lean
   Units.map (algebraMap ℂ (Module.End ℂ (generalizedWeightBlock A c))).toMonoidHom
       (c i)⁻¹ * generalizedWeightBlockGenerator A c i
   ```

   That is, the scalar unit `(c i)⁻¹`, sent into the block endomorphisms by
   the scalar algebra map, times `G_i`. The scalar normalization equations
   are:

   - `coe_normalizedBlockGenerator`:
     `(U_i : Module.End ℂ W) = (c i : ℂ)⁻¹ • (G_i : Module.End ℂ W)`;
   - `coe_normalizedBlockGenerator_inv`: the underlying map of `U_i⁻¹` is
     `(c i : ℂ) • ((G_i⁻¹ : (Module.End ℂ W)ˣ) : Module.End ℂ W)`;
   - `normalizedBlockGenerator_apply_coe` and
     `normalizedBlockGenerator_inv_apply_coe`: in `V`, `U_i` and `U_i⁻¹` act
     as `(c i : ℂ)⁻¹ • A.1 i` and `(c i : ℂ) • (A.1 i)⁻¹`.

   `normalizedGeneratorDifference A c i`, written `N_i`, is
   `(U_i : Module.End ℂ W) - 1`. The name is neutral: this module does
   **not** assert that `N_i` is nilpotent, nor that different `N_i` commute.
   The exported identities are:

   - `one_add_normalizedGeneratorDifference`: `1 + N_i = U_i`;
   - `generalizedWeightBlockGenerator_eq_smul`: the normalization identity
     `(G_i : Module.End ℂ W) = (c i : ℂ) • (1 + N_i)`, which is the
     basis-free form of the source's `A_j(e_k) = z_k^{(j)} (Id + N_k^{(j)})`;
   - `coe_generalizedWeightBlockGenerator_inv_eq_smul`: the inverse form
     `G_i⁻¹ = (c i : ℂ)⁻¹ • U_i⁻¹`;
   - `normalizedGeneratorDifference_apply_coe`: in `V`, `N_i w` is
     `(c i : ℂ)⁻¹ • A.1 i (w : V) - (w : V)`.

   These rely on `c i ≠ 0`, which holds because `c i` is a unit.

## Scope

The constructions hold for every `d : ℕ`, including `d = 0`, every label
tuple `c`, every carrier universe `u` and every complex vector space,
including zero spaces. A block may be zero, for example when `c` is not a
tuple of eigenvalues; every construction is still defined and the laws still
hold. No finite dimension, invariance hypothesis, decomposition, basis or
nilpotence hypothesis is assumed.

This is a basis-free extension of the source's finite-dimensional setting.
For finite-dimensional `V`, the same definitions apply with no extra
hypothesis, so they specialize to the source's setting. The labels here are
all tuples in `Fin d → ℂˣ`, not only the source's list of distinct common
eigenvalue tuples. Coordinates are indexed by `Fin d` from zero, matching the
source's `1, ..., d` after a shift by one.

## Provenance

The definitions are derived, not quoted. The source works with matrices in a
chosen common triangularization basis. This module replaces each matrix block
by the corresponding intersection of maximal generalized eigenspaces, with
the actual restricted lattice action on it. The source's scalar
`z_k^{(j)}` becomes the label `c i` and the source's `N_k^{(j)}` becomes the
difference `N_i`. The source's character `χ_j` becomes `coordinateCharacter`
evaluated at the label tuple. The ambient coercion, inverse and
normalization identities are the intrinsic laws of these constructions, and
the source uses them implicitly when it reads the matrix of `U(e_k)` on a
block.

For the errata check, the registered errata to the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
was read at PDF18–19. Its only C.III entry (old p. 322, l. -4) adds the
parentheses that group the whole scalar-times-unipotent factor
`z (Id + N)` under the power `n_i`. The 2026 PDF286 already prints those
parentheses. The constructions here do not depend on that formula.

## Separate obligations

This module does not prove, and should not be read as proving, any of the
following:

- finite nonzero support, independence or spanning of the blocks (the
  separate decomposition task);
- identification of nonzero blocks with common eigenvalue tuples;
- nilpotence or pairwise commutation of the differences `N_i`;
- common strictly upper-triangular bases or global block-basis assembly;
- the all-integer multivariable product factorization and its finite
  binomial expansion.
