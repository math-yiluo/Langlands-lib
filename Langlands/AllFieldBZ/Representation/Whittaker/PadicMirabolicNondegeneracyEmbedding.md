<!-- MANUAL -->
# Nondegenerate irreducible representations embed in good products (all fields)

Lean module: `Langlands.AllFieldBZ.Representation.Whittaker.PadicMirabolicNondegeneracyEmbedding`,
namespace `Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy`.

This helper module belongs to the proof of Bernstein–Zelevinsky 1977, Theorem 4.9, over an
arbitrary nonarchimedean local field (literature id `bernstein-zelevinsky-1977-induced-i`, printed
p. 456, PDF p. 17). The source deduces Theorem 4.9 from Theorem 4.11 as follows. Let `ω` be
irreducible and nondegenerate with support `ρ_1, …, ρ_r`. Order the `ρ_i` so that `ρ_j ≇ νρ_i` for
`i < j`, and put `π = ρ_1 × ⋯ × ρ_r`. An irreducible submodule `σ` of `π` is nondegenerate by
Theorem 4.11. Only one irreducible subquotient of `π` is nondegenerate (§4.7), so `ω ≅ σ`. This
module proves this step: `ω` is a subrepresentation of a product that satisfies the conclusion of
Theorem 4.11.

## Origin

Worker 5677 wrote this argument as the p-adic draft module
`Langlands.Representation.Whittaker.PadicMirabolicNondegeneracyEmbedding`, for `F : PadicField p`.
That draft is not published. This module is its mechanical all-field port, made by the port
script of Worker 71 with the systematic changes of the other all-field port modules, listed below.
Every declaration of the draft depends on the field, so the module neither imports nor uses the
draft. The module name keeps the draft's name.

## Setting

`F : Langlands.AllFieldBZ.LocalFieldPackage` and `T : F.TopologicalData` (the Library's
`Langlands.LocalFieldData F.Carrier`), with the topology `T.topology` on `F`. `ψ` is a unitary
additive character of `F` and `n : ℕ`. Representations are bundled smooth complex representations
`SmoothRep.{0, uF, max uF uV}` of `GL_(n+1)(F)`. This carrier universe is the one used by the
supercuspidal embedding and support theorems.

The predicate `Good T ψ P` is `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.Good`,
from the ported proof of Theorem 4.11. It says that:

1. the restriction of `P` to the mirabolic subgroup is homogeneous (`IsHomogeneous`): every
   nonzero subrepresentation has the same level as the whole representation;
2. the top derivative `(generalLinearDerivative T ψ (n+1) (n+1) le_rfl).obj P` has dimension one.

## Declarations

- `sigma_ne_of_ne T ρ σ h`: distinct cuspidal data have distinct pairs `⟨rank, class⟩` in
  `Σ d, SupercuspidalClass (n := d)`. The order hypothesis `Ordered` of the ported Theorem 4.11 is
  stated with these pairs.
- `exists_good_embedding T ψ n X hX hJX`: let `X` be irreducible (`hX`) with nonzero top
  derivative (`hJX`). Then there are `P` and an injective morphism `X ⟶ P` with `Good T ψ P`.

## Proof of `exists_good_embedding`

All named results below are the all-field versions in `Langlands.AllFieldBZ`, unless they are
field-independent Library results.

1. **Supercuspidal embedding.** `Classification.glSupercuspidalEmbedding` gives cuspidal data
   `ρ : Fin k → T.CuspidalDatum`, representatives `A i`, and an embedding of `X` into the product
   of the `A i` in the given order.
2. **Good order.** `exists_ordered_perm` gives a permutation `e` with `ρ (e j) ≠ ν ρ (e i)` for
   `i < j`. Put `ρ' = ρ ∘ e` and `A' = A ∘ e`. Let `P = T.cuspidalProductInduced ρ' h' A'` be the
   product in the new order. The order hypothesis `Ordered T B A'` follows from `sigma_ne_of_ne`.
   Since the ranks add up to `n + 1 > 0`, `k = l + 1` for some `l`. The lemma `good_product` (the
   homogeneous form of Theorem 4.11) gives `Good T ψ P`.
3. **An irreducible subrepresentation `Y` of `P`.** `P` is nonzero: its top derivative is nonzero
   (`nontrivial_top_of_good`, `Derivative.LevelCalculus.nontrivial_of_hasNonzeroDerivative`). `P`
   has finite length by `Classification.irreducibleProductFiniteLength`. Hence its group-algebra
   module is Artinian and has an atom `N` (`eq_bot_or_exists_atom_le`). `Y` is the smooth
   subrepresentation on `N`. It is irreducible because its module is isomorphic to the simple
   module `N`.
4. **`Y` is nondegenerate.** The restriction of `P` is homogeneous of level `n + 1`
   (`level_of_good`). So `Y`, a nonzero subrepresentation, has a nonzero derivative of order
   `n + 1` (`Derivative.hasNonzeroDerivative_of_isHomogeneous`). By
   `Derivative.RestrictionBridge.generalLinearDerivative_succ_obj_eq`, that is the top derivative
   of `Y`. This is the source's "Theorem 4.11 implies that `σ` is nondegenerate".
5. **`X ≅ Y`.** Both `X` and `Y` are irreducible subrepresentations of products of the `A' i`. So
   both have supercuspidal support `ρ'` (as a multiset; for `X` the reordering is
   `Equiv.Perm.ofFn_comp_perm`). This uses
   `LocalFieldPackage.TopologicalData.IsCuspidalSubrepresentation.isCuspidalConstituent`. Both have
   nonzero top derivative. `CuspidalSupport.fixedSupportDetectedEquiv` then gives an equivalence
   `E : X ≃ Y`. This replaces the source's appeal to §4.7: only one irreducible subquotient of a
   given support is nondegenerate.
6. The required morphism is `X → Y → P`, the composite of `E` with the inclusion. It is injective.

## Systematic changes from the p-adic draft

- `Langlands.PadicField.{u} p` becomes `Langlands.AllFieldBZ.LocalFieldPackage.{u}`; the prime
  `p` and its `Fact p.Prime` instance are removed from binders.
- The namespace `Langlands.Whittaker.PadicMirabolicNondegeneracy` becomes
  `Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy`, and references to ported Library
  declarations `Langlands.X` use their all-field versions `Langlands.AllFieldBZ.X`.

## Provenance

Mathematics: Worker 5677 (p-adic draft); generated by the all-field port script of Worker 71.
