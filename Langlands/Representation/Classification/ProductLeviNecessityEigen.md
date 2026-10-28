# Eigenvectors of compressions from generalized Jacquet exponents

Author: Worker 819.

This module is a helper for the proof of
`Langlands.GLProductLeviTemperedExponentNecessityStatement`
(see [`ProductLeviTemperedExponentNecessityStatement`](ProductLeviTemperedExponentNecessityStatement.md)).
Its declarations are in the namespace `Langlands.ProductLeviNecessity`. It turns
a generalized eigencharacter of the upper normalized refined Jacquet module
into explicit matrix coefficients of the original representation of the
product Levi `C.Levi F.Carrier`.

## Statements

Throughout, `C : BlockShape n`, `D : BlockRefinement C`, and for a nested tuple
`c : ∀ i, Fin (D i).length → F.Carrierˣ` the element `g_c` of the Levi is
`fun i => (D i).blockScalar F.Carrier (c i)`. The compression
`Jacquet.compressedAction ρ hρ KP hKP g` (module
`Representation/Jacquet/CanonicalLiftDefinitions`) is the operator
`x ↦ e_KP (ρ g x)` on the `KP`-fixed vectors, where `e_KP` averages over the
compact open subgroup `KP`. The subgroup `KP` is
`CuspidalSupport.leviPiOpenSubgroup T C K`, the product of compact open
subgroups `K i` of the factors.

- `isWeaklyContracting_mul`, `isWeaklyContracting_pow`: weakly contracting
  block-scalar tuples are closed under products and natural powers.
- `compressedAction_commute`: when every `K i` has a block-Iwahori factorization
  for `D i`, the compressions by two weakly contracting tuples commute.
- `compressedAction_pow`: under the same hypothesis, the compression by
  `g_c ^ m` is the `m`-th power of the compression by `g_c`.
- `compressionEigenvalue T C D ψ c` is the complex number
  `√δ(c) * ψ(flatScalars C D c)`, where `δ` is `T.refinedLeviModulus C D`
  evaluated at the refined-Levi element of the flattened tuple.
- `exists_compressedAction_eigenvector`: let `ρ` be admissible and let `ψ` be a
  generalized eigencharacter of the pullback of `T.normalizedRefinedJacquet C D ρ`
  through `flattenedLeviEquiv` and the flattened `blockScalarLevi`, exactly the
  pullback of the target statement. Let `U` be a neighbourhood of `1` in the
  Levi and `c` a weakly contracting nested tuple. Then there are compact open
  subgroups `K i` with block-Iwahori factorizations for every block shape, with
  `KP ⊆ U`, and a nonzero `KP`-fixed vector `x` with
  `compressedAction (g_c) x = compressionEigenvalue T C D ψ c • x`.
- `exists_eigen_coefficient`: under the same hypotheses there are a compact open
  subgroup `K ⊆ U` of the Levi, a vector `x` fixed by `K`, and a smooth
  functional `ℓ : SmoothDual ρ` invariant under `K` with `ℓ x ≠ 0`, such that
  `ℓ (ρ (g_c ^ m) x) = λ ^ m * ℓ x` for every `m : ℕ`, where
  `λ = compressionEigenvalue T C D ψ c`.

## Proofs

`compressedAction_commute` and `compressedAction_pow` use the first half of the
published `Jacquet.refinedUpperCompression` (module
`Representation/Jacquet/RefinedUpperCompressionProof`): compression is
multiplicative on weakly contracting block-scalar tuples. Since block scalars
commute, the two products in either order agree. The power statement is an
induction on `m`, with `Jacquet.compressedAction_one` as base case.

`exists_compressedAction_eigenvector`:

1. `isGeneralizedEigencharacter_iff` (module `Representation/Exponents/Jacquet`)
   gives an exponent `k` and a nonzero Jacquet class `w0` in the generalized
   character space of `ψ` of order `k`. Lift `w0` to a smooth vector `v0` and
   choose an open subgroup `U0` fixing `v0`.
2. `CuspidalSupport.exists_leviPiOpenSubgroup_subset_forall` (module
   `Representation/CuspidalSupport/UniformBlockIwahoriBasis`) gives compact open
   `K i` whose product lies in `U ∩ U0` and which have block-Iwahori
   factorizations for every block shape.
3. Let `Y` be the vectors of the unnormalized Jacquet module fixed by `KP ∩ M`,
   where `M` is the refined Levi, and `W = Y ⊓ characterSpace π ψ k`. The
   space `W` contains the class of `v0`. It is stable under the pulled-back
   normalized action `π`, because block scalars commute with the refined Levi.
   For `b0 = flatScalars C D c`, the operator `π b0 - ψ(b0)` is nilpotent on `W`.
   So the published `exists_mem_ker_of_pow_eq_zero` (module
   `Representation/Exponents/JacquetEigenvectorProof`) gives a nonzero `w ∈ W`
   with `π b0 w = ψ(b0) w`. Undoing the inverse half-modulus normalization
   (`refinedLeviInverseHalfModulus_apply`), the unnormalized action of `g_c`
   multiplies `w` by `λ`.
4. Choose a strictly contracting nested tuple `c0` from
   `(D i).deepChamberNonempty`. The published
   `Jacquet.refinedStableImageJacquetBijective` (module
   `Representation/Jacquet/RefinedUpperCanonicalLiftProof`) says that the
   Jacquet map from the stable image of the compression by `g_{c0}` onto `Y` is
   bijective. Let `x` be the preimage of `w`; it is nonzero.
5. The compression `A` by `g_c` commutes with the compression by `g_{c0}`, so it
   preserves the stable image. The second half of `refinedUpperCompression`
   says that the Jacquet map intertwines `A` with the action of `g_c` on `Y`.
   Hence `A x` and `λ x` have the same image `λ w`. Injectivity gives
   `A x = λ x`.

`exists_eigen_coefficient` takes `K = KP` and `x` from the previous lemma.
Choose any linear functional `ℓ0` with `ℓ0 x ≠ 0`, and set
`ℓ = ℓ0 ∘ Compact.averageMap ρ _ KP _`. By `Jacquet.averageMap_apply_of_mem`
(module `Representation/Jacquet/StablePairingProof`), `ℓ` is `KP`-invariant,
hence smooth for the dual action. Since `x` is `KP`-fixed, `ℓ x = ℓ0 x`. Then
`ℓ (ρ (g_c ^ m) x) = ℓ0 ((A ^ m) x) = λ ^ m ℓ0 x` by `compressedAction_pow`.

## Provenance

This is the Lean form of Casselman's construction: a Jacquet exponent produces
an eigenvector of the Hecke-type operator `e_K ρ(a) e_K` on `K`-fixed vectors,
and hence a matrix coefficient which is geometric along the powers of `a`
(Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, §4; Waldspurger 2003, I.4 and III.2). The
implementation reuses the Library's refined upper compression and canonical
lift results. It does not use Waldspurger's `Xi` function.
