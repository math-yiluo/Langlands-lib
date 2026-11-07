# Herbrand's tower laws for independently presented intermediate fields

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.TowerProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`.

## What the module proves

Let `K`, `E`, `L` be actual `PadicField`s. The setting is that of the tower clauses of the
Library module `Langlands.LocalFactor.Ramification.Herbrand.ArithmeticStatement`:
algebras `K → L`, `K → E`, `E → L`, the p-adic towers through `K`, the tower
`K → E → L`, and `L/K`, `E/K`, `L/E` Galois. Let `T : L.TopologicalData` and
`S : E.TopologicalData` be arbitrary realizations. Here `E` is an independently presented
field with its own algebra map into `L`, not an intermediate field of `L`. The module
proves three Library propositions for all such data, with no further hypotheses:

- `herbrandPhiTower K L E T S : Padic.HerbrandPhiTower K L E T S`. For `u ≥ -1`,
  `φ_{L/K}(u) = φ_{E/K}(φ_{L/E}(u))`. The equation is proved for every real `u` as
  `herbrandPhi_tower`.
- `herbrandPsiTower K L E T S : Padic.HerbrandPsiTower K L E T S`. For `v ≥ -1`,
  `ψ_{L/K}(v) = ψ_{L/E}(ψ_{E/K}(v))`. It is proved for every real `v` as
  `herbrandPsi_tower`.
- `upperRestrictionCompatibility K L E T S : Padic.UpperRestrictionCompatibility K L E T S`.
  For `v ≥ -1`, the image of `Gal(L/K)^v` under the actual normal restriction
  `AlgEquiv.restrictNormalHom E.Carrier` is `Gal(E/K)^v`. As in the Library proposition,
  the hypothesis `IsScalarTower (Padic p) E.Carrier L.Carrier` is not taken. It follows
  from the other towers (`padicScalarTower_of_tower`).

Here `φ_{L/K} = Padic.herbrandPhi T K.Carrier`, `φ_{L/E} = Padic.herbrandPhi T E.Carrier`,
`φ_{E/K} = Padic.herbrandPhi S K.Carrier`, and the same for `ψ`.

Named definitions:

- `towerKernel K L E`: the kernel of `AlgEquiv.restrictNormalHom E.Carrier` on
  `Gal(L/K)`.
- `towerSubgroupEquiv K L E : Gal(L/E) ≃* towerKernel K L E`. It sends `τ` to
  `τ.restrictScalars K`; the inverse keeps the ring isomorphism. An element of the kernel
  fixes the image of `E` (`algebraMap_fixed_of_mem_towerKernel`), and a restricted
  automorphism lies in the kernel (`restrictScalars_mem_towerKernel`). Both use
  `AlgEquiv.restrictNormal_commutes`.
- `towerIntegerHom K L E T S : S.Integers →+* FixedPoints.subring T.Integers (towerKernel K L E)`
  is `algebraMap E L` restricted to integers, and `towerIntegerEquiv` is its inverse ring
  isomorphism. The action of `Gal(L/K)` on `T.Integers` is `Padic.integerAction T K.Carrier`.
- `towerQuotientEquiv K L E : Gal(L/K) ⧸ towerKernel K L E ≃* Gal(E/K)` is
  `QuotientGroup.quotientKerEquivOfSurjective` applied to the surjective restriction.

## Sources

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Chapter IV, §3,
Propositions 14 and 15 (printed p. 74), proofs on printed p. 75. The Library statement
module cites the same places. The proofs specialize the ported Anthropic FLT theorems in
`Langlands.AnthropicFLT` (accepted candidate `cf07dc37-888b-4c8a-8bc0-81226d21710e`).
They also reuse the transport and comparison lemmas of `QuotientProof` (staged
candidate `301ebebb-9ba4-46b1-8ca7-3ba077f298a3`). All declarations listed above are
internal identifications.

## Proof (as implemented)

1. **Kernel and `Gal(L/E)`.** Write `N = towerKernel K L E`; it is normal as a kernel.
   `towerSubgroupEquiv` preserves the underlying maps of `L`. So the actions on
   `T.Integers` agree (`Subtype.ext rfl`), and `QuotientProof`'s
   `lowerRamificationCard_of_equivariant` gives `lowerGroupOrder_tower`. These are the
   Library orders of `L/E`, equal to the source orders of `N`.
2. **Integer rings.** `towerIntegerHom` is well defined by
   `PadicField.TopologicalData.relative_mem_integers_iff S T` and step 1. It is injective
   because `algebraMap E L` is injective. It is surjective because a point of `L` fixed by
   `N`, hence by all of `Gal(L/E)`, is in the range of `algebraMap E L`
   (`InfiniteGalois.mem_range_algebraMap_iff_fixed`, using `L/E` Galois). Integrality of
   the preimage again follows from `relative_mem_integers_iff`.
3. **Equivariance.** `towerIntegerHom (restrictNormalHom E σ • x) = (mk σ) • towerIntegerHom x`
   (`towerIntegerHom_smul`, by `AlgEquiv.restrictNormal_commutes`). By injectivity this
   transfers to `towerIntegerEquiv` and `towerQuotientEquiv` (`towerIntegerEquiv_smul`).
   With the transport lemmas of `QuotientProof`, this gives `map_restrictNormalHom_eq_tower`
   (images of lower groups) and `lowerGroupOrder_towerQuotient` (orders of `E/K`).
4. **φ tower** (`herbrandPhi_tower`). This is the argument of `QuotientProof`'s
   `herbrandPhi_fixedField_tower` with `N` in place of `H`. For rational `u ≤ 0` all three
   functions are the identity. For rational `u > 0` they are the source functions
   (`herbrandPhi_ratCast` with the order identities of steps 1 and 3), and the ported
   φ-transitivity theorem applies. Then continuity and density of `ℚ` in `ℝ` finish.
5. **ψ tower** (`herbrandPsi_tower`). `φ_{L/K}` is injective. Applying it to both sides and
   using step 4 and `Padic.herbrandPhi_herbrandPsi` three times gives `v = v`.
6. **Upper numbering** (`upperRestrictionCompatibility_aux`). This is the argument of
   `QuotientProof`'s `upperQuotientCompatibility`. At `v = -1` both sides are the whole
   group because the restriction is surjective. For `v > -1`, pass to a common
   nonnegative rational index `w` with `exists_rat_upperRamificationGroup_eq`. Express both
   upper groups as Library lower groups with the source indices
   (`upperRamificationGroup_ratCast`). Then apply the ported upper-numbering theorem and
   step 3. `upperRestrictionCompatibility` supplies the derived p-adic tower instance.
