# Relative conjugacy from the inflation and restriction laws

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.InvariantRelativeConjugacyStatement`
(module `Langlands.ClassFieldTheory.Local.InvariantTransferConsequencesStatement`).
The exact-target theorem is

```
theorem invariantRelativeConjugacy :
    InvariantRelativeConjugacyStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every prime `p` and every raw invariant family `I : InvariantFamily.{u,u} p`,
if `I.InflationCompatibility` and `I.RelativeRestriction` hold, then
`I.RelativeConjugacy` holds. The conjugacy map is the Library's actual
`relativeConjugacy`, induced by a `Padic p`-algebra equivalence of the bases
and a compatible ring equivalence of the extensions.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`),
Chapter XI, §2, Proposition 1 (iii) (statement on printed page 167, proof on
printed page 168; PDF pages 173–174). Serre writes `x = Res(x₀)` with `x₀`
over the base field of the formation. He then uses that restriction commutes
with `s*` and that `s*` is the identity over the base field.

The Lean proof takes a different route. It does not pass through a common
base field. It views the target extension `M` over the source base `F`
through the base equivalence. Conjugacy then becomes conjugacy over the same
base `F`, followed by restriction along the degree-one extension `E/F`. The
same-base case is the Library theorem
`relative_relativeConjugacy_refl_of_inflationCompatibility` (module
`Langlands.ClassFieldTheory.Local.SameBaseConjugacy`), which follows from
inflation compatibility.

## The implemented proof

The module contains two auxiliary theorems and the exact-target theorem.

1. `relativeConjugacy_hom_eq_comp_relativeRestriction eK eL h h' n`: let
   `K, K', L, M` be fields in universe `u` with algebras `K → L`, `K' → M`,
   `K → K'`, `K → M` and `IsScalarTower K K' M`. Let `eK : K ≃+* K'` and
   `eL : L ≃+* M`, and let `h` and `h'` say that `eL` is compatible with `eK`
   and with `RingEquiv.refl K` respectively. Then in every degree `n`

   ```
   (relativeConjugacy eK eL h n).hom =
     (relativeConjugacy (RingEquiv.refl K) eL h' n).hom ≫
       relativeRestriction K K' M n
   ```

   `relativeConjugacy` is `groupCohomology.mapIso` of the Galois-group
   conjugacy and the unit-group map `unitsConjugacy eL`, and
   `relativeRestriction` is `groupCohomology.map` of
   `AlgEquiv.restrictScalarsHom K` and the coefficient inclusion. After
   `unfold relativeConjugacy groupCohomology.mapIso`,
   `← groupCohomology.map_comp` combines the right side into one
   `groupCohomology.map`. `groupCohomology.map_congr` then leaves two goals.
   The group homomorphisms `Gal(M/K') → Gal(L/K)` agree on every automorphism
   and element (`ext σ x; rfl`). The coefficient maps agree by `rfl`.

2. `InvariantFamily.relativeConjugacy_of_inflationCompatibility I hInf hRes`:
   `I.RelativeConjugacy`. Take p-adic fields `F`, `E`, finite Galois
   extensions `L/F` and `M/E`, `eF : F ≃ₐ[Padic p] E`, `eL : L ≃+* M`
   compatible with `eF`, and `x : relativeCohomology F L 2`. The proof
   introduces local data:
   - `Algebra F E` given by `eF`, and `Algebra F M` given by
     `algebraMap E M ∘ eF`. Then `IsScalarTower F E M` holds by `rfl`, and
     `IsScalarTower (Padic p) F E` follows from `eF.commutes`.
   - `Algebra.linearMap F E` is `eF`, hence bijective. So `E` is
     finite-dimensional over `F` (`Module.Finite.of_surjective`), and `M` is
     finite-dimensional over `F` (`Module.Finite.trans`).
     `Module.finrank F E = 1` follows from `LinearEquiv.ofBijective` and
     `Module.finrank_self`.
   - `IsGalois F M` follows from `IsGalois E M` by
     `IsGalois.of_equiv_equiv`, with `eF.symm` on the bases and the identity
     on `M`. The compatibility square is closed with `eF.apply_symm_apply`.
   - `e : L ≃ₐ[F] M` is `eL` with `commutes' := h`. For the new algebra
     `F → M`, `h` is also the compatibility `h'` of `e` with
     `RingEquiv.refl F`.

   Item 1 with `K = F`, `K' = E` rewrites the conjugacy as same-base
   conjugacy followed by `relativeRestriction F E M 2`. `RelativeRestriction`
   for the tower `F ⊆ E ⊆ M` multiplies the invariant by
   `Module.finrank F E = 1`, and `one_nsmul` removes the factor. The Library
   theorem `relative_relativeConjugacy_refl_of_inflationCompatibility`
   applied to `hInf`, `F`, `e` and `h'` closes the goal.

The exact-target theorem introduces `p`, `I` and the two hypotheses and
applies item 2.

## Notes

- Item 1 holds in every degree and for arbitrary fields. It is exported for
  reuse.
- `RelativeImages` and the `H¹` clause of `RelativeClassFormation` are not
  used.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
