# The finite norm and transfer diagrams at field universes zero: proof

The module `Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroNormTransferProof`
proves the published proposition
`Langlands.LocalClassField.UniverseZero.FiniteAbelianNormTransferTypeZeroStatement` with
the theorem

```lean
theorem Langlands.LocalClassField.UniverseZero.finiteAbelianNormTransferTypeZero :
    FiniteAbelianNormTransferTypeZeroStatement
```

Its type is exactly the target. The target is the transparent alias of the Library
proposition `Langlands.LocalClassField.FiniteAbelianNormTransfer.{0, 0, 0}` in
[`TypeZeroStatement`](TypeZeroStatement.lean). The module also proves the
auxiliary theorem `abelianization_of_injective_of_isMulCommutative`.

It imports the target module, the supporting module
[`FiniteGeometricQuotient`](../FiniteGeometricQuotient.lean), and the published
modules [`FiniteArtinNorm`](../FiniteArtinNorm.lean),
[`FiniteAbelianizedArtin`](../FiniteAbelianizedArtin.lean) and
[`NormTransferReductionProof`](NormTransferReductionProof.lean). It changes none
of them and imports no module under `Langlands/NYLL/`.

## What is proved

**Auxiliary theorem.** For a group `G` whose multiplication is commutative
(`[IsMulCommutative G]`), `Abelianization.of : G →* Abelianization G` is
injective. With the commutative group structure from `IsMulCommutative`,
`Abelianization.lift (MonoidHom.id G)` is a left inverse of `Abelianization.of`
by `Abelianization.lift_apply_of`. So equal images have equal preimages.

**Main theorem.** Fix a prime `p`, fields `F E L : PadicField.{0} p` in a tower
`F ⊆ E ⊆ L`, the algebra, scalar-tower and finite-dimension instances of the Library
proposition, the hypothesis `IsAbelianGalois F.Carrier L.Carrier`, and arbitrary
supplied `TF : F.TopologicalData` and `TE : E.TopologicalData`. Give `F.Carrier`
and `E.Carrier` the topologies `TF.topology` and `TE.topology`. Write `[·]` for
`QuotientGroup.mk` and `N` for `Units.map (Algebra.norm F.Carrier (S := E.Carrier))`.
Then there are continuous multiplicative equivalences `rF` and `rE` from the norm
quotients for `L/F` and `L/E` to `Gal(L/F)` and `Gal(L/E)` such that:

- **norm clause:** `rF [N a] = (rE [a]).restrictScalars F.Carrier` for every
  `a : E.Carrierˣ`;
- **transfer clause:** for every `a : F.Carrierˣ`, with `a_E` its image under
  `Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom`,
  `(rE [a_E]).restrictScalars F.Carrier = rF [a] ^ Module.finrank F.Carrier E.Carrier`.

## Proof

1. **Instances.** The proof installs `TF.topology` and `TE.topology`. It derives
   `IsAbelianGalois E.Carrier L.Carrier` by `IsAbelianGalois.tower_top`. So
   `Gal(L/F)` and `Gal(L/E)` both have commutative multiplication.
2. **The witnesses.** The Library theorems
   `continuous_geometricArtin F TF L L.canonicalTopologicalData` and
   `continuous_geometricArtin E TE L L.canonicalTopologicalData` give continuity
   of `geometricSymbol F L.Carrier` for `TF.topology` and of
   `geometricSymbol E L.Carrier` for `TE.topology`. The canonical data of `L` are
   used only to obtain these continuity proofs. The supporting theorem
   `exists_quotientEquiv_geometricSymbol` then gives `rF` and `rE`, with
   `rF [b] = geometricSymbol F L.Carrier b` and
   `rE [a] = geometricSymbol E L.Carrier a`.
3. **Norm clause.** Fix `a : E.Carrierˣ`. By step 2 and `geometricSymbol_apply`,
   the goal becomes
   `artinSymbol F L (N a)⁻¹ = (artinSymbol E L a⁻¹).restrictScalars F.Carrier`,
   where `artinSymbol` is the Library's arithmetic finite Artin symbol.
   - The Library theorem `abelianizedArtinSymbol_norm F E L.Carrier a⁻¹` (module
     `FiniteArtinNorm`; it is the pointwise form of `artinNormCompatibility`)
     says that `Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier)` sends
     `abelianizedArtinSymbol E L a⁻¹` to
     `abelianizedArtinSymbol F L (normUnits F.Carrier E.Carrier a⁻¹)`.
   - Both Galois groups are commutative by step 1. So the Library theorem
     `abelianizedArtinSymbol_eq_of_comm` (module `FiniteAbelianizedArtin`)
     rewrites each abelianized symbol as `Abelianization.of` of the arithmetic
     symbol. `Abelianization.map_of` moves the map inside `Abelianization.of`.
   - The auxiliary theorem, for `G = Gal(L/F)`, removes `Abelianization.of`:
     `(artinSymbol E L a⁻¹).restrictScalars F.Carrier =
     artinSymbol F L (normUnits F.Carrier E.Carrier a⁻¹)`.
   - `normUnits F.Carrier E.Carrier` is `N` by definition, and `N` commutes with
     inverses (`map_inv`). So `N a⁻¹ = (N a)⁻¹`, and the equation is the goal
     read from right to left.
4. **Transfer clause.** The published `normCompatibleTransfer p F E L TF TE rF rE`
   turns the norm clause of every pair of quotient equivalences into its
   transfer clause.

The theorem returns `⟨rF, rE, step 3, step 4⟩`.

## Scope and provenance

Both witnesses are quotients of the Library's geometric finite Artin symbols over
`F` and over `E`. The proof adds no hypothesis to the target. The mathematical
source of the target is Serre, *Local Fields*, XIII.4, Proposition 10(a)–(b)
(source `serre-1979-local-fields`), with the abelian transfer formula and the
geometric convention explained in
[`FiniteReciprocityStatement.md`](../FiniteReciprocityStatement.md). The proof
assembles published Library theorems, starting from the Library's own finite
Artin symbol.
The auxiliary theorem is an elementary group-theory fact proved here
for this use.

The module compiled without errors or warnings with Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
