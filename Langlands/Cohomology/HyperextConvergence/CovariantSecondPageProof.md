# The covariant hyperext spectral sequence: second page and abutment (proof)

Author: Worker 23 (Task 5469). The module proves the Library proposition
`Langlands.Cohomology.HyperextConvergence.CovariantSecondPageStatement`
(module `Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement`) by the
theorem

```lean
theorem covariantSecondPageStatement_proof (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] : CovariantSecondPageStatement.{w, w', v, u} C
```

in namespace `Langlands.Cohomology.HyperextConvergence`. Its binders are those
of the proposition definition, in the same order, with the same four
independent universes `w`, `w'`, `v`, `u`; the instance `HasExt.{w'} C`, the
object `K` of the derived category, the object `A` of `C` and all degrees are
quantified inside the proposition and are kept. No hypothesis is added.

It builds on Worker 61's Library modules
`Langlands.Cohomology.HyperextSpectralSequence` (`opTStructure`,
`heartPiece`, `hyperextSpectralSequence`, `secondPageIso`) and
`Langlands.Cohomology.HyperextSecondPage` (the generic truncation triangles
`upperTriangle` and `heartTriangle`, `isoSingleHomology`, and the additive
equivalences `precompAddEquiv`, `postcompAddEquiv`, `shiftAddEquiv`), and on
Mathlib's opposite pretriangulated structure, derived categories and
`Abelian.Ext`. The route is the one of Step 5 of "Why the statements are true"
in the statement Markdown; the Lean proof makes the identification of the
heart piece precise by dualizing Worker 61's `heartPieceIso`.

## Setting and notation

`C` is an abelian category (objects in `Type u`, morphisms in `Type v`) with
`HasDerivedCategory.{w} C`; write `D = DerivedCategory C`, whose morphisms lie
in `Type w`. `t = DerivedCategory.TStructure.t` is the standard t-structure,
`H^n = DerivedCategory.homologyFunctor C n`, and `(singleFunctor C n).obj M`
is `M` placed in degree `n`. Write `A₀ = (singleFunctor C 0).obj A`.

`Dᵒᵖ` carries Mathlib's pretriangulated (and triangulated) structure from
`CategoryTheory.Pretriangulated.Opposite`: the shift by `n` on `Dᵒᵖ` is the
opposite of the shift by `-n` on `D` (`shiftFunctorOpIso`), and a triangle of
`Dᵒᵖ` is distinguished when its image under the inverse of
`triangleOpEquivalence` is a distinguished triangle of `D`; that image of
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is `Z.unop ⟶ Y.unop ⟶ X.unop ⟶ Z.unop⟦1⟧` (Mathlib's
`unop_distinguished`).

`tOp` (an `abbrev`) is `opTStructure t`, a t-structure on `Dᵒᵖ`: `X` lies in
degrees `≤ n` for `tOp` iff `X.unop` lies in degrees `≥ -n` for `t`, and in
degrees `≥ n` iff `X.unop` lies in degrees `≤ -n`. The spectral sequence of the
statement is `hyperextSpectralSequence tOp (op K) (op A₀)`.

## The heart piece

| Declaration | Content |
| --- | --- |
| `unopAddEquiv X Y` | For a preadditive category and `X Y : Cᵒᵖ`, the additive equivalence `(X ⟶ Y) ≃+ (Y.unop ⟶ X.unop)`, `f ↦ f.unop`. |
| `coheartPiece K q` (abbrev) | `(heartPiece tOp (op K) q).unop`, an object of `D`; classically `τ_{≥ q} τ_{≤ q} K`. |
| `coheartPiece_isGE`, `coheartPiece_isLE` (instances) | `coheartPiece K q` lies in degrees `≥ q` and `≤ q`: Worker 61's instances `heartPiece_isLE` and `heartPiece_isGE` say that `heartPiece tOp (op K) q` lies in degrees `≤ -q` and `≥ -q` for `tOp` (the latter needs `Dᵒᵖ` triangulated, Mathlib's scoped instance), and `opTStructure_isLE_iff`, `opTStructure_isGE_iff` translate to `t`. |
| `coupperTriangle K q` | The image in `D` of `upperTriangle tOp (op K) q` under the inverse of `triangleOpEquivalence`: a triangle `(upperPiece tOp (op K) q).unop ⟶ K ⟶ Z ⟶ …` whose first morphism is `(toUpperPiece tOp (op K) q).unop` (`coupperTriangle_mor₁`, by definition). Distinguished (`coupperTriangle_distinguished`, by `unop_distinguished` and `upperTriangle_distinguished`). Its third object `Z` is the first object of `upperTriangle`, which lies in degrees `≤ -(q + 1)` for `tOp`; so `Z` lies in degrees `≥ q + 1` (instance `coupperTriangle_obj₃_isGE`). Classically `τ_{≤ q} K ⟶ K ⟶ τ_{≥ q+1} K ⟶`. |
| `coheartTriangle K q` | The image in `D` of `heartTriangle tOp (op K) q`: a triangle `Z ⟶ (upperPiece tOp (op K) q).unop ⟶ coheartPiece K q ⟶ …` whose second morphism is `(heartPieceToUpperPiece tOp (op K) q).unop` (`coheartTriangle_mor₂`, by definition). Distinguished (`coheartTriangle_distinguished`). Its first object `Z` is the third object of `heartTriangle`, which lies in degrees `≥ -(q - 1)` for `tOp`; so `Z` lies in degrees `≤ q - 1` (instance `coheartTriangle_obj₁_isLE`). Classically `τ_{≤ q-1} K ⟶ τ_{≤ q} K ⟶ τ_{≥ q} τ_{≤ q} K ⟶`. |
| `isIso_homologyMap_coupperTriangle_mor₁` (instance) | `H^q` of the first morphism of `coupperTriangle K q` is an isomorphism. The third object lies in degrees `≥ q + 1`, so its `H^{q-1}` and `H^q` vanish (`isZero_of_isGE`). In the long exact cohomology sequence of the triangle, the connecting map `H^{q-1}(Z) ⟶ H^q(first object)` is then zero, giving a monomorphism (Mathlib's `homologySequence_mono_shift_map_mor₁_iff`), and `H^q` of the second morphism lands in zero, giving an epimorphism (`homologySequence_epi_shift_map_mor₁_iff`). |
| `isIso_homologyMap_coheartTriangle_mor₂` (instance) | `H^q` of the second morphism of `coheartTriangle K q` is an isomorphism. The first object lies in degrees `≤ q - 1`, so its `H^q` and `H^{q+1}` vanish (`isZero_of_isLE`); this gives a monomorphism (`homologySequence_mono_shift_map_mor₂_iff`) and an epimorphism (`homologySequence_epi_shift_map_mor₂_iff`, the connecting map lands in `H^{q+1}` of the first object). |
| `coheartPieceHomologyIso K q` | `H^q(coheartPiece K q) ≅ H^q(K)`: the inverse of the isomorphism induced by the second morphism of `coheartTriangle K q`, followed by the isomorphism induced by the first morphism of `coupperTriangle K q` (both pass through `H^q` of `(upperPiece tOp (op K) q).unop`). |
| `coheartPieceIso K q` | `coheartPiece K q ≅ (singleFunctor C q).obj (H^q K)`: Worker 61's `isoSingleHomology` (an object in degrees `≥ q` and `≤ q` is its `H^q` placed in degree `q`) followed by `singleFunctor C q` applied to `coheartPieceHomologyIso K q`. |

## Second page, vanishing and abutment

`secondPageAddEquiv K A p q`, for `[HasExt.{w'} C]`, `p : ℕ` and `q : ℤ`, is an
additive equivalence

`(heartPiece tOp (op K) q ⟶ (op A₀)⟦p + q⟧) ≃+ Abelian.Ext.{w'} A (H^q K) p`.

With `M = H^q K` and `M₀ = (singleFunctor C 0).obj M`, it is the composite of:

1. postcomposition with `(shiftFunctorOpIso D (p + q) (-(p + q)) _).app (op A₀)`,
   identifying `(op A₀)⟦p + q⟧` with `op (A₀⟦-(p + q)⟧)`;
2. `unopAddEquiv`, giving `A₀⟦-(p + q)⟧ ⟶ coheartPiece K q` in `D`;
3. postcomposition with `coheartPieceIso K q`, giving
   `A₀⟦-(p + q)⟧ ⟶ (singleFunctor C q).obj M`;
4. postcomposition with the inverse of
   `((singleFunctors C).shiftIso (-q) q 0 _).app M : M₀⟦-q⟧ ≅ (singleFunctor C q).obj M`;
5. `shiftAddEquiv` by `p + q`, giving `A₀⟦-(p + q)⟧⟦p + q⟧ ⟶ M₀⟦-q⟧⟦p + q⟧`;
6. precomposition with the inverse of
   `(shiftFunctorCompIsoId D (-(p + q)) (p + q) _).app A₀`, giving `A₀ ⟶ M₀⟦-q⟧⟦p + q⟧`;
7. postcomposition with the inverse of
   `(shiftFunctorAdd' D (-q) (p + q) p _).app M₀`, giving
   `A₀ ⟶ M₀⟦p⟧ = ShiftedHom A₀ M₀ p`;
8. the inverse of Mathlib's `Abelian.Ext.homAddEquiv`.

`abutmentAddEquiv K A n : (op K ⟶ (op A₀)⟦n⟧) ≃+ ShiftedHom A₀ K n` is the
composite of postcomposition with `(shiftFunctorOpIso D n (-n) _).app (op A₀)`,
`unopAddEquiv` (giving `A₀⟦-n⟧ ⟶ K`), `shiftAddEquiv` by `n` (giving
`A₀⟦-n⟧⟦n⟧ ⟶ K⟦n⟧`), and precomposition with the inverse of
`(shiftFunctorCompIsoId D (-n) n _).app A₀`.

`isZero_secondPage_of_neg K A p q (hp : p < 0)`: the page-2 object in position
`(p, q)` is zero. By `secondPageIso` it is the group
`heartPiece tOp (op K) q ⟶ (op A₀)⟦p + q⟧`. Here `heartPiece tOp (op K) q` lies
in degrees `≤ -q` for `tOp` (`heartPiece_isLE`); `A₀` lies in degrees `≤ 0`
for `t` (Mathlib's instance), so `op A₀` lies in degrees `≥ 0` for `tOp` and
`(op A₀)⟦p + q⟧` in degrees `≥ -(p + q)` (`isGE_shift`). Since
`-q < -(p + q)`, every morphism between them is zero
(`zero_of_isLE_of_isGE`), so the group is a subsingleton and hence a zero
object of `AddCommGrpCat` (`AddCommGrpCat.isZero_of_iff_subsingleton`).

## The theorem

`covariantSecondPageStatement_proof` introduces the `HasExt.{w'} C` instance,
`K` and `A`, and proves the three conjuncts:

1. for `p : ℕ` and `q : ℤ`, `secondPageIso tOp (op K) (op A₀) p q`, converted
   to an additive equivalence by `Iso.addCommGroupIsoToAddEquiv`, followed by
   `secondPageAddEquiv K A p q`;
2. for `p < 0`, `isZero_secondPage_of_neg`;
3. for `n : ℤ`, `abutmentAddEquiv K A n`.

## Scope

The module identifies page 2 and the abutment groups only. It does not prove
convergence (the `HyperextHalfBounded…` propositions of the same statement
module) or any compatibility of these identifications with differentials or
with the abutment filtration; the statement asserts none. The equivalences
are built from choices (`isoSingleHomology` uses a chosen isomorphism, and the
truncations of `tOp` are chosen by Mathlib); the statement asks only for the
existence (`Nonempty`) of the additive equivalences. Axioms used:
`propext`, `Classical.choice`, `Quot.sound`.
