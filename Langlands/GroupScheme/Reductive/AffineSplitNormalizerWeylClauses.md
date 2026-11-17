# Normalizer points of a split torus: the relation `Induces` and clauses 2 and 3

Worker 4348 (Task 6589).

This module works in the namespace `Langlands.GroupScheme.AffineSplitNormalizerWeyl`. It
defines the relation `Induces` between a point of `G(S)` and an automorphism of a root
datum. It proves two of the four clauses of
[`Reductive.AffineSplitNormalizerWeylStatement`](AffineSplitNormalizerWeylStatement.md)
(Conrad, *Reductive group schemes*, Example 6.4.3):

- **clause 3**, `exists_eq_of_mem_centralizerPoints`: a point of `G(S)` that centralizes
  a fibrewise maximal closed split torus is a point of the torus;
- **clause 2**, `exists_weylGroup_of_mem_normalizerPoints`: over a ring `R` whose
  spectrum is connected, a point of `G(R)` that normalizes the split maximal torus induces
  an element of the Weyl group `P.weylGroup`.

It does not prove clauses 1 and 4 of the statement, and it does not prove the statement
itself. It adds no axioms.

## Provenance

The definition and the theorems are internal to the Library. They exist to prove the
published statement `AffineSplitNormalizerWeylStatement`. `Induces` is a copy, over an
arbitrary base scheme, of the relation that this statement introduces by a local `let`.
The two theorems are clauses 2 and 3 of the statement. Their source is Conrad, Example 6.4.3,
pp.230–231 (registered as `conrad-2014-reductive-group-schemes`; the statement's
Markdown quotes the passage). The proofs below do not follow Conrad's route through the
group schemes `N_G(T)` and `W_G(T) = W(Φ)_S`. They combine results that are already in the
Library.

## Definition

### `Induces`

```
def Induces {S : Scheme.{u}} {G : GroupScheme S} {I : Type u} [Fintype I]
    (i : splitTorus S I ⟶ G) {J : Type*} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (n : Over.mk (𝟙 S) ⟶ G.X) (w : RootPairing.Aut P) : Prop
```

`Induces i n w` holds when there is an automorphism
`σ : splitTorus.commGroupScheme S I ≅ splitTorus.commGroupScheme S I` of the split torus
`𝔾_m^I` such that

- `IsNormalizingPoint i n σ` ([`Torus.Maximal`](../Torus/Maximal.md)): conjugation by
  `n` restricts along `i` to `σ`, that is `i ≫ (G.innerIso n).hom = groupHom σ.hom ≫ i`;
- for every `U : Over S`, every point `x : U ⟶ 𝔾_m^I` and every `m : I → ℤ`,
  `∏ j, (pointsEquiv I U (x ≫ σ_*))_j ^ m j = ∏ j, (pointsEquiv I U x)_j ^ (w • m) j`,
  where `x ≫ σ_*` is `x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom`. So
  `χ_m ∘ σ = χ_{w • m}` on all points: `σ` acts on the character lattice `ℤ^I` by `w`.

For `S = Spec R` and `J : Type u`, the term `Induces i n w` unfolds to the body of the
local `let Induces` of `AffineSplitNormalizerWeylStatement`, applied to `n` and `w`. The
two are equal by unfolding definitions (`Iff.rfl`). The statement's Markdown explains the
meaning and the direction convention of the relation.

## Theorems

### `exists_eq_of_mem_centralizerPoints` (clause 3)

Hypotheses: any base scheme `S`, `hG : IsReductive G`, a finite type `I`, a homomorphism
`i : splitTorus S I ⟶ G` with `IsClosedSubgroup i` and
`IsFibrewiseMaximalTorus i`, and `n ∈ centralizerPoints i`.
Conclusion: `∃ t : Over.mk (𝟙 S) ⟶ (splitTorus S I).X, n = t ≫ i.hom.hom`.

Proof. The Library theorem `splitTorusCentralizer_eq_range_of_fibrewiseMaximal`
([`Torus.MaximalSelfCentralizingDescent`](../Torus/MaximalSelfCentralizingDescent.md))
says that the centralizer subgroup functor `torusCentralizer i` equals the range of `i`
when `i` is a split torus that is maximal on every fibre (the split hypothesis is
`isSplitTorus_splitTorus` from [`Torus.Split`](../Torus/Split.md)). By
`mem_torusCentralizer_base_iff`
([`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)) the point `n` of
`centralizerPoints i` lies in the base-point carrier of `torusCentralizer i`. So it lies
in the range of `i`, and `SubgroupFunctor.mem_range` gives the point `t`.

### Auxiliary lemmas for clause 2

- `zpow_finsetSum`: in a commutative group, `a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i`
  (induction on `s`).
- `prod_powUnits_zpow`: for an integer matrix `M`, units `y : I → Aˣ` and `m : I → ℤ`,
  `∏ j, (powUnits M y)_j ^ m j = ∏ j, y j ^ (vecMul m M) j`. Here `splitTorus.powUnits M y`
  is the monomial map `j ↦ ∏ l, y l ^ M j l`. So the character `χ_m` composed with the
  monomial map of `M` is `χ_{m M}`. The proof expands the products, swaps them, and
  applies `zpow_finsetSum`.
- `exists_matrix_of_isNormalizingPoint`: over a connected base `S`, if
  `IsNormalizingPoint i n σ` and `i` is a monomorphism, then one integer matrix `M`
  satisfies `pointsEquiv I U (x ≫ σ_*) = powUnits M (pointsEquiv I U x)` for every `U`
  and `x`. The proof uses the rigidity theorem
  `TorusConjugation.exists_actsBy_of_connected`
  ([`Rational.TorusNormalizerRigidity`](../Rational/TorusNormalizerRigidity.md)), which says
  that over a connected test scheme conjugation by a torus-normalizing point acts by one
  exponent matrix. It applies to `n` because `normalizerPoints_le_torusNormalizer`
  ([`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)) puts `n` in the
  normalizer functor. The rigidity is stated for `TorusConjugation.conjUnits`. It is
  turned into a statement about `σ` with `conjUnits_spec`, `comp_eq_constantPoint` and
  `IsNormalizingPoint.conj_comp`, and then cancelling the monomorphism `i`.
- `comp_exponentCharacter_of_powUnits`: if an endomorphism `f` of the split torus acts on
  points by the monomial map of `M`, then
  `f ≫ exponentCharacter S I m = exponentCharacter S I (vecMul m M)`. This is checked on
  points (`CommGroupScheme.hom_ext_points`, `splitTorus.pointsEquiv_exponentCharacter`) with
  `prod_powUnits_zpow`.
- `exists_weylGroup_vecMul`: let `R` be a ring, `k` a field with an `R`-algebra
  structure, `G` reductive over `Spec R`, `i` fibrewise maximal, and `P` a fibrewise root
  datum of `(G, i)`. If `IsNormalizingPoint i n σ` and `σ` acts on points by the monomial
  map of `M`, then some `w ∈ P.weylGroup` satisfies `w • m = vecMul m M` for every `m`.

  Proof. The fibre over `k` is used:
  1. `IsNormalizingPoint.inv` and `IsNormalizingPoint.baseChangeBasePoint`
     ([`Rational.NormalizerGaloisAction`](../Rational/NormalizerGaloisAction.md)) show
     that the base change of `n⁻¹` normalizes the base-changed torus through the base
     change of `σ.symm`. `IsNormalizingPoint.transport`
     ([`Rational.CrossTorusWeylTransport`](../Rational/CrossTorusWeylTransport.md)) moves
     this to the coordinate split torus `𝔾_m^I` over `k`. The comparison isomorphism is
     `splitTorus.commBaseChangeIso`, and the morphism to `G_k` is
     `splitTorus.baseChangeHom`.
  2. `AlgebraicFundamentalGroup.IsNormalizingPoint.exists_weylGroup`
     ([`AlgebraicFundamentalGroupWeyl`](../AlgebraicFundamentalGroupWeyl.md)) applies on
     the fibre. Its inputs are `isConnectedReductive_baseChange`
     ([`Reductive.BaseChange`](BaseChange.md)),
     `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`
     ([`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md)) and
     `IsFibrewiseRootDatumOf.field` ([`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md)).
     It gives `w'` in the Weyl group of the field realization of `P` over `k` with
     `w'.weightEquiv χ = τ.inv ≫ χ`, where `τ` is the transported automorphism. Its
     inverse is the base change of `σ`.
  3. Base change commutes with exponent characters
     (`splitTorus.exponentCharacter_baseChange`, `characterLattice.baseChange_apply`).
     So `comp_exponentCharacter_of_powUnits` over `R` gives
     `τ.inv ≫ χ_m = χ_{vecMul m M}` over `k`.
  4. The equivalence `CoordinateRootDatum.fieldRealizationEquiv k P` between `P` and its
     field realization sends `m` to `exponentCharacter k I m`
     (`fieldRealizationEquiv_weightMap`). Conjugating by it with `rootDatumWeylGroupEquiv`
     ([`Torus.WeylGroupSchemeFibreCardinality`](../Torus/WeylGroupSchemeFibreCardinality.md))
     transports `w'` to an element `w` of `P.weylGroup`. Steps 2 and 3 then give
     `w • m = vecMul m M`.

### `exists_weylGroup_of_mem_normalizerPoints` (clause 2)

Hypotheses: a ring `R` with `ConnectedSpace (Spec R)`, `hG : IsReductive G`, a finite type
`I` and `i : splitTorus (Spec R) I ⟶ G`, a root datum `P : RootDatum J (I → ℤ) (I → ℤ)`
with `J : Type u`, `IsClosedSubgroup i`, `IsFibrewiseMaximalTorus i`,
`IsFibrewiseRootDatumOf I G i P`, and `n ∈ normalizerPoints i`.
Conclusion: `∃ w ∈ P.weylGroup, Induces i n w`.

The free-root-space hypothesis of the statement is not needed.

Proof. `mem_normalizerPoints` gives `σ` with `IsNormalizingPoint i n σ`. `i` is a closed
immersion, hence a monomorphism, and `Spec R` is connected. So
`exists_matrix_of_isNormalizingPoint` gives a matrix `M` describing `σ` on points. `R` is
non-zero because its spectrum is non-empty. Take a maximal ideal `𝔪` and apply
`exists_weylGroup_vecMul` with `k = R ⧸ 𝔪` to get `w ∈ P.weylGroup` with
`w • m = vecMul m M`. The same `σ` witnesses `Induces i n w`: by the matrix description of
`σ` and `prod_powUnits_zpow`, both sides of the character identity equal
`∏ j, (pointsEquiv I U x)_j ^ (vecMul m M) j`.

## Lean notes

The module sets `backward.isDefEq.respectTransparency false` (and its `.types` variant) as
several Library modules on split tori do. In `exists_weylGroup_vecMul`, the objects of
`IsNormalizingPoint.transport` are given explicitly, because leaving them to unification
times out.
