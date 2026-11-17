# Finite Galois character exactness for groups of multiplicative type: proof

Worker 159.

The theorem `Langlands.GroupScheme.multiplicativeTypeGaloisExactness` proves
the proposition `Langlands.GroupScheme.MultiplicativeTypeGaloisExactnessStatement.{u}`
(module `Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessStatement`)
for every universe `u`. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`. The auxiliary declarations are in the namespace
`Langlands.GroupScheme.MultiplicativeTypeGaloisExactness`, and none of them is
private.

## The statement

Let `L/k` be a finite Galois extension. Let `N`, `E`, `Q` be commutative group
schemes over `Spec k` with isomorphisms `e_N : N_L ≅ D_L(M_N)`,
`e_E : E_L ≅ D_L(M_E)` and `e_Q : Q_L ≅ D_L(M_Q)`, where the `M_X` are finitely
generated abelian groups (torsion allowed). Let `i : N → E` and `q : E → Q`. The
statement says the following two conditions are equivalent:

- `i` is a closed immersion (`IsClosedSubgroup`) and
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` holds. This means
  that `q` is flat, surjective and locally of finite presentation, and that the
  range of the actual kernel inclusion of `q` equals the range of `i` on every
  test scheme.
- The character pullbacks `pullQ = (q_L ≫ ·)` and `pullN = (i_L ≫ ·)` commute
  with the canonical Galois actions `characterLattice.galoisRepresentation`,
  `pullQ` is injective, the pair `(pullQ, pullN)` is exact, and `pullN` is
  surjective.

The statement's Markdown gives the source: Milne, *Algebraic Groups* (2017),
Theorems 12.9(b) and 12.23 (`milne-2017-algebraic-groups`). Over `L`, the
models reduce the statement to Theorem 12.9(b), which identifies short exact
sequences of diagonalizable groups with reversed short exact sequences of
their character groups. The Lean proof follows the same reduction. It descends
along the fpqc map `Spec L → Spec k`, transports along the models, and proves
the split case directly with points.

## The proof of the main theorem

Write `p = algebraBaseMap k L`.

1. `fieldExtension_fpqc k L` (module `Langlands.GroupScheme.BaseChangeReflection`)
   makes `p` surjective, flat and quasi-compact.
2. Every homomorphism `D_L(A) → D_L(B)` is `Diagonalizable.restrictMap L f` for
   a unique `f : B →+ A`
   (`DiagonalizableCharacter.restrictMap_bijective`, module
   `Langlands.GroupScheme.Torus.DiagonalizableCharacterProof`; no finite
   generation is needed). This gives `f : M_E →+ M_N` with
   `restrictMap f = e_N⁻¹ ≫ i_L ≫ e_E`, and `g : M_Q →+ M_E` with
   `restrictMap g = e_E⁻¹ ≫ q_L ≫ e_Q`.
3. The left side of the statement is equivalent to the conditions
   `Injective g ∧ Exact g f ∧ Surjective f`. This is the chain
   `descent_iff` (the conditions for `i`, `q` over `k` are equivalent to those
   for `i_L`, `q_L`), then `transport_iff` (equivalent to those for
   `restrictMap f`, `restrictMap g`), then `splitCore L f g`. Here `grpIso`
   turns the given isomorphisms of commutative group schemes into isomorphisms
   of the underlying group schemes.
4. Let `Φ_X : M_X ≃+ X(X_L)` be `DiagonalizableCharacter.evalCharacterEquiv L M_X`
   followed by the inverse of `characterLattice.congr e_X`, so that
   `Φ_X m = e_X.hom ≫ evalCharacter m`. Rewriting with
   `restrictHom_comp_evalCharacter` and step 2 gives the ladder identities
   `pullN (Φ_E m) = Φ_N (f m)` and `pullQ (Φ_Q m) = Φ_E (g m)`.
5. The ladder transfers the three exactness conditions.
   `Function.Exact.iff_of_ladder_addEquiv` gives `Exact pullQ pullN ↔ Exact g f`.
   This is the additive version of Mathlib's `Function.MulExact.iff_of_ladder_mulEquiv`,
   applied with `pullQ`, `pullN` packaged as `Preadditive.leftComp`.
   `EquivLike.injective_comp` and `EquivLike.comp_injective` give
   `Injective pullQ ↔ Injective g`. The surjective versions give
   `Surjective pullN ↔ Surjective f`.
6. Both equivariance conditions hold unconditionally. Each is the symmetric
   form of `characterLattice.galoisRepresentation_naturality`
   (module `Langlands.GroupScheme.Torus.GaloisCharacterFunctor`), applied to
   `q` and to `i`. Combining steps 3, 5 and 6 proves the equivalence.

## Auxiliary declarations

### Character-level algebra

The variables are `f : B →+ A` and `g : C →+ B`.

- `PointCriterion f g M`, for a commutative group `M`, holds when every
  homomorphism `χ : Multiplicative B →* M` satisfies the following: `χ` kills
  the image of `g` exactly when `χ` factors as `ψ ∘ f`.
- `pointCriterion_of_exact`: if `f` is surjective and `Exact g f`, the
  criterion holds for every `M`. The factorization is built with a section of
  `f`; it is well defined because `ker f = im g`.
- `exact_of_pointCriterion`: assume injective homomorphisms
  `u₁ : Multiplicative A →* M₁` and `u₂ : Multiplicative (B ⧸ g.range) →* M₂`,
  and the criterion for `M₁` and for `M₂`. Then `Exact g f`. The criterion at
  `u₂ ∘ (B → B ⧸ g.range)` gives `ker f ⊆ im g`. The criterion at `u₁ ∘ f`
  gives `f ∘ g = 0`.

### Group algebras

- `mapDomainRingHom_surjective_iff`: `K[B] → K[A]` along `f` is surjective iff
  `f` is. To show necessity, compare coefficients at an element `a` outside
  the range of `f` (`Finsupp.mapDomain_of_notMem_range`).
- `injective_of_mapDomainRingHom`: if `K[C] → K[B]` along `g` is injective,
  then `g` is injective (apply it to the basis elements `single c 1`).
- `mapDomainRingHom_finitePresentation`: for finitely generated `A` and `B`,
  the map is of finite presentation. Its composite with `K → K[B]` is
  `K → K[A]`, which is of finite presentation because `K[A]` is of finite type
  over the noetherian ring `K` (`Algebra.FinitePresentation.of_finiteType`).
  Since `K → K[B]` is of finite type, the map itself is of finite presentation
  (`RingHom.FinitePresentation.of_comp_finiteType`).

### Diagonalizable restriction maps over a field `K`

The underlying scheme map of `restrictMap f` is `Spec` of the group-algebra map
(`Diagonalizable.restrictMap_left`, module
`Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat`).

- `isClosedSubgroup_restrictMap_iff`: `restrictMap f` is a closed subgroup iff
  `f` is surjective. This uses `CentralExtensionHopfSpec.surjective_of_isClosedImmersion`
  and `IsClosedImmersion.spec_of_surjective`.
- `flat_surjective_restrictMap_iff`: `restrictMap g` is flat and surjective iff
  `g` is injective. This uses `flat_and_surjective_SpecMap_iff` (faithful
  flatness implies injectivity) and the published
  `Diagonalizable.flat_and_surjective_restrictMap`.
- `locallyOfFinitePresentation_restrictMap`: for finitely generated `B` and
  `C`, `restrictMap g` is locally of finite presentation.
- `characterPointsEquiv_restrictMap`, `comp_restrictMap_eq_one_iff` and
  `mem_range_restrictMap_iff` describe points through
  `Diagonalizable.characterPointsEquiv`. Composing with `restrictMap g`
  restricts the character along `g`. A point is killed exactly when its
  character kills `im g`. A point lies in the range of `restrictMap f`
  exactly when its character factors through `f`.
- `range_kernelι_eq_range_iff`: the range of `kernelι (restrictMap g)` equals
  the range of `restrictMap f` iff `PointCriterion f g Γ(U, 𝒪)ˣ` holds for
  every test `U`. This uses `mem_range_kernelι_iff` (module
  `Langlands.GroupScheme.CentralIsogeny.Basic`).
- `characterPointsEquiv_id_injective`: the character of the universal point
  `𝟙 : D(Λ) → D(Λ)` is injective. By
  `DiagonalizableCharacter.lift_characterPointsEquiv_id`, its value at `m`
  corresponds to `single m 1` under `DiagonalizableCharacter.sectionsIso`, and
  the elements `single m 1` of `K[Λ]` are distinct.
- `splitCore`: take `B` and `C` finitely generated. Then `restrictMap f` is a
  closed subgroup with `IsFppfQuotient (range (restrictMap f)) (restrictMap g)`
  iff `Injective g ∧ Exact g f ∧ Surjective f`. For the forward direction,
  apply `exact_of_pointCriterion` to the universal points of `D(A)` and
  `D(B ⧸ g.range)`. For the converse, use `pointCriterion_of_exact` on
  every test.

### Transport, descent and characters

- `range_comp_iso_hom`, `transport` and `transport_iff`: the pair of
  conditions transports along isomorphisms `a`, `b`, `c` of the three groups,
  from `(j, r)` to `(a⁻¹ ≫ j ≫ b, b⁻¹ ≫ r ≫ c)`, and back. They use
  `IsClosedSubgroup.iso_comp`, `IsClosedSubgroup.comp_iso`,
  `SubgroupFunctor.range_iso_comp`, `IsFppfQuotient.comp_iso` and
  `IsFppfQuotient.comapIso`.
- `descent_iff`: let `p` be flat, surjective and quasi-compact. The pair of
  conditions for `(i, r)` is equivalent to the pair for their base changes
  along `p`.
  - Descent of the closed immersion uses the pullback square
    `baseChange_map_isPullback` and `closedImmersion_descendsAlong_fpqc` (module
    `Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent`).
  - Descent of the fppf quotient is
    `RelativeRoot.IsFppfQuotient.of_baseChange_iso`, applied with the identity
    isomorphism (module `Langlands.GroupScheme.Descent.AffineFppfQuotient`).
  - The converse uses `IsClosedSubgroup.baseChange`,
    `SubgroupFunctor.range_baseChangeHom` and `IsFppfQuotient.baseChange`.
- `restrictHom K f` is `restrictMap f` as a morphism of commutative group
  schemes. `restrictHom_comp_evalCharacter` shows that
  `restrictHom f ≫ evalCharacter m = evalCharacter (f m)`, checked on points
  with `Diagonalizable.pointsEquiv_restrictMap`.
- `grpIso e` is the isomorphism of underlying group schemes of an isomorphism
  `e` of commutative group schemes.

## Scope

The proof uses only the hypotheses of the statement: the finite Galois
extension, the three actual groups and morphisms, and the finitely generated
models, possibly with torsion. It proves both directions in full, including
the all-test kernel identity and both equivariance conclusions. Finite
generation is used only for local finite presentation of `restrictMap g`. The
proof does not use the `FiniteDimensional` and `IsGalois` hypotheses. It uses
only that `Spec L → Spec k` is fpqc and that the canonical Galois actions are
natural.
