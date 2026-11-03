# Vector groups, weight actions on them, and quotients by primitive coordinates

This module builds the vector group `𝔾ₐⁿ` over an affine base `Spec R` as a corepresented
group scheme, with its linear coordinates on points of every test scheme. It then does three
things:

- it lets a torus act on `𝔾ₐⁿ` through a character `χ`, scaling every coordinate by the
  value of `χ`;
- over a field, for a nonzero character of a split torus, it shows that this action has a
  unique weight vector structure of weight `χ`;
- for a corepresented group scheme with coordinate algebra `B`, it builds the homomorphism to
  `𝔾ₐⁿ` given by a family `y₁, …, yₙ` of primitive functions on the group. If `y`, together
  with finitely many further elements `z`, is a set of free polynomial generators of `B`
  over `R`, it proves that this homomorphism is an fppf quotient map. Its kernel is the
  subgroup functor where all `yᵢ` vanish.

The declarations are in namespace `Langlands.GroupScheme.VectorGroup`, except for
`Langlands.GroupScheme.AutomorphicAction.ofPoints`, `AutomorphicAction.ofPoints_act` and
`Langlands.GroupScheme.Corepresented.adjunction_homEquiv_symm_apply`. Throughout,
`R : CommRingCat.{u}`, `n : ℕ`, and `Γ(T.left, ⊤)` is the ring of global functions of a test
scheme `T : Over (Spec R)`.

## Actions from natural actions on points

`AutomorphicAction.ofPoints φ hnat hone hmul hmulr` builds an action by automorphisms
`AutomorphicAction H G` of a group scheme `H` on a group scheme `G` over a scheme `S`. The
input is a family of maps `φ T : (T ⟶ H.X) → (T ⟶ G.X) → (T ⟶ G.X)` on points over every
`T : Over S`, with these properties:

- `hnat`: it is natural, `a ≫ φ T h g = φ T' (a ≫ h) (a ≫ g)` for `a : T' ⟶ T`;
- `hone`: `φ T 1 g = g`;
- `hmul`: `φ T (h * h') g = φ T h (φ T h' g)`;
- `hmulr`: `φ T h (g * g') = φ T h g * φ T h g'`.

The action morphism `H.X ⊗ G.X ⟶ G.X` is `φ` applied to the two projections, i.e. to the
universal point. `ofPoints_act` states that its action on points is `φ`:
`(ofPoints φ hnat hone hmul hmulr).act h g = φ T h g`. Both follow from naturality, since
every pair of points `(h, g)` is the pullback of the universal point along `lift h g`.

## The vector group

- `functor R n : CommAlgCat R ⥤ GrpCat` sends an `R`-algebra `A` to the additive group
  `Aⁿ = Fin n → A`, written multiplicatively (`Multiplicative (Fin n → A)`). An algebra map
  acts coordinatewise (`functor_map_apply`).
- `coordinateAlgebra R n` is the polynomial ring `MvPolynomial (Fin n) R` as an object of
  `CommAlgCat R`.
- `corepresentableBy R n` says that the polynomial ring corepresents `functor R n`: an
  algebra map `f` corresponds to the tuple `(f (X i))ᵢ`, and a tuple `x` corresponds to
  `aeval x` (`corepresentableBy_homEquiv`, `corepresentableBy_homEquiv_symm`).
- `groupScheme R n : GroupScheme (Spec R)` is the corepresented group scheme
  `Corepresented.groupScheme (functor R n) (corepresentableBy R n)`. Its underlying scheme
  is the spectrum of the polynomial ring.
- `coordinateSection R n i` is the global function `Xᵢ` on it, transported through
  `Scheme.ΓSpecIso`.
- `coordinates R n T : (T ⟶ (groupScheme R n).X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))`
  is the group isomorphism `Corepresented.pointsEquiv` between points over `T` and `n`-tuples
  of global functions on `T`.

The basic facts about coordinates are:

- `Corepresented.adjunction_homEquiv_symm_apply`: for a point `x : T ⟶ Spec B` of a relative
  spectrum, the algebra map `B → Γ(T)` adjoint to `x` sends `b` to the pullback
  `x.left.appTop` of the global function corresponding to `b`.
- `coordinates_apply`: the `i`-th coordinate of a point `x` is the pullback
  `x.left.appTop (coordinateSection R n i)`.
- `coordinates_comp`: coordinates are natural; for `f : W ⟶ T`, the coordinates of
  `f ≫ x` are the pullbacks along `f` of the coordinates of `x`.
- `points_ext`: two points with the same coordinates are equal.
- `coordinates_mul`: the coordinates of a product are the sums of the coordinates.

## Torus actions through a character

Let `S : CommGroupScheme (Spec R)` and `χ : characterLattice S`.

- `charValue χ T s : Γ(T.left, ⊤)` is the value of `χ` at a point `s : T ⟶ S.X`: the
  global unit `Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom χ).hom.hom)`, viewed as a
  function. It is `1` at `s = 1` (`charValue_one`), multiplicative (`charValue_mul`) and
  natural (`charValue_comp`: `charValue χ T' (a ≫ s) = a.left.appTop (charValue χ T s)`).
- `weightPointAction χ T s v` is the point whose coordinates are
  `charValue χ T s • (coordinates R n T v).toAdd` (`coordinates_weightPointAction`).
  It is natural (`weightPointAction_comp`), unital (`weightPointAction_one`), compatible
  with multiplication in `s` (`weightPointAction_mul`) and with multiplication in `v`
  (`weightPointAction_mul_right`). Each of these is checked on coordinates via
  `points_ext`.
- `weightAction χ : AutomorphicAction S.toGrp (groupScheme R n)` is
  `AutomorphicAction.ofPoints` applied to `weightPointAction χ`. By `weightAction_act`, its
  action on points is `weightPointAction χ`. `coordinates_weightAction_act` states that it
  scales all coordinates by the value of `χ`:
  `(coordinates R n T ((weightAction χ).act s v)).toAdd = charValue χ T s • (coordinates R n T v).toAdd`.

## Weight vector structures over a field

Let `k : Type u` be a field, `S : CommGroupScheme (Spec (CommRingCat.of k))` and
`χ : characterLattice S`.

- `isNaturalVectorCoordinates`: `coordinates (CommRingCat.of k) n` satisfies
  `RelativeRoot.IsNaturalVectorCoordinates`. This is `coordinates_comp`.
- `isWeightVectorCoordinates_weightAction`: these coordinates satisfy
  `RelativeRoot.IsWeightVectorCoordinates (weightAction χ) χ`. This is
  `coordinates_weightAction_act`, because `charValue` unfolds to the scalar in that
  definition.
- `hasUniqueWeightVectorStructure_weightAction (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0)`:
  the action `weightAction (n := n) χ` satisfies
  `RelativeRoot.HasUniqueWeightVectorStructure (weightAction χ) χ`, for every `n`. The proof
  applies `RelativeRoot.hasUniqueWeightVectorStructure_of_coordinates` (module
  `Langlands.GroupScheme.Rational.WeightVectorUniqueness`) to the coordinates above.

## Polynomial algebras over a subring of variables

Here `R` and `B` are commutative rings in `Type u` with `[Algebra R B]`, and `κ : Type u`. The
families are `y : Fin n → B` and `z : κ → B`. The hypothesis `hyz` states that
`aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B` is bijective, i.e. that
`y` and `z` together are free polynomial generators of `B`.

- `extensionMap y z : MvPolynomial κ (MvPolynomial (Fin n) R) →+* B` is the composite of
  `sumAlgEquiv` (inverted), a renaming along `Equiv.sumComm`, and `aeval (Sum.elim y z)`.
  It sends the inner variables to `y` and the outer ones to `z`.
- `extensionMap_bijective`: under `hyz`, `extensionMap y z` is bijective.
- `aeval_eq_extensionMap_comp`: `aeval y` equals `extensionMap y z` composed with the
  coefficient inclusion `MvPolynomial (Fin n) R → MvPolynomial κ (MvPolynomial (Fin n) R)`.
  Both sides agree on constants and on variables.
- `flat_aeval`: under `hyz`, `(aeval y).toRingHom` is flat. Indeed, a polynomial ring is free,
  hence flat, over its coefficients, and a bijection is flat.
- `finitePresentation_aeval` (with `[Finite κ]`): under `hyz`, `(aeval y).toRingHom` is of
  finite presentation. Indeed, a polynomial ring in finitely many variables is finitely
  presented over its coefficients, and a bijection is of finite presentation.
- `exists_retraction_aeval`: under `hyz`, there is a ring map
  `r : B →+* MvPolynomial (Fin n) R` with `r.comp (aeval y).toRingHom = RingHom.id _`. Take
  the inverse of `aeval (Sum.elim y z)`, followed by setting the `κ`-variables to `0`
  (`aeval (Sum.elim X 0)`).

## Quotients by primitive coordinates

Let `F : CommAlgCat R ⥤ GrpCat` be corepresented by `B : CommAlgCat R` through
`e : (F ⋙ forget GrpCat).CorepresentableBy B`, and let `y : Fin n → B`. Then
`Corepresented.groupScheme F e` is the group scheme over `Spec R` with underlying scheme
`Spec B`.

- `IsPrimitiveFamily e y` (a `Prop`) says that each `yᵢ` is primitive. Concretely, for every
  `R`-algebra `A`, all `x x' : F.obj A` and all `i`,
  `(e.homEquiv.symm (x * x')).hom (y i) = (e.homEquiv.symm x).hom (y i) + (e.homEquiv.symm x').hom (y i)`.
  Here `e.homEquiv.symm x : B ⟶ A` is the classifying algebra map of the point `x`, so its
  value at `yᵢ` is the value of `yᵢ` at `x`. In Hopf-algebra terms, `Δ yᵢ = yᵢ ⊗ 1 + 1 ⊗ yᵢ`.

Assume `hy : IsPrimitiveFamily e y`.

- `coordinateMap hy : F ⟶ functor R n` is the natural homomorphism sending `x` to the tuple
  `((e.homEquiv.symm x).hom (y i))ᵢ`. It is a homomorphism by `hy` and natural by
  `e.homEquiv_symm_comp`.
- `quotientMap hy : Corepresented.groupScheme F e ⟶ groupScheme R n` is the induced
  homomorphism of group schemes, `Corepresented.groupSchemeMap e (corepresentableBy R n)
  (coordinateMap hy)`.
- `homEquiv_symm_pointsEquiv_apply`: for a point `h` over `T` and `b : B`, the classifying
  map of `Corepresented.pointsEquiv F e T h` sends `b` to the pullback `h.left.appTop` of
  the global function corresponding to `b`.
- `coordinates_quotientMap`: the `i`-th coordinate of `h ≫ (quotientMap hy).hom.hom` is
  `(e.homEquiv.symm (Corepresented.pointsEquiv F e T h)).hom (y i)`, the value of `yᵢ` at
  `h`. It follows from `Corepresented.groupSchemeMap_points`.
  `coordinates_quotientMap_eq_appTop` states the same with the right-hand side written as
  `h.left.appTop` of the global function `yᵢ`.
- `quotientMap_left`: the underlying scheme morphism of `quotientMap hy` is
  `Spec.map (CommRingCat.ofHom (aeval y).toRingHom)`.
- `mem_range_kernelι_quotientMap_iff`: a point `x` over `T` lies in the kernel subgroup
  functor `SubgroupFunctor.range (kernelι (quotientMap hy))` exactly when
  `(e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom (y i) = 0` for all `i`. By
  `mem_range_kernelι_iff`, membership means that `x ≫ quotientMap` is the identity point,
  and points of `𝔾ₐⁿ` are determined by their coordinates.

Now let `κ : Type u`, `z : κ → B`, and let `hyz` say that
`aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B` is bijective.

- `flat_quotientMap hy hyz`: the underlying scheme morphism of `quotientMap hy` is flat.
- `locallyOfFinitePresentation_quotientMap hy hyz` (with `[Finite κ]`): it is locally of
  finite presentation.
- `surjective_quotientMap hy hyz`: it is surjective.

The first two follow from `quotientMap_left`, `flat_aeval`, `finitePresentation_aeval` and
`HasRingHomProperty.Spec_iff`. For surjectivity, the retraction `r` from
`exists_retraction_aeval` gives a section `Spec.map r` of `Spec.map (aeval y)`. The composite
is `Spec.map` of the identity, hence an isomorphism and surjective, so
`Spec.map (aeval y)` is surjective (`Surjective.of_comp`).

**Main theorem** `isFppfQuotient_quotientMap hy hyz N hN`. Let `[Finite κ]`, and let
`N : SubgroupFunctor (Corepresented.groupScheme F e)` satisfy
`hN : ∀ T x, x ∈ N.carrier T ↔ ∀ i, (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom (y i) = 0`.
Then `RelativeRoot.IsFppfQuotient N (quotientMap hy)` holds. That is, the underlying morphism
is flat, surjective and locally of finite presentation, and
`SubgroupFunctor.range (kernelι (quotientMap hy)) = N`. The last part combines
`mem_range_kernelι_quotientMap_iff` with `hN`.

## Provenance

This is an internal supporting module for the proof task of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (module
`Langlands.GroupScheme.Rational.WeightSemigroupStatement`). It follows the explicit
Hopf-algebra route agreed between that task's two executors. In that route, each successive
quotient of the cyclic-tail filtration is identified with a vector group through primitive
coordinates, on which the torus acts through a single character. This mirrors the role of
vector group quotients in the proofs of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*
(2nd ed., 2015), Proposition 3.3.6 and Lemma 3.3.8 (printed pp. 109–112). The module does
not formalize a statement from that source. Its contents are standard facts:
the corepresentation of `𝔾ₐⁿ` by a polynomial ring, scaling actions through a character, and
flatness, finite presentation and surjectivity of the inclusion of a polynomial subring
generated by part of a set of free generators. The statement shapes of `IsPrimitiveFamily`
and `isFppfQuotient_quotientMap` were fixed with the task's first executor. The proofs are
self-contained modulo Mathlib and the cited Library modules.
