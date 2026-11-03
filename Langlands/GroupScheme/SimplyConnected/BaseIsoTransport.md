# Simply connected covers under isomorphisms of base fields

Let `k` and `K` be arbitrary fields in universe `u`, and let
`b : Spec K ⟶ Spec k` be an isomorphism. Write `F` for the actual group-scheme
pullback functor `GroupScheme.baseChange b`, and `R` for pullback along `b⁻¹`.
This module proves transport along this specified base isomorphism. All
simply-connectedness and central-isogeny predicates retain their original
scheme-theoretic definitions.

## Connected reductivity and semisimplicity

`IsConnectedReductive.baseChange_of_bijective` first treats `b = Spec φ` for
a bijective homomorphism `φ : k → K`. Mathlib's
`IsAlgClosure.equivOfEquiv` extends the field equivalence to an equivalence
`E : AlgebraicClosure k ≃+* AlgebraicClosure K` commuting with the two
algebraic-closure maps. The actual iterated pullback comparisons in
`Descent.Data` identify the geometric base change of `FG` with the pullback of
the geometric base change of `G` along `Spec E`. The published
`HasTrivialUnipotentRadical.baseChange_of_bijective` transports the trivial
unipotent radical, and invariance under the comparison isomorphism gives the
required geometric property. Smoothness and affineness are stable under
pullback; `connectedSpace_baseChange_of_isIso` supplies connectedness.

`IsConnectedReductive.baseChange_of_isIso` covers every isomorphism of field
spectra. Full faithfulness of `Spec` writes it as the spectrum of its preimage
ring homomorphism, which is bijective by `isIso_SpecMap_iff`.

`IsSemisimple.baseChange_of_isIso` combines connected-reductivity transport
with the published `HasFiniteCenter.baseChange`. The finite centre remains a
representative of the entire centre functor on all test schemes, including its
possibly nonreduced structure.

## Simple connectedness and the universal property

`IsSimplyConnected.baseChange_of_isIso` proves algebraic simple connectedness
of `FG`. For an incoming semisimple central isogeny `q : H ⟶ FG`, pull back
along `b⁻¹` and compose with the comparison `RFG ≅ G`. The source `RH` is
semisimple by the preceding restricted transport theorem. Arbitrary
central-isogeny base change and target-isomorphism transport make this a
central isogeny into `G`. Simple connectedness of `G` makes the composite an
isomorphism. Cancellation gives invertibility of `Rq`, and the published
base-change reflection theorem gives invertibility of `q`.

`HasCentralCoverUniversalProperty.baseChange_of_isIso` transports the
explicit unique-factorization property of a supplied map `π : C ⟶ G`.
Let `e : RF ≅ id` be `baseChangeSectionNatIso`. For an incoming semisimple
central isogeny `q : H ⟶ FG`, form
`q₀ = Rq ≫ e_G : RH ⟶ G`. The original universal property supplies the
unique `a₀ : C ⟶ RH` satisfying `a₀ ≫ q₀ = π`.

The two inverse-base pullback comparisons exhibit `F` and `R` as a
categorical equivalence. In particular, `R` is fully faithful, so
`e_C ≫ a₀ : RFC ⟶ RH` has an actual preimage `a : FC ⟶ H`. Applying `R`,
postcomposing with `e_G`, and using naturality of `e` proves
`a ≫ q = Fπ`. Any competing `t` gives the original factorization
`e_C⁻¹ ≫ Rt`; uniqueness of `a₀`, cancellation and faithfulness give `t = a`.
This argument uses the specified natural isomorphism `e` consistently;
it requires no equality between `e` and the adjusted unit of the categorical
equivalence.

`IsSimplyConnectedCover.baseChange_of_isIso` combines the transported
semisimplicity, simple connectedness, central isogeny and universal property
into the full cover predicate for `Fπ`.

## Actual comparison of supplied covers

Suppose `π : C ⟶ G` is a supplied simply connected cover over `k`,
`π' : C' ⟶ G'` is a supplied simply connected cover over `K`, and
`d : FG ≅ G'` is a specified target isomorphism. The data-valued construction
`IsSimplyConnectedCover.isoOverBaseIso` gives an actual isomorphism
`FC ≅ C'`. It applies `CoverComparison.isoOver` to the transported first
cover and the supplied second cover.

`isoOverBaseIso_hom_comp` proves exactly
`(isoOverBaseIso hπ hπ' b d).hom ≫ π' = Fπ ≫ d.hom`.
`hom_eq_isoOverBaseIso` says every homomorphism satisfying that equation is
the forward map of this isomorphism. `existsUnique_lift_over_baseIso`
packages existence and uniqueness among all homomorphisms.

## Provenance and scope

These are internal deductions from the Library predicates and actual pullback
constructions, Mathlib's extension of field equivalences to algebraic closures,
and its categorical equivalence and full-faithfulness infrastructure. The
module imports published transport and reflection results by Lean name; no
external source assertion or new axiom is introduced.

Both covers and the two specified isomorphisms are inputs to the selected
comparison. This module proves no cover existence, tensor-product
decomposition or effective descent. Its base map must be an isomorphism;
the arbitrary-field-extension theorem remains a separate obligation.
