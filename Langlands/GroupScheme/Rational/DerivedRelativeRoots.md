# Relative roots through the actual derived inclusion

Authors: Worker 27 and Worker 1631. Worker 1631 supplied the
`DerivedRootTransport` support used to detect characters by the torus product.

Over a field `k : Type u`, let `d : D ⟶ G` be a supplied actual derived
inclusion, with `D` affine and locally of finite type and `G` affine and
smooth. Let `T`, `S` and `A` be split tori, with maps
`j : T.toGrp ⟶ D`, `i : S.toGrp ⟶ G`, `e : T ⟶ S` and `c : A ⟶ S`.
Assume the commuting square

`j ≫ d = CommGroupScheme.groupHom e ≫ i`.

Assume also that the actual product homomorphism
`RelativeRoot.centralComplementProduct e c : T.toGrp ⊗ A.toGrp ⟶ S.toGrp`
is flat and surjective on schemes, and that
`CommGroupScheme.groupHom c ≫ i` is central in `G`.
The maps and these structural properties are supplied; no maximality or
rational-point surjectivity is asserted.

The definition `RelativeRoot.derivedRelativeRootEquiv` constructs an
equivalence

`relativeRoots i ≃ relativeRoots j`.

Its forward map sends an ambient root `a` to the literal character
restriction `e ≫ a`. The lemma `derivedRelativeRootEquiv_val` proves this
evaluation formula by reflexivity. The equivalence concerns the existing
relative-root sets, defined by the nonzero adjoint Lie weight spaces, and
does not replace either set by its image.

The proof has three parts.

- `mem_relativeRoots_precomp_derived` proves that every ambient root
  restricts to a derived root. Centrality makes the root vanish on `A`.
  The flat-surjective torus product then detects that its restriction to
  `T` is nonzero. A nonzero vector in the ambient root's weight space lies
  in the actual differential image of `d`, by the derived-tangent theorem.
  Its restricted weight is preserved when lifting through the differential,
  by `Lie.exists_weightSpace_preimage`. A zero source vector would map to
  zero, so the derived weight space is nonzero.
- `exists_relativeRoot_precomp_eq_derived` proves surjectivity.
  The derived inclusion is a monomorphism, so it injects a nonzero derived
  weight vector into the ambient Lie module with the same `T`-weight.
  The split-torus theorem `mem_roots_comp_iff` then supplies an original
  `S`-root restricting to that weight. This argument does not require
  character detection by the central product.
- `precomp_injective_relativeRoots_derived` proves injectivity.
  Both ambient roots vanish on the central factor. If their restrictions
  to `T` agree, their difference therefore restricts to zero on both
  factors. The product detects nonzero characters, forcing the difference
  to be zero.

This is an internal construction from `Derived.TorusTangent`,
`Lie.TargetCoefficients`, `Torus.WeightRestriction`, and the character
detection and central-root restriction results used by
`Rational.DerivedRootTransport`. The inverse is chosen from the proved
bijectivity; no formula for it is claimed.

The module does not construct the derived maximal split torus, the central
complement or their flat-surjective product. It also does not construct a
source apartment, prove full omega compatibility of such an apartment, or
prove the final simply connected normalizer-image theorem. These remain
separate obligations.
