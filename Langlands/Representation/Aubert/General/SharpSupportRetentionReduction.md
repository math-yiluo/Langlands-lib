# Sharp support retention from induction–Jacquet stability

Implementation and documentation: Worker 219 (task
`d441ca88-a2fa-4174-93e0-97d1b9fca9ba`).

This module reduces the support-retention target for the actual terminal
cokernel `E#` to the stability of `Alg({I})` under the actual normalized
composites `i_K r_K`. It defines the coordinate projections of the homogeneous
objects of the standard complex and proves two closure laws of `Alg({I})`. It
asserts no target and imports no proof of either target. The stability is an
explicit hypothesis of both reductions.

## Generic lemmas on smooth representations (`Langlands.SmoothRep`)

These hold for smooth representations over any field `R` of any topological
group, at any universes.

* `not_isSubquotient_of_subsingleton hD`: if `C` is a subsingleton (the zero
  representation) and `D` is irreducible, then `D` is not a subquotient of `C`.
  A subquotient datum `B ↪ C`, `B ↠ D` forces every vector of `D` to be zero.
  Then `⊥ = ⊤` in the subrepresentation lattice of `D`, which irreducibility
  excludes. (A `ℂ`-specific lemma with the same short name exists in the GL
  classification module `SegmentHeadDerivativeSupportLengthTwo`. It lives in a
  different namespace, outside this module's import closure.)
* `exists_isSubquotient_of_jointlyInjective p hp hD h`: let `J` be finite, and let
  `p j : X ⟶ T j` be intertwiners that are jointly injective: `x = 0` whenever
  `p j x = 0` for every `j`. Every irreducible subquotient `D` of `X` is then a
  subquotient of some `T j`. No finite-length hypothesis is used. The proof
  shows, by induction on a finset `F ⊆ J`, the following claim. If `i : C ⟶ X` is
  injective, every `p j ∘ i` with `j ∉ F` vanishes, and `D` is a subquotient of
  `C`, then `D` is a subquotient of some `T j`.
  * For `F = ∅`, joint injectivity makes `C` a subsingleton, which contradicts
    the first lemma.
  * For `F = insert a F'`, the Library's
    `SmoothRep.irreducibleSubquotient_kernel_or_image` applied to `i ≫ p a`
    gives two cases. In the first, `D` is a subquotient of the kernel, which
    embeds in `X` through `kernelι ≫ i` and is killed by `p a`, so the induction
    hypothesis for `F'` applies. In the second, `D` is a subquotient of the
    image, which is a subrepresentation of `T a`; conclude with
    `smoothSubquotientTransitivity`.

  The lemma is the claim for `F = univ`, `C = X` and `i = 𝟙 X`.

## Closure laws of `Alg({I})` (`Langlands.Aubert.General`)

* `IsInSupportCategory.of_jointlyInjective p hp hT`: if `X` admits a finite
  jointly injective family of intertwiners into members `T j` of `Alg({I})`, then
  `X ∈ Alg({I})`. Each irreducible subquotient of `X` is a subquotient of some
  `T j` by the previous lemma. This is the finite direct-sum step; the
  intertwiners need not be surjective.
* `IsInSupportCategory.of_isQuotient hE hFE`: an actual quotient
  (`SmoothRep.IsQuotient F E`) of a member `E` of `Alg({I})` lies in
  `Alg({I})`. This is the Library's `IsInSupportCategory.of_isSubquotient`
  composed with `IsQuotient.isSubquotient`.

## Coordinate projections of the standard complex

For a smooth `A`, a degree `k`, and `s` with `s.card = k`,
`StandardComplex.degreeProjection P M U h hclosed A k s` is the projection of
the actual homogeneous object
`StandardComplex.degreeObject P M U h hclosed A k` onto its factor
`(inductionJacquetFunctor (h (univ \ s)) (hclosed (univ \ s))).obj A`, that is,
onto `i_{S \ s} r_{S \ s}(A)`. The degree representation is the finite product
`FiniteProduct.representation` of the term representations over the subsets of
cardinality `k`. Its underlying linear map is `LinearMap.proj s`, and it
intertwines by definition of the product action.
`StandardComplex.degreeProjection_jointlyInjective` records that these
projections are jointly injective (function extensionality on the product).

## The reductions

`sharpSupportRetention_of_supportCategoryInductionJacquet hIJ` proves
`SharpSupportRetentionTarget P M U h hclosed hδ hP hU hM hL IsAssociate` at
universes `uI, uG, uV` from
`SupportCategoryInductionJacquetTarget P M U h hclosed hM hL IsAssociate` at
universes `uI, uG, max uI uV`. Both statements then concern representations
with carriers in `Type (max uI uG uV)`.

Proof. Let `E ∈ Alg({I})` and `k = terminalDegree I = |S| - |I|`. By `hIJ`, each
`i_{S \ s} r_{S \ s}(E)` with `s.card = k` lies in `Alg({I})`. The projections
`degreeProjection … E k s` are jointly injective, so `of_jointlyInjective` puts
the degree object `degreeObject … E k` in `Alg({I})`. By definition,
`sharpObject … E I = terminalObject … E k` is the quotient of the degree
representation by the boundary. Its canonical projection
`StandardComplex.terminalProjection` is surjective
(`Complex.terminalProjection_surjective`), so `E#` is an actual quotient of the
degree object, and `of_isQuotient` concludes. Exactness of the complex is not
used.

`RationalPointFamily.rationalSharpSupportRetention_of_inductionJacquet hIJ`
proves `RationalSharpSupportRetentionStatement.{u, v}` from
`RationalSupportCategoryInductionJacquetStatement.{u, v}`. After introducing all
binders of the target, it applies the generic reduction at universes
`u, u, max (u + 1) v` with the literal families `parabolic i ν`, `levi i ν`,
`unipotent i ν` and the derived data the target fixes. The hypothesis is applied
to the same `k`, `G`, `hG`, `T`, `i`, `hi`, `ν`, `hν`, `hStandard`, `hInter`,
`hRoots`, `hN`, `hZ`, `hU` and `hM`. The `max uI uV` universe of the generic
hypothesis is then `max u (max (u + 1) v) = max (u + 1) v`, which is the
universe of the rational stability statement. The target's extra premises
`hOrder` and `hUc` are used only to form the target's own `hP`, `hU` and `hδ`.
The target's linear order on `SimpleRoot i ν` is the order on which the
standard complex is built.

## Dependencies

Besides the two target modules it imports, the module uses the Library's
`SmoothRep.isSubquotient_iff_exists`,
`SmoothRep.irreducibleSubquotient_kernel_or_image`, `SmoothRep.kernel`,
`kernelι`, `image`, `subrepresentation_isSubrepresentation`,
`IsSubrepresentation.isSubquotient`, `IsQuotient.isSubquotient`,
`smoothSubquotientTransitivity`, `IsInSupportCategory.of_isSubquotient`,
`StandardComplex.terminalProjection` and
`Complex.terminalProjection_surjective`. It uses no Langlands classification,
character independence, geometric lemma or adjointness result.

## Provenance

The retention target is derived: it is needed to iterate `#` on `Alg({I})`
(Aubert, *Erratum*, Trans. AMS 348 (1996), p. 4687 for `Alg({I})` and p. 4690
for `E#` as the cokernel of `d_{|I|}`). As `SharpConsequenceStatements.md`
explains, `E#` is a quotient of a finite direct sum of the `i_J r_J E`. The
retention therefore follows from stability under these composites (Renard,
Théorème VI.7.2 and Proposition VI.7.3) together with the closure of `Alg({I})`
under finite sums and quotients. This module formalizes that deduction. The
joint-injectivity lemma replaces the source's implicit use of finite direct sums
and avoids any finite-length assumption.

No declaration uses axioms beyond Lean's standard ones.
