# Normalized induction in stages for actual nested subgroups

`Langlands.Aubert.General.NestedInduction.iso` constructs the natural induction
comparison used in the proof of Renard VI.1.4. This is an internal, derived
construction from the existing smooth induction, split-quotient and
character-twist equivalences. It is conditional on the explicit intermediate
hypotheses below. It does not prove the dynamic-parabolic target or the Jacquet
comparison.

Let `G : Type uG` be a locally compact nonarchimedean group. Assume the
semidirect decompositions `hP : P = M N` and `hQ : Q = L U`, closedness of
`L`, `N`, and `U`, the inclusions `P ≤ Q`, `M ≤ L`, and `U ≤ N`, and a
semidirect decomposition `hInner` of the literal subgroup `P.subgroupOf L`
with Levi `M.subgroupOf L` and radical `N.subgroupOf L`. Also assume that
the actual projection `hQ.projection : Q →* L` is continuous and that the
modulus of each of `N` and `U` is trivial on that subgroup, expressed by
`IsUnimodularModulus N hN` and `IsUnimodularModulus U hU`.

The remaining hypothesis is `NestedInduction.HalfCharacterProduct`: for every
`p : P.subgroupOf L`, the half-character of `N` at the corresponding point
of `P` equals the product of the half-character of `U` at `(p : L)` and the
half-character of `N.subgroupOf L` at `p`. These intermediate hypotheses
must all be discharged when applying this construction to the published
dynamic-parabolic statement.

The resulting natural isomorphism is

```text
normalizedInductionFunctor hP hN ≅
  leviNormalizedInductionFunctor hL hML hInner hN ⋙
    normalizedInductionFunctor hQ hU.
```

The group universe `uG` and the representation-carrier universe `uV` are
independent. The source is the full category of smooth complex
`M`-representations with carriers in `Type uV`. Both functors take values in
the full smooth `G`-category with carriers in `Type (max uG uV)`. The inner
functor uses the existing transport `M.subgroupOf L ≃ₜ* M`.

The object component `NestedInduction.equiv` first uses smooth induction in
stages to expand a direct induced function. It then restricts the inner
function along the continuous Levi section. The projection kernel lies in
`P.subgroupOf Q` because `U ≤ N ≤ P`, and acts trivially on the inducing
coefficients by unimodularity of `N`. The split-quotient equivalence therefore
identifies the inner induction with inflation from `L`. The half-character
product and the compatibility of the actual Levi projections identify the
restricted coefficients with the inner normalized coefficients twisted by
the outer half-character. The inverse character-twist equivalence removes
that outer character from the function. Finally, unimodularity of `U`
identifies the remaining outer twist with its inflation along `hQ.projection`.

Writing `c(l)` for the `U` half-character on `L`, the implemented comparison
has the exact formula

```text
(equiv A f)(x)(l) = c(l)⁻¹ • f((l : G) * x).
```

`equiv_eval` proves this formula by definitional reduction, including the
underlying identity linear maps used to transport equal actions.
`equiv_natural` proves coefficient naturality by equality of the two
underlying smooth functions at each `x : G` and `l : L`; the remaining
equality is preservation of complex scalar multiplication by the
coefficient intertwiner. `iso` then applies `SmoothRep.mkIso` to the object
equivalences and packages these components with `NatIso.ofComponents`.

The construction is authored by Worker 691 for the joint task with Worker 194.
