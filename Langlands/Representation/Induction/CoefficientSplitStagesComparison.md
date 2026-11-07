# Native coefficient compact split stages comparison

This internal construction assembles compact induction in stages, the native
normal/split comparison, and the native relative kernel integral. All quotient
maps and representation equivalences are linear over the original coefficient
algebra. It is an unnormalized intermediate construction for the actual
universal-family Jacquet-finiteness task.

## Coefficients, groups and measures

Let `R` be a commutative complex algebra. Let `V` be an additive commutative
group with compatible `R`- and complex-module structures, expressed by
`IsScalarTower ℂ R V`. No topology, finite generation, dimension or length
condition is imposed on `V`. The coefficient algebra, ambient group, section
group, inducing carrier and target carrier for naturality have independent
universe parameters `uR`, `uG`, `uL`, `uV` and `uW`.

Let `G` be a locally compact Hausdorff topological group, `L` a topological
group, and `r : G →* L`, `s : L →* G` continuous with `r(s(l)) = l`.
Let `H ≤ P ≤ G` be closed, assume `ker r ≤ P`, and suppose `s(l) ∈ H`
for every `l ∈ P.comap s`. The inducing representation `σ` is a smooth
`R`-linear representation of the actual subgroup `H`.

Write `K = P.comap s`, `HP = H.subgroupOf P`, and let `φ : HP →* H`
be the underlying homomorphism of `Subgroup.subgroupOfEquivOfLe hHP`.
Then `σP = σ.comp φ` is the original inducing action on the intermediate
subgroup and `ρP = compactInduced HP σP`. The imported restricted retraction
`rP = splitStagesRetraction r s hrs P hker : P →* K` sends `p` to
`r(p)`, and its section is `sP = s.subgroupComap P`. The identity
`rP.ker = r.ker.subgroupOf P` is proved in `SplitStagesRetraction`.
The actual inner intersection is `I = HP.comap rP.ker.subtype`, with action
`σI = σP.comp (rP.ker.subtype.subgroupComap HP)`.

The assembly takes compact-open subgroup neighborhood bases for `G` and
`rP.ker`, closedness of `r.ker`, and local compactness and Borel structures
for `rP.ker`. It takes Borel structures on `I` and its left quotient,
regular left and right invariant Haar measures `μN`, `μI` on `rP.ker`
and `I`, and a compatible quotient measure `ν` finite on compact sets.
`IsCompatible I μN μI ν` is the imported measure-theoretic condition
including the Weil formula and right-translation invariance. Local
compactness of `P` and `I` is derived from closedness when needed. Existence
of these supplied measure data is outside this construction. None of the
hypotheses supplies a representation comparison or a finiteness conclusion.

## Original maps and the Haar character

All new declarations are in `Langlands.Induction.Coefficient`. The private
section-membership lemma restricts `hsH` to `HP`; the private smoothness lemma
restricts `σ` through `φ`, so no new smoothness premise is imposed on `σP`.

Let `χC` be `Jacquet.complexCharacter` of the published positive Haar
character `splitKernelHaarRatio rP sP HP hSI hHPc`. Its value is the
subgroup-to-kernel Haar ratio for forward precomposition by inverse
conjugation through the section. The native character is

```text
χ = MonoidHom.comp
      (Units.map (RingHom.toMonoidHom (algebraMap ℂ R))) χC.
```

Thus the coefficient action used by the comparison is exactly
`κ = twist χ (Coefficient.splitKernelCoefficientAction rP sP HP hSI σP)`
on the original native quotient `Representation.Coinvariants σI`.
On representatives the untwisted action sends `[v]` to `[σ(s(l)) v]`
with the actual subgroup inclusions. This unnormalized comparison retains
the Haar character; no normalization cancellation is asserted.

`splitStagesInnerEquiv` first uses the native `normalCoinvariantsCongr`
and `restrictAlongEquiv` to identify the two actual kernel subgroups, then
applies `Coefficient.splitKernelCompactEquivariantEquiv`. It is a native
`R`-linear representation equivalence from
`((compactInduced HP σP).toCoinvariants (r.ker.subgroupOf P)).comp sP`
to `κ`. `splitStagesInnerIntegral` names its actual relative integral on
compact functions before descent; `splitStagesInnerEquiv_mk` identifies
this integral with the value of the equivalence on a quotient representative.

`splitStagesCompactEquiv` is an `R`-linear equivalence of actual
`L`-representations from

```text
((compactInduced H σ).toCoinvariants r.ker).comp s
```

to `compactInduced K κ`. Its forward map is the composition of the inverse
of the published arbitrary-coefficient `compactStagesEquiv`, the native
`normalCoinvariantsEquiv` restricted through `s`, the native
`normalSplitCompactEquiv`, and compact induction of `splitStagesInnerEquiv`.
Each component is a proved equivalence on the original covariant functions
or actual relation quotients. Bijectivity is inherited from those proofs.

## Integral formula on representatives

`splitStagesSlice` takes the inverse stages map and evaluates the resulting
outer compact function at `x : G`. Its value at `q : P` is exactly
`f(q*x)`, as proved by `splitStagesSlice_eval`. The function
`splitStagesKernelSlice` restricts this slice at `x = s(l)` to `rP.ker`;
`splitStagesKernelSlice_eval` gives the original value `f(n*s(l))`.

The complex scalar comparison `compactFunctionsComplexEquiv I σI`
preserves these original values. The simple function
`quotientCoinvariantSimple I (complexRepresentation σI)` applied to that
comparison takes the complex quotient class of `f(n*s(l))` at the quotient
representative of `n`. The native comparison
`fullCoinvariantsComplexEquiv σI` sends that class to the original native
`R`-quotient class. This is the assertion of `splitStagesIntegrand_mk`.

`splitStagesCompactEquiv_eval_mk` proves that evaluating the image of `[f]`
at `l` gives the raw relative integral of the actual slice at `s(l)`.
`splitStagesCompactEquiv_eval_mk_integral` writes it explicitly as

```text
fullCoinvariantsComplexEquiv σI
  (AlgebraicIntegral.integral ν
    (quotientCoinvariantSimple I (complexRepresentation σI)
      (compactFunctionsComplexEquiv I σI (splitStagesKernelSlice ... f l)))).
```

This finite-fiber integral needs no topology on the inducing module.
The scalar comparisons preserve original functions and quotient classes;
the resulting map is `R`-linear by the native relative-integral theorem.
The formula has no extra scalar. The Haar character occurs in its
intertwining law through `κ`.

## Naturality and provenance

`splitStagesCoefficientMap` is the actual intersection-coinvariant map
induced by an `R`-linear inducing intertwiner, bundled as an intertwiner of
the Haar-twisted actions. `splitStagesSlice_natural` proves pointwise that
the slice commutes with coefficient postcomposition.
`splitStagesInnerIntegral_natural` invokes native relative-integral
naturality, and quotient induction proves `splitStagesInnerEquiv_natural`.
Finally, `splitStagesCompactEquiv_natural` reduces to the representative
evaluation formula and those two identities. It quantifies over every
smooth target inducing representation on an independent carrier `W` with
compatible `R` and complex scalar structures. Its source map is the actual
map on kernel coinvariants of `compactInducedMap H T`; its target map is
`compactInducedMap K` of `splitStagesCoefficientMap`.

The construction is internally derived by composing the named published
and native prerequisites. Its organization follows the existing proved
complex assembly `SplitStagesComparison`, generalized to the native
coefficient algebra using the proved native transport and integral maps.
It claims no new theorem verbatim from an external source.

The parent `RationalSupercuspidalJacquetFamilyFiniteStatement` remains a
separate obligation. Applying this comparison there still requires actual
rational orbit and parabolic identifications, the necessary compatible
measure data, identification of the inner quotient with the refined source
Jacquet module, cancellation of all normalization characters, and the
coefficient-admissibility and compact-open fixed-module finiteness steps.
No such assertion is assumed or discharged in this intermediate unit.
