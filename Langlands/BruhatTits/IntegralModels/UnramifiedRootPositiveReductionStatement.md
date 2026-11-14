# Positive reduction in a single unramified root model

`UnramifiedRootPositiveReductionStatement.{u}` is a proposition at arbitrary
universe `u`. It states the integral-section criterion of Kaletha–Prasad
Lemma 8.4.4, equivalently the preimage assertion in Corollary 8.4.5(2), for
the actual root model constructed from a supplied compatible integral
apartment torus.

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F`, and
`O = fixedFieldIntegers F`. The supplied `C : MaximalUnramified.BuildingData F G`
carries the connected reductivity of `G`, its maximal split torus, actual
relative root groups, and their valued apartment. The supplied zero datum
`E` defines the subgroup `E.zeroPoints` in this same `G(K)`. Let `Ω` be any
nonempty apartment subset whose image under every real affine functional
is bounded above. This is the explicit boundedness condition used here.

The supplied relative-component model pair `D` has smooth affine neutral
model with connected fibres. Its actual integral-point image is required
to equal

```
E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω).
```

The compatible integral split apartment torus
`A : IntegralSplitTorusData D.neutral C.i` and the actual special-fibre
quotient `Q : SpecialFibreQuotientData D` are inputs. The predicate
`Q.IsReductiveQuotient` requires its specified radical to be the smooth
connected normal unipotent radical, its projection to represent the fppf
quotient by that radical, and its quotient group to be connected reductive.
Existence of these models, torus data, and quotient data is not asserted.

For each actual relative root `a`, `A.rootModel a a.2.1` is the smooth
affine integral model from `IntegralRootFiltration`, with its actual
compatible map `A.rootModelMap` to `D.neutral` and generic root inclusion
`A.rootInclusion`. For each integral section `u` of this root model, the
statement asserts

```
the reduction of u in D.neutral lies in Q.radicalPoints
  ↔ there exists x ∈ Ω such that the generic image of u lies in U_(a,x,0+).
```

Both images use the specified scheme maps. In particular, the left side
uses reduction of the integral image of `u`, and the right side uses
`A.rootInclusion` applied to its generic image. `Q.radicalPoints` is the
image of the actual radical's residue-field points. No surrogate reduction
map or freely chosen identification of root groups occurs.

The existing root-model point-image theorem and the arbitrary-zero-datum
root intersection identify the generic image of these sections with
`C.apartment.rootFixer a Ω`. Thus, in the source notation, the positive
subgroup in this criterion is

```
U_(a,Ω,0) ∩ ⋃ x ∈ Ω, U_(a,x,0+).
```

The existential quantifier is intentional. The Library's `rootFixerPlus`
uses positivity at every point, which is a different construction for
general bounded sets. This statement does not identify those two
constructions.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
§8.4.2–§8.4.3, Lemma 8.4.4 and Corollary 8.4.5, printed pp. 303–304 /
PDF pp. 334–335, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of November 1, 2024, PDF pp. 37–38, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
require perfect base residue field throughout §8.4, use the split torus
over `O`, insert the definition of the special-fibre root group in §8.4.2,
and replace the two occurrences of `k` by `K` in the proof of Lemma 8.4.4.
The local-field hypothesis retains the perfect residue-field scope.

The formulation uses the Library's explicit characterized model and
constructed root model in place of KP's named canonical models. Its
point criterion is the stated source assertion. It does not include the
scheme-level image equality of Corollary 8.4.5(1), identify the surviving
quotient roots, prove a model-map kernel smooth, or prove the incident-facet
Lie-weight sign formula. It is an unproved statement.
