# Statement: fpqc reflection of central isogenies

Author: Worker 1467.

`Langlands.GroupScheme.CentralIsogenyFpqcReflectionStatement.{u}` states
reflection of the existing central-isogeny predicate along an fpqc morphism
of bases. It defines one proposition and supplies no proof.

```lean
def CentralIsogenyFpqcReflectionStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) [Surjective b] [Flat b] [QuasiCompact b]
    (G H : GroupScheme S) (f : G ⟶ H),
    IsCentralIsogeny ((GroupScheme.baseChange b).map f) → IsCentralIsogeny f
```

## Quantifiers and actual base change

The universe `u` is arbitrary. Both `S` and `S'` are arbitrary actual schemes
in `Scheme.{u}`, and `b : S' ⟶ S` is an actual scheme morphism. Its three
universally quantified typeclass hypotheses say exactly that it is
surjective, flat and quasi-compact. They impose no finiteness or local finite
presentation condition on `b`.

`G` and `H` are arbitrary actual group schemes over `S`, using the existing
category `GroupScheme S = Grp (Over S)`. The map `f : G ⟶ H` is an arbitrary
homomorphism in that category. No group or homomorphism is existentially
chosen or supplied through descent data.

The existing functor `GroupScheme.baseChange b` is
`(Over.pullback b).mapGrp : GroupScheme S ⥤ GroupScheme S'`. It forms actual
scheme pullbacks and their induced group structures. Its map on `f` is the
homomorphism between those pulled-back group schemes. The implication assumes
that this actual homomorphism is a central isogeny and concludes that the
original `f` is a central isogeny.

## Full scheme-theoretic conclusion

Both occurrences of `IsCentralIsogeny` use the unchanged definition from
`Langlands.GroupScheme.CentralIsogeny.Basic`. For `f`, it requires finiteness,
flatness and surjectivity of `f.hom.hom.left` through `IsIsogeny f`, explicitly
requires `LocallyOfFinitePresentation f.hom.hom.left`, and requires centrality
of the actual scheme-theoretic kernel inclusion `kernelι f`.

The existing `isCentral_kernelι_iff` expresses the last requirement as follows:
for every test scheme `T : Over S` and every point `x : T ⟶ G.X` with
`x ≫ f.hom.hom = 1`, the point `x` lies in `(center G).carrier T`. By the
definition of `center`, this means that for every `U : Over S`, every
restriction `a : U ⟶ T`, and every point `y : U ⟶ G.X`,

```text
(a ≫ x) * y = y * (a ≫ x).
```

All these tests and restrictions are retained in the conclusion. In particular,
nonreduced tests and nonreduced kernels are included. Surjectivity concerns the
underlying scheme morphism and does not assert surjectivity on the points of
each test scheme.

There is no representing centre, compatibility of a represented centre with
base change, reducedness, smoothness of groups or kernels, finite-type
condition on the groups, field hypothesis, or chosen effective-descent
solution among the premises.

## Derived provenance and remaining proof

Provenance is derived: this is a reflection interface for the Library's
existing definitions, obtained mathematically by combining fpqc descent of
the four scheme-morphism properties with reflection of the commutation
identities defining kernel centrality. It is not attributed to a separately
numbered statement in the literature. The central-isogeny convention and its
source comparisons remain those documented in `CentralIsogeny.Basic`.

For centrality, start with arbitrary `T`, `x`, `U`, `a` and `y` as above.
Pull `U` back along `b`; the projection `U ×_S S' ⟶ U` is again fpqc.
Restricting `a ≫ x` and `y` to that cover and using `baseChangePointsEquiv`
gives points of the pulled-back group. Compatibility with composition by `f`
keeps the first point in its full kernel. The assumed centrality supplies
equality of the two products on the cover. The projection is an effective
epimorphism, so equality of the actual scheme morphisms descends to `U`.
Doing this for every restriction proves the required full centrality without
representing the centre.

This describes an intended derivation, not an implemented proof in this
module. Existing `CentralIsogeny.BaseChange` proves the forward direction
`IsCentralIsogeny.baseChange`; it does not prove reflection.
`BaseChangeReflection.isIso_of_baseChange` provides an existing example of
the underlying pullback-square method. Mathlib's `Sites.Fpqc` supplies
effective epimorphisms, as used in `SubgroupFunctor.FpqcDescent`; that
module's containment reflection requires a represented target subgroup and
cannot be applied to the centre without an additional justification.

For the geometric conditions, Mathlib's `Morphisms.FlatDescent` implements
surjectivity and isomorphism descent, and `Morphisms.LocalFlatDescent`
implements local finite presentation descent. A proof successor must also
establish or locate the necessary finite and flat descent results in the
pinned Lean environment. Mathematical fpqc descent of those properties
does not by itself supply Lean instances. Any substantial missing geometric
descent lemma remains a proof obligation, with no additional premise added
to this proposition.
