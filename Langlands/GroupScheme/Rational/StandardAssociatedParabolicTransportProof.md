# Whole standard parabolic and radical transport in associated Levis

The theorem `Langlands.GroupScheme.standardAssociatedParabolicTransport` has
exactly the published type
`Langlands.GroupScheme.StandardAssociatedParabolicTransportStatement.{u}`.
It proves the target from
`Langlands.GroupScheme.Rational.StandardAssociatedParabolicTransportStatement`
by reusing the published construction in
`Langlands.GroupScheme.Rational.StandardAssociatedConjugation`. This is an
internal derived proof; it introduces no external source assertion.

The scope is every universe `u`, every field `k`, every connected reductive
group scheme `G` over `Spec k`, every actual maximal split torus
`i : T.toGrp ⟶ G`, and every generic cocharacter `ν`. It retains every finite
enumeration of `SimpleRoot i ν` and `relativeWeylGroup i`, every Coxeter system
`cs` on that actual quotient with the target's
`IsRelativeWeylCoxeterRealization i ν cs` premise, every finite subset `J`,
every `n : normalizerPoints i` with class `longestRep cs J`, and every
`I : Finset (associatedSubset cs J)`.

The implemented proof introduces the quantified data and installs the affine
instance `hG.isAffineHom` and the monomorphism instance
`hi.isSplitSubtorus.mono`, exactly as in the target definition. After
introducing the genericity premise, finite enumerations, Coxeter data and
realization proof `h`, it introduces `J`, `n`, its class equation `hn`, and `I`.
It then applies the published theorem
`associatedStandardSubgroups_eq_comap i ν cs h J n hn I`. That theorem yields
the conjunction of the two literal subgroup-functor equalities required by
`IsStandardAssociatedParabolicTransport`:

```text
restrictedStandardParabolic i ν (associatedSubset cs J) I
  = comap(Int(n), restrictedStandardParabolic i ν J (associatedFinsetEquiv cs J I))
restrictedStandardUnipotent i ν (associatedSubset cs J) I
  = comap(Int(n), restrictedStandardUnipotent i ν J (associatedFinsetEquiv cs J I)).
```

Here `Int(n)(x) = n*x*n⁻¹`, so forward conjugation by the same supplied `n`
carries the source family to the target family. The direction of
`associatedFinsetEquiv cs J` is unchanged: it sends finite subsets of
`associatedSubset cs J` to finite subsets of `J`. The imported theorem proves
equalities of the actual subgroup functors on every test scheme, including
nonreduced tests. The proof does not pass to rational points. It retains empty
subsets, empty simple-root types, all characteristics and potentially
nonreduced relative root systems.

The imported construction derives the required standard cocharacters and
actual character images from the already quantified realization, then applies
the generic all-test restricted-family transport theorem. It needs no
additional genericity premise, so the target's genericity hypothesis is
introduced but unused here. No structural-theorem assumption has been added.
The existence of an actual Coxeter realization and the separate Levi-only,
minimum-source, outer opposite-family and representation comparisons remain
with their existing targets; this proof establishes exactly the whole positive
family transport proposition specified above.
