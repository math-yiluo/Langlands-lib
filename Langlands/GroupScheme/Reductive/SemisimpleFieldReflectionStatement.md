# Reflection of semisimplicity under arbitrary field extension

Author: Worker 1360.

This module defines the proposition
`Langlands.GroupScheme.SemisimpleFieldReflectionStatement.{u}`. It states the
reflection direction of semisimplicity under field extension and supplies no
proof of that implication. Its only import is the unchanged module
`Langlands.GroupScheme.Reductive.Semisimple`.

## Quantifiers and actual base change

The universe `u` is arbitrary. The proposition quantifies over every pair
`k K : Type u`, every field structure on each, every `Algebra k K`, and every
actual `G : GroupScheme (Spec (CommRingCat.of k))`. Here a group scheme is the
Library's group object in the category of schemes over the indicated base.
The algebra structure specifies the ring homomorphism `algebraMap k K`; for
fields this homomorphism is injective. The extension may be transcendental,
inseparable or infinite. There is no perfectness or characteristic restriction,
so imperfect fields of positive characteristic are included.

Write

```text
b = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k,
G_K = (GroupScheme.baseChange b).obj G.
```

These expressions abbreviate the actual terms written inline in Lean. The
unchanged functor `GroupScheme.baseChange b` is `(Over.pullback b).mapGrp`;
its object is the scheme pullback with the induced group law. The proposition
is exactly `IsSemisimple G_K → IsSemisimple G`. Its sole mathematical premise
on `G` is semisimplicity of this scalar extension. In particular, reductivity,
affineness, smoothness, connectedness, centre representability or finiteness,
and effective descent of `G` are not inputs.

## The unchanged semisimplicity predicate

Both occurrences of `IsSemisimple` use the published predicate from
`Reductive.Semisimple`. Its two fields are:

- `isConnectedReductive : IsConnectedReductive G`: the structural morphism is
  smooth and affine, the underlying space is connected, and the geometric
  unipotent radical is trivial after base change to an algebraic closure of
  the field in question.
- `hasFiniteCenter : HasFiniteCenter G`: there exist an actual group scheme
  `Z` over the same field and an actual homomorphism `z : Z ⟶ G` such that
  `IsSchemeTheoreticCenter z` and `IsFinite Z.X.hom`.

In the second field, `IsSchemeTheoreticCenter z` means that the underlying
scheme morphism is a closed immersion and
`SubgroupFunctor.range z = center G`. The range on a test scheme `T` consists
of the points factoring through `z`. Membership of a point `x` in the centre
requires every restriction of `x` along every morphism `T' ⟶ T` to commute
with every `G`-point on `T'`. Equality here is equality of subgroup functors
on all test schemes over the field, with their restriction maps. Nonreduced
tests are included. The representative `Z` need not be smooth, reduced or
connected, so its nilpotents are retained. Finiteness means finiteness of the
structural morphism of this actual representative, rather than finiteness of
a rational-point or reduced centre.

Consequently the conclusion asks for both fields over `k`, including the
existential finite representative of the full centre. Centre descent is part
of the future proof obligation; it is not a hypothesis of this statement.

## Sources and derived packaging

The original source is J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Proposition 19.5, printed pp.398–399 (PDF pp.414–415), gives semisimplicity
invariance under an arbitrary extension field. Its proof reduces to
algebraically closed fields and uses spreading out. The present proposition
selects its reflection direction. Proposition 19.10, printed p.400 (PDF
p.416), characterizes semisimplicity of a reductive group by finiteness of
its centre. The preceding paragraph explicitly allows the centre to be
nonsmooth and disconnected. Those three source pages were read in full.

This is a derived formulation on the Library's actual group schemes, using
its finite-centre characterization as the semisimplicity predicate. Milne
does not write these Lean interfaces or their existential representative.
His algebraic-group framework has finite type built in; the Lean statement
quantifies over every actual `G` and imposes only semisimplicity after scalar
extension. A proof must establish all necessary descent and predicate
comparisons at that generality. No equivalence with a different radical-based
predicate, nor descent of the centre representative, is proved here.

The complete retained author errata was also read: source
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
Its Chapter 19 entry corrects Definitions 19.7 and 19.8, with no correction
to Propositions 19.5 or 19.10.

## Ascent and downstream use

The separately owned `Langlands.GroupScheme.IsSemisimpleFieldExtensionStatement`
in `Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement` states
`IsSemisimple G → IsSemisimple G_K`. This module states the reverse
implication as its own proof target. Neither proposition supplies a proof of
the other. No existing predicate or cover-existence interface is changed.

For a descended group whose scalar extension is isomorphic to a semisimple
group, existing isomorphism transport supplies semisimplicity after scalar
extension. A future proof of this target would then give semisimplicity of
the descended group. Constructing effective descent, reflecting central
isogenies, reflecting simple connectedness and constructing a covering
cocycle remain separate obligations.
