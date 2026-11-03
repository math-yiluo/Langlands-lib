# Lifting maximal split tori through a central isogeny

Author: Worker 1384. The Lean text is reproduced verbatim from the task
contract written by Workers 1463 and 1469; see Provenance below.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement`. The
Lean file only defines the proposition. It contains no proof of it, and it
adds no new definitions or axioms.

## Binders and hypotheses

The declaration is polymorphic in a universe `u`. It quantifies over every
`k : Type u` with `[Field k]`. The field is arbitrary: it may be imperfect
and may have positive characteristic. There is no separability,
characteristic, perfectness or kernel-smoothness hypothesis. Write
`Spec k` for `Spec (CommRingCat.of k)`. The proposition then quantifies
over the following data.

- Actual group schemes `G H : GroupScheme (Spec k)`, that is, group objects
  in schemes over `Spec k`, with `IsConnectedReductive G` and
  `IsConnectedReductive H`. This published predicate from
  [`Reductive.Basic`](../Reductive/Basic.md) says that the structure
  morphism is smooth and affine, that the underlying scheme is connected,
  and that the base change to an algebraic closure of `k` has trivial
  unipotent radical.
- An actual group-scheme homomorphism `π : G ⟶ H` with
  `IsCentralIsogeny π`. This published structure from
  [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md) has three fields:
  - `IsIsogeny π`: the underlying scheme morphism `π.hom.hom.left` is
    finite, flat and surjective;
  - `LocallyOfFinitePresentation π.hom.hom.left`;
  - `IsCentral (kernelι π)`: the full scheme-theoretic kernel of `π`, the
    pullback of `π` along the unit, is central. For every test scheme `U`
    over `Spec k`, every `U`-point of the kernel lands in the centre of `G`,
    and centre membership means commuting with every point of `G` after
    every further base change. Nonreduced test schemes and infinitesimal
    kernel points are included.
- An actual commutative group scheme `S : CommGroupScheme (Spec k)` and a
  homomorphism `i : S.toGrp ⟶ H` with `IsMaximalSplitTorus i`. This
  published predicate from [`Rational.SplitTorus`](SplitTorus.md) says
  three things. `S.toGrp` is a split torus, that is, isomorphic to
  `splitTorus (Spec k) I` for a finite `I : Type u`. The morphism
  `i.hom.hom.left` is a closed immersion. Finally, for every commutative
  group scheme `S'`, every split subtorus `i' : S'.toGrp ⟶ H` and every
  `g : S.toGrp ⟶ S'.toGrp` with `g ≫ i' = i`, the homomorphism `g` is an
  isomorphism.

The hypotheses mention no torus of `G`, so the lifted torus is not
assumed.

## Conclusion

There exist

- a commutative group scheme `T : CommGroupScheme (Spec k)`,
- a homomorphism `j : T.toGrp ⟶ G`, and
- a homomorphism of commutative group schemes `f : T ⟶ S`

such that

1. `IsMaximalSplitTorus j`: `T` is a split torus, `j` is a closed
   immersion, and `j` is maximal among split subtori of `G` in the
   factorization sense just described;
2. `j ≫ π = CommGroupScheme.groupHom f ≫ i`, an equality of homomorphisms
   `T.toGrp ⟶ H` in `Grp (Over (Spec k))`. Here
   `CommGroupScheme.groupHom f : T.toGrp ⟶ S.toGrp` is `f` with
   commutativity forgotten. So the square commutes, and `f` is the
   restriction of `π` to `T`, landing in `S`;
3. `Flat`, `Surjective` and `LocallyOfFinitePresentation` hold for
   `(CommGroupScheme.groupHom f).hom.hom.left : T.X.left ⟶ S.X.left`,
   the actual underlying morphism of schemes of `f`. Thus `f` is an fppf
   covering morphism of schemes.

All three objects are existential. No chosen torus, chosen preimage or
construction is presented. Surjectivity in item 3 is surjectivity of the
morphism of schemes, not surjectivity on `k`-points.

## What is not asserted

- The statement does not identify `T` with the inverse image of `S` in `G`.
  That inverse image contains the whole kernel of `π`, and this kernel need
  not lie in `T`. For example, let `D` be a quaternion division algebra over
  `k`, let `G = SL₁(D)` and `H = G/μ₂`. Both groups are anisotropic, so `S`
  and `T` are trivial, whereas the inverse image of `S` is the kernel `μ₂`
  of `π`.
- It does not assert that `f` is finite or that its kernel is central, so it
  does not assert `IsCentralIsogeny (CommGroupScheme.groupHom f)`. That
  stronger restriction is a separate adapter in the consumer task
  `68b5794b-3764-4cb2-b769-c1fc3ddf5bc2`. The adapter derives finiteness
  from the closed torus inclusions and the finite isogeny `π`, and
  centrality from commutativity of `T`.
- It does not assert that `f` is smooth or étale. The conclusion asks only
  for flatness. For instance, over a field of characteristic 2, the central
  isogeny `SL₂ → PGL₂` has kernel `μ₂`, which is not smooth. On the
  diagonal tori it restricts to `t ↦ t²` on `𝔾ₘ`, which is finite, flat
  and surjective but not smooth.
- It asserts nothing about `k`-points and no uniqueness of `T`, `j` or `f`.

## Sources and derived passage

The statement is derived, not a verbatim theorem.

**Source.** A. Borel and J. Tits, *Compléments à l'article « Groupes
réductifs »*, Publ. Math. IHÉS 41 (1972), 253–276, registered as
`borel-tits-1972-complements-groupes-reductifs`, SHA-256
`7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`.

- The standing convention at the end of the introduction, printed p.253
  (PDF p.2), takes `k` to be an arbitrary commutative field and `G` a
  connected reductive `k`-group. No separability is assumed in §2.
- Definition (2.2), printed p.254 (PDF p.3), calls a morphism central when
  the commutator factors through the image as a morphism. Remarque (2.3),
  same page, says that in the language of group schemes this means that
  the scheme-theoretic kernel lies in the centre. This is the field
  `IsCentral (kernelι π)` of `IsCentralIsogeny π`.
- Théorème (2.20)(ii), printed p.260 (PDF p.9), concerns a central
  surjective `k`-morphism `f : G → G'` with `G` connected reductive. It
  states: « Les tores déployés sur k maximaux de G' (resp. G) sont les
  images (resp. les tores déployés maximaux des images réciproques) des
  tores déployés sur k maximaux de G (resp. G'). » The proof, on the same
  page, uses Proposition (2.11), printed pp.256–257 (PDF pp.5–6). It takes a
  maximal `k`-torus `T'` of `G'` containing the given split torus and the
  maximal `k`-split torus of the torus `f⁻¹(T')`, and shows that this
  split torus maps onto the given one.

**Derived passage.** Apply the theorem to `π`, which is central by
Remarque (2.3) and surjective. Its source `G` is connected reductive, and
the target `H` is assumed connected reductive as well; the theorem itself
does not need the latter. Borel and Tits work with affine algebraic groups
over `k` in the classical sense. These correspond to the smooth affine
group schemes of finite type over `k` that `IsConnectedReductive` and
`IsSplitTorus` describe. The first clause of part (ii) gives a maximal
`k`-split torus `T` of `G` whose image `π(T)` is the supplied torus `S`.
The conclusions are obtained from this as follows.

1. Let `j` be the inclusion of `T`. It is a closed immersion and `T` is
   split. Classical maximality of `T` among `k`-split subtori is the
   Library's factorization maximality. A factorization `j = g ≫ j'`
   through a split subtorus `j'` forces `g` to be a closed immersion
   onto a torus containing `T`. That torus then equals `T`, so `g` is an
   isomorphism.
2. The torus `T` is reduced, and `j ≫ π` maps it set-theoretically into
   the closed subset underlying `i`. That closed subscheme is a torus, so
   it is reduced and carries the reduced induced structure. Hence
   `j ≫ π` factors through the closed immersion `i` by a morphism of
   schemes. The factor `f` is a homomorphism because `i` is a
   monomorphism. This gives the displayed equality.
3. `π(T) = S` says that `f` is surjective on points over an algebraic
   closure `k̄` of `k`. After base change to `k̄`, the image of `f` is
   closed, since the image of a homomorphism of algebraic groups is
   closed. It contains every closed point, so it is everything. Since
   `S` is the image of its base change to `k̄`, the morphism of schemes
   `f` is surjective. The scheme-theoretic
   kernel of `f` equals that of `j ≫ π`, because `i` is a monomorphism.
   It is the base change of the closed immersion `j` along the inclusion
   of `ker π`, hence a closed subscheme of the finite `k`-scheme `ker π`.
   So it is finite. It is central because `T` is commutative. Tori are
   reductive. B. Conrad, *Reductive group schemes* (2014), registered as
   `conrad-2014-reductive-group-schemes`, SHA-256
   `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
   Proposition 3.3.10, PDF p.103, says that a surjective homomorphism of
   reductive groups is a central isogeny when its fibres have finite
   central kernel. Its Definition 3.3.9, on the same page, defines a central
   isogeny as a finite flat surjection with central kernel. So `f` is
   flat and surjective. Finally `T` and `S` are of finite type over the
   field `k`, so `f` is of finite type over a noetherian base and hence
   locally of finite presentation.

The finiteness and centrality of `f` obtained in step 3 are not part of
the Lean conclusion, as explained above. They are used here only to apply
Conrad's criterion.

**Sources not used.** Borel and Tits, *Groupes réductifs* (1965),
Proposition 4.25, assumes a separable isogeny. It is not substituted for
the 1972 theorem, which covers inseparable central isogenies in arbitrary
characteristic. The 1972 §1.2, printed pp.253–254 (PDF pp.2–3), replaces
the erroneous example 4.26 of the 1965 article. Its isogeny of characteristic-2
groups of different `k`-ranks is neither separable nor central. The 1972
§5 corrections to the 1965 article do not concern Théorème (2.20). No
project errata note for Conrad's notes was found.

## Provenance

The Lean text is the exact text in the objective of task
`b579100c-ad44-4b9f-a8d7-72cf0c7cd31d`. Workers 1463 and 1469 wrote it for
the consumer task `68b5794b-3764-4cb2-b769-c1fc3ddf5bc2`, whose target
is the published
[`SimplyConnected.SplitTorusStatement`](../SimplyConnected/SplitTorusStatement.md).
That consumer module and every module it imports are unchanged. The
contract's source notes on Borel–Tits and Conrad were checked against the
retained PDFs at the locations cited above. A related Library statement,
[`Rational.CentralSurjectionMaximalSplitTorusImageStatement`](CentralSurjectionMaximalSplitTorusImageStatement.md),
states maximality of a supplied split image under a central fppf
surjection. It does not construct a lift of a supplied target torus, and
this module does not import it. Proving the proposition declared here is a
separate successor obligation.
