# Proper quotients of reductive group schemes by parabolic subgroups: statement

Author: Worker 1654.

`Langlands.GroupScheme.RelativeParabolicQuotient.ExistenceStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it. Its proof is a
separate obligation.

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`;
- every pair of actual group schemes `G P : GroupScheme (Spec (CommRingCat.of R))`;
- every group-scheme homomorphism `i : P ⟶ G`.

It has four hypotheses:

1. `IsReductive G`, the Library's predicate for reductive group schemes over a base scheme
   (`Langlands.GroupScheme.Reductive.Basic`). It requires `G` to be smooth and affine over
   `Spec R`. Its geometric fibre at every point `s`, taken over the chosen algebraic closure
   of the residue field, must satisfy `IsPseudoReductive`. Over an algebraically closed
   field that means smooth, connected and affine with trivial unipotent radical, so the
   geometric fibres are connected reductive groups.
2. `Smooth P.X.hom`: the subgroup is smooth over `Spec R`.
3. `IsClosedImmersion i.hom.hom.left`: the underlying scheme morphism of `i` is a closed
   immersion.
4. For every field `k : Type u` and every ring homomorphism `R → k` (an instance
   `Algebra R k`), the base change of `i` along `Spec.algebraMap R k` satisfies the existing
   `IsParabolicSubgroup` predicate (`Langlands.GroupScheme.Absolute.Borel`). That predicate
   asks for a smooth closed subgroup that contains a Borel subgroup after base change to
   `AlgebraicClosure k`, through an actual factorization.

The conclusion asserts the existence of an actual relative scheme
`Q : Over (Spec (CommRingCat.of R))` and a morphism `q : G.X ⟶ Q` over `Spec R` with:

- `IsProper Q.hom`: the structure morphism of `Q` is proper (Mathlib's `IsProper`);
- `Flat q.left`, `Surjective q.left` and `QuasiCompact q.left` for the underlying scheme
  morphism of `q`;
- the exact coset criterion on every test object: for every
  `T : Over (Spec (CommRingCat.of R))` and all points `g h : T ⟶ G.X`,

  ```lean
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T
  ```

Here `g⁻¹ * h` is the group law on `T`-points of `G`. `SubgroupFunctor.range i` assigns
to `T` the points `y ≫ i.hom.hom` with `y : T ⟶ P.X`. So the fibres of `q` are the right
cosets `gP`. The tests `T` are arbitrary schemes over `Spec R`, not only affine, reduced,
field-valued or `R`-valued ones.

## Source

The source is Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes*
I, Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, with retained file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). The page numbers
below are one-based PDF pages; they agree with the printed page numbers of this file.

- Definition 3.1.1 (p. 81): a reductive `S`-group is a smooth `S`-affine group scheme whose
  geometric fibres are connected reductive groups.
- Definition 5.2.1 (p. 151): a parabolic subgroup of a reductive `G → S` is a smooth
  `S`-affine `S`-group `P` with a monic homomorphism `P → G` such that `P_s` is parabolic in
  `G_s` (that is, `G_s/P_s` is proper) for all `s ∈ S`.
- Proposition 5.2.3 (p. 152): such a homomorphism `P → G` is a closed immersion.
- Corollary 5.2.8 (pp. 155–156): for any parabolic subgroup `P` of a reductive group scheme
  `G`, the normalizer of `P` is `P`, and the étale quotient sheaf `G/P` is represented by a
  smooth proper `S`-scheme with a canonical `S`-ample line bundle. Its proof applies
  Theorem 2.3.6 to the self-normalizing `P`.
- Theorem 2.3.6 (p. 72) and the first lines of its proof (p. 73): the quotient sheaf `G/H`
  is represented by a smooth `S`-scheme, and, since `H` is smooth, `G → G/H` admits sections
  étale-locally on `G/H`.

Getz and Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations` (SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), cite exactly
[Con14, Corollary 5.2.8] for the scheme `G/P` (printed p. 543, PDF p. 548). They use its
properness over `O_{F_v}` in the proof of Theorem B.2.5 (printed p. 544, PDF p. 549).
The registered errata `getz-hahn-2024-errata-2026-10` (SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`, all five pages) do not
amend these passages. No errata for Conrad's notes are registered, and the registered
snapshot of Conrad's author page lists none for them.

## Derivation from the source

The Lean proposition is a derived consequence of Corollary 5.2.8 and Theorem 2.3.6 for the
affine base `S = Spec R`. It is not a verbatim numbered assertion.

**The hypotheses imply the source's hypotheses.** Hypothesis 1 is Definition 3.1.1.
Hypotheses 2 and 3 make `P` smooth, `S`-affine (closed in the affine `G`) and monic in `G`.
For a point `s` with residue field `κ(s)`, hypothesis 4 at `k = κ(s)` says that `P_s`
contains a Borel subgroup after base change to an algebraic closure. Over a field this is
equivalent to properness of `G_s/P_s`. Properness can be checked after the faithfully flat
extension to the algebraic closure, where Conrad's discussion after Theorem 1.1.8 (p. 9)
identifies parabolic subgroups with closed subgroups containing a Borel subgroup. The same
comparison of parabolicity notions is explained in the published
`Langlands/GroupScheme/Rational/ParabolicNormalizerStatement.md`. Hypothesis 4 tests every
field-valued point, not only residue fields, and hypothesis 3 is a conclusion of
Proposition 5.2.3 in the source. So both are stronger than the source's hypotheses, and
the proposition is weaker than the source result.

**The conclusions follow.** Take `Q = G/P` from Corollary 5.2.8 and `q` the quotient map.

- `Q` is proper over `Spec R` by Corollary 5.2.8.
- Over an étale cover `U → Q` on which `q` has a section, `G ×_Q U ≅ P ×_{Spec R} U` over
  `U`. So `q` is étale-locally on its target the base change of the smooth affine morphism
  `P → Spec R`. Hence `q` is smooth, so flat, and it is affine, so quasi-compact; both
  properties descend along the étale cover. It is surjective because `q` has sections
  étale-locally.
- If `g⁻¹h` factors through `P`, then `g` and `h` have the same image in the quotient sheaf.
  Conversely, if they have the same image in the sheaf quotient, then `g⁻¹h` factors through
  `P` on an étale cover of `T`. Since `P` is closed in `G`, the preimage of `P` under
  `g⁻¹h` is a closed subscheme of `T` whose pullback to the cover is everything. Faithful
  flatness forces it to be all of `T`. This gives the all-test criterion, including for
  non-affine and nonreduced `T`.

Smoothness of `Q`, the ample line bundle, the self-normalizer property and the moduli
description of `G/P` are true in the source but are not part of this proposition.

## Scope

All objects are in universe `u`; the field tests are in `Type u`. The ring `R` is
arbitrary: it need not be Noetherian, local, a domain or of positive dimension. The empty
scheme (`R = 0`), fields, and the improper case `P = G` are included. No split maximal
torus, cocharacter presentation, Levi decomposition, Borel subgroup over `R`, or
connectedness of `Spec R` is assumed. No properness certificate, quotient or local section
is supplied as a hypothesis.

## Intended consumer

The hypotheses are exactly those supplied by the fields `reductive`, `parabolicSmooth`,
`closedImmersion` and `fieldParabolic` of the published
`Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading.ModelData`, applied to
`ambient.group`, `parabolic.group` and `inclusion.hom`. The conclusions are exactly the
quotient premises of the published
`Langlands.GroupScheme.IntegralParabolicCovering.range_mul_integralPoints_eq_univ`: `IsProper
Q.hom`, the flat, surjective and quasi-compact instances on `q.left`, and the all-test
criterion `hfib`. With a monomorphism from the closed immersion, smoothness and connected
special fibre, that theorem gives the parabolic-left covering `G(K) = P(K) · M(R)` over a
complete valuation ring `R` with finite residue field. This feeds the local covering clause
of `Langlands.Global.IntegralIwasawaFamily.ExistenceStatement`.
