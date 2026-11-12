# Statement: unipotent fibres of dynamic unipotent subgroups over a ring

Worker 3483.

`Langlands.GroupScheme.DynamicRingUnipotentFibresStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it
adds no other definitions, theorems or axioms. It imports
[`Dynamic.Basic`](Basic.md) (for `Dynamic.unipotent` and
`SubgroupFunctor.IsRepresentedBy`), [`Reductive.Basic`](../Reductive/Basic.md)
(for `IsUnipotent`) and Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(for `LocallyOfFiniteType`).

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`;
- every group scheme `G : GroupScheme (Spec (CommRingCat.of R))` whose structure
  morphism `G.X.hom` is `IsAffineHom` and `LocallyOfFiniteType` (instance arguments);
- every cocharacter `χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G`;
- every group scheme `H` over `Spec R` and every homomorphism `j : H ⟶ G` with
  `(Dynamic.unipotent χ).IsRepresentedBy j`;
- every field `K : Type u` and every morphism `y : Spec K ⟶ Spec R`.

It concludes `IsUnipotent ((GroupScheme.baseChange y).obj H)`: the group scheme
`H ×_{Spec R} Spec K` over `Spec K` is unipotent.

- `Dynamic.unipotent χ` is the subgroup functor of points `g` of `G` for which the
  orbit map `t ↦ χ(t) g χ(t)⁻¹` extends over the affine line with value `1` at `0`
  ([`Dynamic.Basic`](Basic.md)); this is Conrad's and CGP's `U_G(λ)` for the conjugation
  action.
- `F.IsRepresentedBy j` says that `j` is a monomorphism of the underlying schemes over
  `Spec R` and that its range subgroup functor is `F`
  ([`SubgroupFunctor`](../SubgroupFunctor.md)). Nothing asserts that such an `H`
  exists, and the representative is arbitrary.
- `IsUnipotent` ([`Reductive.Basic`](../Reductive/Basic.md)) is defined for group
  schemes over a field: every nonzero finite-dimensional matrix representation has a
  nonzero fixed vector.
- `GroupScheme.baseChange y` is the base change of group schemes along `y`.

The trivial cocharacter is included. No smoothness, flatness or finite presentation of
`G` is assumed.

## Source

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*, second edition,
Cambridge University Press, 2015; registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, file
`Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`
(SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`).

- Setting, printed p.49 (PDF p.75): "Let V = G be an affine group scheme over a ring k
  and let λ : GL1 → G be a k-group homomorphism. Endow G with a GL1-action via
  t.g = λ(t)gλ(t)⁻¹."
- Lemma 2.1.5, printed p.50 (PDF p.76): the functor `R ↝ {g ∈ G(R) | lim_{t→0} t.g = 1}`
  "is represented by a closed normal k-subgroup scheme U_G(λ) ⊆ P_G(λ), and if G is of
  finite type over k then U_G(λ) has unipotent fibers over Spec k. The formation of
  U_G(λ) commutes with any extension of the base ring".
- Proof of Lemma 2.1.5, printed p.51 (PDF p.77): "To check unipotence of the fibers of
  U_G(λ) over Spec k when G is of finite type, we may assume k is a field."

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014; registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
one-based PDF pages, which agree with the printed page numbers of this file.

- Theorem 4.1.7(4), last sentence (p.113): "Also, the fibers of U_G(λ) → S are
  unipotent." Part 4 begins "Assume G is smooth", and the theorem is stated for a
  finitely presented affine group over a ring.
- Proof of Theorem 4.1.7 (p.114): "The fibral unipotence for U_G(λ) in (4) is part of
  [CGP, Lemma 2.1.5] (which does not require smoothness of G, once one has developed a
  good theory of unipotent group schemes over a field; see [SGA3, XVII, 1.3, 2.1])."

## Derivation from the source

The Lean proposition is CGP Lemma 2.1.5's unipotence assertion over the ring `R`, for
affine `G` of finite type, applied to every field-valued point of `Spec R`.

- Base and action. `k = R`, and the `G_m`-action is conjugation through `χ`, which is
  CGP's setting on p.49. Representatives: `H` is isomorphic over `Spec R` to CGP's
  closed subgroup `U_G(λ)`, because both represent the same subgroup functor through
  monomorphisms.
- Finiteness. `G.X.hom` is affine and locally of finite type, so `G` is affine of finite
  type over `R`, which is CGP's hypothesis.
- Arbitrary field points. For `y : Spec K ⟶ Spec R`, CGP's base-change compatibility
  identifies `U_G(λ) ×_{Spec R} Spec K` with `U_{G_K}(λ_K)`, and `G_K` is of finite
  type over the field `K`. Lemma 2.1.5 over the base `K` then says that `U_{G_K}(λ_K)`
  is a unipotent `K`-group, which is the conclusion. Taking for `y` the residue-field
  points of `Spec R` gives CGP's "unipotent fibers over Spec k".
- Unipotence. The cited passages do not restate the definition; the Lean predicate is
  the fixed-vector definition of James S. Milne, *Algebraic Groups* (2017), registered as
  `milne-2017-algebraic-groups` (SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`): "Recall (6.45)
  that an algebraic group G is unipotent if every nonzero representation of G has a
  nonzero fixed vector" (§14b, printed p.280, PDF p.296). For algebraic groups over a
  field, Milne's Theorem 14.5 (printed p.281, PDF p.297) shows that this is equivalent to
  being isomorphic to an algebraic subgroup of `U_n`; that equivalence is not part of
  this statement. The field-case statement `DynamicUnipotentUnipotenceStatement` uses
  the same predicate.

So the proposition is no stronger than CGP's lemma. Compared with Conrad's
Theorem 4.1.7(4), it drops smoothness and finite presentation of `G`, as Conrad's
p.114 remark permits by reference to CGP.

## Scope

All objects are in universe `u`, including the test fields `K`. The ring `R` is
arbitrary: it need not be Noetherian, local or a domain. Not stated here: the same
assertion over a non-affine base, for abstract `G_m`-actions, or for `P_G(λ)` and
`Z_G(λ)` (which are not unipotent in general). The existence of a representative is
not part of the statement.

## Relation to the Library

- `DynamicUnipotentUnipotenceStatement`
  ([`UnipotentUnipotenceStatement`](UnipotentUnipotenceStatement.md)) is the case of a
  base field `k` and the trivial field point. It is proved in the Library by
  `dynamicUnipotentUnipotence`
  ([`UnipotentUnipotenceProof`](UnipotentUnipotenceProof.md)).
- `Dynamic.unipotent_baseChange` ([`Dynamic.BaseChange`](BaseChange.md)) records the
  base-change compatibility of `Dynamic.unipotent`, and
  `SubgroupFunctor.IsRepresentedBy.baseChange`
  ([`SubgroupBaseChange`](../SubgroupBaseChange.md)) transports representatives.

This module proves none of these relations.
