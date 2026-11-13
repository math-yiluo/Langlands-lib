# Proof: dynamic unipotent subgroups have unipotent fibres over any base scheme

Worker 3483 (proof), Worker 282 (verification and submission), 13 November 2026.

`Langlands.GroupScheme.dynamicBaseUnipotentFibres.{u}` proves the exact target
`Langlands.GroupScheme.DynamicBaseUnipotentFibresStatement.{u}`, already
published in the Library. The proof specializes the published field theorem
to each field-valued point of the base scheme.

For every scheme `S`, affine locally finite-type `S`-group scheme `G`,
cocharacter `χ`, and homomorphism `j : H ⟶ G` representing the actual dynamic
unipotent subgroup functor, the base change of `H` along every field-valued
point `y : Spec K ⟶ S` is unipotent. No smoothness, flatness, finite-presentation
or Noetherian hypothesis is added.

## Implemented proof

Fix `y : Spec K ⟶ S`. The structure morphism of the base-changed group is the
pullback projection of `G → S`. `MorphismProperty.pullback_snd` gives its
affineness and local finite type.

`SubgroupFunctor.IsRepresentedBy.baseChange` transports `hj` to the
base-changed homomorphism `j_K`. The equality
`Dynamic.unipotent_baseChange` identifies its represented functor with
`Dynamic.unipotent (Dynamic.baseChangeCocharacter y χ)`. The published theorem
`dynamicUnipotentUnipotence` then gives unipotence of the actual group scheme
`H_K`.

The dynamic base-change theorem is an equality of subgroup functors on all
test schemes, including nonreduced ones. The conclusion is the existing
representation-theoretic predicate `IsUnipotent`; it is not a statement about
an abstract quotient or only the rational points.

## Sources and provenance

This is a derived proof by specialization to field-valued points, using
published Library theorems. The original sources and their detailed
correspondence are recorded in
[`BaseUnipotentFibresStatement.md`](BaseUnipotentFibresStatement.md):

- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition
  (2015), §2.1 and Lemma 2.1.5, printed pp.49–51 (PDF pp.75–77), registered
  source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
  This supplies the finite-type unipotent-fibre assertion without smoothness.
- Conrad, *Reductive group schemes* (2014), Theorem 4.1.7(4) and its proof,
  pp.113–114, and the paragraph after Example 4.1.9, p.114, registered source
  `conrad-2014-reductive-group-schemes`, SHA-256
  `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
  The latter paragraph explains arbitrary base change and extension to any
  base scheme.
- Milne, *Algebraic Groups* (2017), §14b and Theorem 14.5, printed pp.280–281
  (PDF pp.296–297), registered source `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  These passages explain the fixed-vector convention used by `IsUnipotent`.

The statement's source reading found no matching project errata note, and
the retained Milne official errata snapshot has no correction to these
passages. This proof uses the field unipotence theorem already in the Library;
it does not reimplement the field embedding argument.
