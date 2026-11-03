# Affineness of a represented quotient of an affine algebraic group

`Langlands.GroupScheme.AffineGroupSchemeQuotientStatement.{u}` is a
Prop-valued statement. This module supplies no proof.

For every field `k : Type u`, it quantifies over actual group schemes `G`
and `Q` over `Spec (CommRingCat.of k)` and an actual group homomorphism
`q : G ⟶ Q`. The structure map of `G` is locally of finite type and affine;
in particular, `G` is a finite-type affine group over the field. The
structure map of `Q` is locally of finite type, quasi-compact and
separated. The underlying scheme morphism of `q` is flat, surjective and
quasi-compact. The conclusion is `IsAffineHom Q.X.hom`, so the represented
target group itself is affine over the field.

The homomorphism is an fpqc quotient in the sense of its stated scheme
properties. Surjectivity refers to the underlying scheme map; it does not
require surjectivity on the points of every original test scheme. Its
scheme-theoretic kernel is normal. The statement introduces no chosen
kernel representative or additional kernel hypothesis. There is no
smoothness, connectedness, perfectness or characteristic restriction.

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field* (2017), Proposition 5.18, printed page 103
(PDF page 119), together with the quotient universal property in
Theorem 5.13, printed page 101 (PDF page 117). Proposition 5.18 constructs
an affine quotient by any normal algebraic subgroup of an affine
algebraic group. Theorem 5.13 identifies a quotient map by its kernel,
giving the formulation for an already represented target used here.
Proposition 5.29, printed page 105 (PDF page 121), makes the same
affineness deduction for a homogeneous quotient by a normal subgroup.
The source's algebraic groups are group schemes of finite type over the
field; the explicit separated finite-type assumptions and the fpqc
scheme-map assumptions give that setting and quotient notion here.

Registered source: `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The official author errata snapshot dated 2026-11-02 was read; it contains
no correction to these three results.

This general statement is a prerequisite for the ground-field unipotent
radical quotient theorem. It asserts neither quotient existence nor
unipotent extension closure, and it does not prove the parent theorem.
