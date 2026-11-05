# Finite-type groups of multiplicative type over a field

Author: Worker 1232.

`Langlands.GroupScheme.IsMultiplicativeType G` is a proposition about an
actual group scheme over a field `k : Type u`. It asks for a field extension
`K : Type u`, a finitely generated abelian group `Λ : Type u`, and an actual
group-scheme isomorphism from `G_K` to the existing diagonalizable group
`Diagonalizable.groupScheme K Λ`.

This is the finite-type convention of Milne, *Algebraic Groups* (2017),
Definition 12.17, printed p.236 / PDF p.252, source
`milne-2017-algebraic-groups`. Milne's algebraic groups are of finite type.
Here finite generation of the full character group is explicit in the
definition; the imported `DiagonalizableGeometry` supplies the finite-type
geometry of that model. The field extension and character group use the
same universe as the existing torus predicate. No separability or Galois
condition is imposed on the splitting extension.

The abelian group `Λ` may have torsion, including characteristic-primary
torsion. There is no smoothness, reducedness or connectedness assumption on
`G`. In particular this predicate retains finite nonsmooth diagonalizable
factors. It does not replace a full group by its largest torus. The
definition itself asserts no Galois classification, quotient existence,
or property of a reductive group's center.

`IsTorus.isMultiplicativeType` uses the splitting extension in the published
torus predicate. Over that extension, an isomorphism with `G_m^I` is composed
with the inverse of `Diagonalizable.splitIso` for the free character group
`I → ℤ`. This proves the inclusion of tori in groups of multiplicative type
stated immediately after Milne's Definition 12.17.

The complete registered official 2017-book errata snapshot of
2 November 2026 was checked in the source reading for this work. Its listed
corrections do not change Definition 12.17 or the torus inclusion.
