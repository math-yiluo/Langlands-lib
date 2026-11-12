# Positive multiplication isogeny over arbitrary fields

Author: Worker 399.

`Langlands.GroupScheme.fieldMultiplicationIsogeny` proves the entire published
proposition `Langlands.GroupScheme.FieldMultiplicationIsogenyStatement.{u}`.
For every field `K : Type u` and actual commutative group object
`G : Grp (Over (Spec (CommRingCat.of K)))`, smoothness, properness and
geometric connectedness of `G.X.hom` imply
`IsIsogeny (multiplication G (n : ℤ))` for every natural number `n > 0`.
The theorem has no additional outer premise.

## Implemented proof

Fix exactly the data and hypotheses quantified by the target. Apply the
published unconditional theorem `fieldSymmetricAmpleExistence` to obtain an
actual `L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left`,
its ampleness, and an actual module-sheaf isomorphism witnessing symmetry
under pullback by multiplication by `-1`. That theorem obtains ample
existence over the arbitrary field and constructs a symmetric ample bundle;
neither property is assumed here.

Apply the published `fieldSymmetricMultiplicationPullback` to this same
line bundle, its symmetry and the given positive natural number. Its
conclusion is `Nonempty` of the actual isomorphism

```text
(Scheme.Modules.pullback
  (multiplication G (n : ℤ)).hom.hom.left).obj L.obj
    ≅ Langlands.Scheme.Modules.tensorPow L.obj (n * n).
```

This is exactly the formula required by
`fieldAmpleMultiplicationKernel`. Apply that published theorem to `L`,
its ampleness, `n`, its positivity and the formula. It proves
`IsFinite (kernel (multiplication G (n : ℤ))).X.hom`, finiteness of the
structure morphism of the whole scheme-theoretic kernel.

The imported kernel proof first obtains ampleness of the multiplication
pullback from the positive tensor-power formula. Its restriction to the
closed kernel is ample and is trivial: the kernel square factors the
restricted multiplication through the identity section, and an actual line
bundle over a field is trivial. Properness and the published ample-trivial
finiteness criterion then give the asserted finiteness.

Finally apply the published `fieldFiniteKernelIsogeny` to the actual
endomorphism `multiplication G (n : ℤ)`, the original three structure
hypotheses and this finite-kernel result. That theorem proves finiteness
using properness and local quasi-finiteness, then proves surjectivity and
flatness using its established geometric inputs. Its conclusion is precisely
`IsIsogeny` of the given multiplication morphism: finiteness, flatness and
surjectivity of its underlying scheme morphism.

The four inputs are imported by their current Library module and Lean
declaration names. This module is only their final composition; it assumes
no unproved geometric, tensor, descent or Picard comparison. The published
target pair and all its imports are unchanged.

## Source correspondence and scope

The proof implements the isogeny part of J. S. Milne, *Abelian Varieties*,
the 1986 article in the author's corrected version of January 2, 2022,
Theorem 8.2, printed and one-based PDF p.13. Its first proof paragraph uses
the symmetric ample bundle of Corollary 7.2, p.12, the symmetric
multiplication formula of Corollary 6.6, and the ample and trivial restriction
to the kernel. Here the imported kernel theorem concludes finiteness directly
from properness and an ample trivial bundle, in place of the source's
dimension-zero intermediate step. The final imported theorem supplies the
endomorphism case of Proposition 8.1, p.12, in the finite-flat-surjective
convention used by `IsIsogeny`. Section 20, p.42, supplies the smooth proper
group-scheme presentation with connected geometric fibres; the target's
[companion](FieldMultiplicationIsogenyStatement.md) explains that
correspondence.

This is an internal assembly by Worker 399 of independently published
prerequisite proofs. Their paired companions describe their constructions
and authorship. The registered original source is
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
retained at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
The p.12–13 passages and retained author errata were read directly. The errata
directs readers to the corrected version and does not change this isogeny
argument.

The universe, field and positive natural multiplier are arbitrary.
Characteristic dividing `n`, imperfect fields, dimension zero and possibly
nonreduced kernels remain in scope. Projectivity, an existing ample bundle,
algebraic closure, perfectness and dimension are not extra hypotheses.
The conclusion is exactly the finite-flat-surjective isogeny assertion;
degree and etaleness are outside this proposition. Arbitrary bases and
negative integer multiplication belong to the separate
`MultiplicationIsogenyStatement`.
