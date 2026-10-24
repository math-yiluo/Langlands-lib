# The Noetherian local fibrewise flatness criterion

`Langlands.Algebra.NoetherianFiberwiseFlatnessStatement` is the proposition
in Stacks Project Lemma 10.99.15, tag **00MP**. It states a criterion;
this module contains no proof of it.

Let \(R\to S\to S'\) be local homomorphisms of commutative Noetherian
local rings, and let \(\mathfrak m\) be the maximal ideal of \(R\).
Let \(M\) be a nonzero finite \(S'\)-module. If \(M/\mathfrak mM\)
is flat over \(S/\mathfrak mS\) and \(M\) is flat over \(R\), then
\(S\) is flat over \(R\) and \(M\) is flat over \(S\).

The Lean declaration uses `IsNoetherianRing` and `IsLocalRing` on all
three rings. The two `IsLocalHom` instances concern the given algebra
maps \(R\to S\) and \(S\to S'\). `IsScalarTower R S S'` identifies
their composite with the specified \(R\)-algebra structure on \(S'\).
The three actions on \(M\) and their scalar towers give the compatible
restricted actions. These compatibility data express the source's
module structures and do not assume flatness.

`Module.Finite S' M` is finiteness over \(S'\). The source imposes no
finiteness over \(S\) or \(R\), and neither does this declaration.
For a module, `Nontrivial M` expresses that \(M\ne0\).

Writing \(k=R/\mathfrak m\), the actual fibre ring in Lean is
\[
F=S\otimes_R\operatorname{IsLocalRing.ResidueField}(R)
  =S\otimes_R k.
\]
Its canonical \(S\)-algebra map sends \(s\) to \(s\otimes1\).
The actual fibre module is \(F\otimes_S M\), with \(F\) acting on
the first tensor factor. Quotient-tensor identifications give
\(F\simeq S/\mathfrak mS\) and
\(F\otimes_S M\simeq M/\mathfrak mM\), with their canonical actions.
In particular the antecedent `Module.Flat F (F ⊗[S] M)` is precisely
the source's fibre-flatness condition. The final antecedent and the
two conclusions use the specified \(R\)- and \(S\)-module structures.
This is the same tensor presentation used by the published
`Langlands.Algebra.LocalFiberwiseFlatnessStatement`.

There are four independent universes, for \(R,S,S'\), and \(M\).
There are no essential-finite-type or essential-finite-presentation
hypotheses on the algebra maps. This distinguishes 00MP from the
general-base criterion 00R7, whose finiteness hypotheses allow
Noetherian approximation. The imported 05UV statement supplies the
existing tensor conventions and imports; its truth is not assumed.

The source proof first applies the ideal variant of the local
criterion 00ML to \(\mathfrak mS\) and obtains \(S\)-flatness of \(M\).
Nakayama's lemma then supplies faithful flatness over \(S\), allowing
the maximal-ideal tensor-injectivity condition to descend to \(S\);
00MK gives \(R\)-flatness of \(S\). This paragraph describes the source
route, not a proof contained in this module.

The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, folder SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00MP.html`, Lemma 10.99.15, displayed statement and proof.
