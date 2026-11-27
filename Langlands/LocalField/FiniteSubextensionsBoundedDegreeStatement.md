# Finitely many subextensions of bounded degree of a local field

`Langlands.LocalField.FiniteSubextensionsBoundedDegreeStatement` is the
proposition that, for every characteristic-zero nonarchimedean local field
\(F\) and every natural number \(d\), only finitely many subfields
\(E\) of the algebraic closure \(\overline F\) that contain \(F\) have finite
degree \([E:F]\le d\). The declaration is a `Prop`-valued definition. This
module states the proposition and does not prove it.

## The Lean statement

```lean
def FiniteSubextensionsBoundedDegreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (d : ℕ),
    {E : IntermediateField F (AlgebraicClosure F) |
      FiniteDimensional F E ∧ Module.finrank F E ≤ d}.Finite
```

The field `F : Type u` and all of its structure are quantified inside the
proposition, so the definition has a single universe parameter `u`.

- **Local field.** `IsNonarchimedeanLocalField F` is Mathlib's class from
  `Mathlib.NumberTheory.LocalField.Basic`: the topology of `F` is the
  valuative topology of the valuation class recorded by `ValuativeRel F`, `F`
  is locally compact, and the valuation is nontrivial. Mathlib derives from it
  that the valuation is discrete and the residue field is finite. Together
  with `CharZero F`, these are the finite extensions of the fields
  \(\mathbb Q_p\). The module `Langlands.LocalField.CharZeroPadicRealization`
  realizes such an `F` as a finite extension of `ℚ_[p]`, with \(p\) the
  residue characteristic, through `Langlands.CharZeroLocalField.padicField`
  and `Langlands.CharZeroLocalField.topologicalData`. The statement does not
  use that realization.
- **Actual subfields of the algebraic closure.** `AlgebraicClosure F` is
  Mathlib's construction of an algebraic closure. An element of
  `IntermediateField F (AlgebraicClosure F)` is a subfield of
  `AlgebraicClosure F` containing the image of `F`. It is a subfield, not an
  isomorphism class of extensions: two distinct conjugate subfields are
  counted separately. Any \(F\)-isomorphism between two algebraic closures
  maps the intermediate fields of one bijectively onto those of the other and
  preserves degrees. So the truth of the proposition does not depend on which
  algebraic closure is used.
- **Degree.** `Module.finrank F E` is the dimension of `E` as an `F`-vector
  space, which is the degree \([E:F]\) when that dimension is finite. Mathlib
  sets `Module.finrank` to `0` for infinite-dimensional spaces. Every
  intermediate field of \(\overline F/F\) is algebraic over \(F\), but some,
  such as the maximal unramified extension, are infinite-dimensional. Without
  the explicit `FiniteDimensional F E` they would satisfy
  `Module.finrank F E ≤ d` and the proposition would be false. With it, the
  condition says exactly that \(E/F\) is finite of degree at most \(d\). For
  \(d = 0\) the set is empty, because a field has positive dimension.
- **Finiteness.** `Set.Finite` is finiteness of the set of intermediate fields
  itself.

The topology and the valuation enter only through the hypothesis
`IsNonarchimedeanLocalField F`; the set whose finiteness is asserted is
defined purely algebraically.

## Source and derivation

The proposition is derived from results in Jean-Pierre Serre, *Local
Fields*, translated by Marvin Jay Greenberg, Graduate Texts in Mathematics
67, Springer, 1979. Serre does not state this finiteness as a numbered
result. It follows from the cited results in the following way.

1. **Unramified part.** Let \(E/F\) be finite of degree \(n\le d\). By
   Chapter III, §5, Corollary 3 to Theorem 3 (printed p. 55), \(E/F\) has a
   maximal unramified subextension \(E_0/F\), and \(E/E_0\) is totally
   ramified. Here the residue fields are finite, hence perfect. The residue
   degree of \(E_0/F\) is at most \(d\). By Chapter III, §5, Theorems 2 and 3
   (printed p. 54), an unramified extension is determined up to isomorphism
   by its residue extension. A finite field has, up to isomorphism, exactly
   one extension of each degree. So there are only finitely many
   possibilities for \(E_0\) up to \(F\)-isomorphism.
2. **Totally ramified part.** By Chapter I, §6, Proposition 18 (printed
   pp. 19–20), if \(E/E_0\) is totally ramified of degree \(e\), then the
   characteristic polynomial of a uniformizer of \(E\) over \(E_0\) is an
   Eisenstein polynomial of degree \(e\). By Proposition 17 and its
   corollary (printed p. 19), every Eisenstein polynomial is irreducible and
   defines a totally ramified extension. So \(E \cong E_0[X]/(f)\) for a
   monic Eisenstein polynomial \(f\) of degree \(e\) over \(E_0\).
3. **Compactness and Krasner's lemma.** The monic Eisenstein polynomials of
   degree \(e\) over \(E_0\) form a compact space of coefficients: the
   nonleading nonconstant coefficients range over the compact maximal ideal
   \(\mathfrak m\), and the constant coefficient ranges over the compact set
   \(\mathfrak m\setminus\mathfrak m^2\). In characteristic zero every
   irreducible polynomial is separable. Chapter II, §2, Exercises 1 and 2
   (printed p. 30) state Krasner's lemma and its consequence: every
   polynomial close enough to a separable irreducible polynomial \(f\) is
   irreducible and defines an extension isomorphic to the one defined by
   \(f\). These neighbourhoods cover the compact space. A finite subcover
   shows that there are only finitely many totally ramified extensions of
   \(E_0\) of degree \(e\), up to \(E_0\)-isomorphism.
4. **From isomorphism classes to subfields.** Steps 1–3 give finitely many
   isomorphism classes of extensions of \(F\) of degree at most \(d\). An
   extension \(E\) of degree \(n\) has at most \(n\) \(F\)-embeddings into
   \(\overline F\), and every intermediate field is the image of its own
   inclusion. So each isomorphism class contributes at most finitely many
   intermediate fields, and the set in the statement is finite.

The characteristic-zero hypothesis is used in step 3, for the separability of
Eisenstein polynomials. The conclusion fails in positive characteristic.
Over \(F=\mathbb F_p((t))\), the Artin–Schreier polynomials
\(X^p-X-t^{-m}\), for integers \(m\ge 1\) prime to \(p\), define infinitely
many pairwise non-isomorphic separable extensions of degree \(p\), since
their ramification breaks \(m\) differ. This module does not formalize that
remark.

A finite set of subfields of the algebraic closure contains a representative
of every isomorphism class of extensions of degree at most \(d\). This is
because every finite extension of \(F\) embeds into \(\overline F\) over
\(F\). The statement can therefore be used directly to choose
representatives of the isomorphism classes.

## Use

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, §V.2.1 (printed p. 104), asserts that, when \(F\)
has characteristic zero, a connected reductive group over \(F\) has only
finitely many conjugacy classes of maximal \(F\)-tori under its group of
\(F\)-points. For \(\mathrm{GL}_N\), maximal \(F\)-tori are described by
étale \(F\)-algebras of dimension \(N\), that is, by finite products of
finite field extensions whose degrees add up to \(N\). The finiteness of
extensions of degree at most \(N\) is the arithmetic input of that case.

For a proof, Mathlib supplies Krasner's lemma through the class `IsKrasner`
in `Mathlib.Analysis.Normed.Field.Krasner`, and the realization above gives
the comparison of `F` with a finite extension of `ℚ_[p]`.
