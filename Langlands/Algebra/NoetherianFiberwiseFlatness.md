# Proof of the Noetherian local fibrewise flatness criterion

`Langlands.Algebra.noetherianFiberwiseFlatness.{u,v,w,z}` proves exactly
`Langlands.Algebra.NoetherianFiberwiseFlatnessStatement.{u,v,w,z}`.
For local homomorphisms \(R\to S\to S'\) of commutative Noetherian local
rings and a nonzero finite \(S'\)-module \(M\) with the specified compatible
actions, \(R\)-flatness of \(M\) and flatness of
\((S\otimes_R k(R))\otimes_S M\) over \(S\otimes_R k(R)\) imply
\(R\)-flatness of \(S\) and \(S\)-flatness of \(M\).
The four universes remain independent. There are no finiteness
hypotheses on \(M\) over \(R\) or \(S\), or finite-type or
finite-presentation hypotheses on the ring maps.

The original mathematical source is the Stacks Project, Lemma 10.99.15
([tag 00MP](https://stacks.math.columbia.edu/tag/00MP)), in the registered
snapshot `stacks-algebra-flatness-criteria-2026-10-22`, file `00MP.html`,
folder SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The original proof and its comments were read in full. In particular, M is
finite over S', with no finiteness assumption over R or S.

The implementation uses the source's ideal-tensor reduction and Nakayama
argument, followed by a general faithful-flatness argument.

1. For any ideal I of R, tensor cancellation identifies tensoring
   `I.subtype.baseChange S` with M over S with tensoring the inclusion of I
   with M over R. The latter is injective by R-flatness of M.
2. Write J for the extension of I to S. The S-linear multiplication map
   `S ⊗[R] I → S` has range J, by the standard ideal-tensor range formula.
   Restricting its codomain gives a surjection to J, which remains surjective
   after tensoring with M. The composite with the tensor inclusion of J is
   injective by the first step and the tensor unit equivalence. Surjectivity
   then gives injectivity for J itself. Commutativity exchanges the left
   and right tensor conventions.
3. Mathlib's S-algebra equivalence
   `S/J ≃ₐ[S] S ⊗[R] (R/I)` transports fibre flatness to the canonical
   `(S/J) ⊗[S] M`. The proof installs the algebra structure induced by this
   equivalence, checks its tower with S, restricts flatness across the
   equivalence, and tensors the resulting linear equivalence with M.
   Thus the actual fibre module and its action are retained.
4. Specialize I to the maximal ideal of R. Locality places J inside the
   maximal ideal of S, so J is proper. The published theorem
   `Langlands.Algebra.idealLocalFlatnessCriterion`, imported from
   `Langlands.Algebra.IdealLocalFlatnessCriterion`, applied to S → S'
   and J, now gives S-flatness of M.
5. To prove faithful flatness over S, suppose its maximal ideal generates M.
   Restricting scalars shows that its extension to S' also generates M.
   That extension lies in the maximal ideal of S'. Nakayama for the finite
   S'-module M contradicts the assumption that M is nonzero.
6. Finally, test R-flatness of S against every ideal of R. After tensoring
   the base-changed ideal inclusion with M, the first step gives
   injectivity. Faithful flatness over S reflects this injectivity. The
   ideal-tensor criterion proves R-flatness of S.

The last step is an internal derived argument from Mathlib's
ideal-tensor flatness criterion and faithful-flatness detection of
injectivity. It replaces the source's final application of the
Noetherian local criterion. Worker 426 implemented these tensor,
Nakayama and faithful-flatness arguments using the source and Mathlib.
The imported ideal local criterion has its own proof and provenance.

The theorem has the complete named proposition as its type, with no
additional criterion as an argument. An unapplied assignment at the
end of the Lean module also checks it at the four independent universes.
The published statement and all of its imported files are unchanged.
All helper lemmas in this module are private.

A development Lake build and complete unapplied declaration inspection
succeeded without errors or warnings in the project environment. The theorem
has universe parameters `u`, `v`, `w`, `z` and uses only `propext`,
`Classical.choice`, and `Quot.sound`. Independent exact-target validation,
semantic review and Library publication are subsequent TaskHub steps.
