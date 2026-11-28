# Unitary splitting at archimedean completions

Module: `Langlands.Algebra.CentralSimple.LandherrRealSplitting`.

`UnitaryInvolutionSplitting K` (module `Langlands.Algebra.UnitaryInvolutionStatements`) says
that over every separable quadratic extension `L/K`, every central simple `L`-algebra with a
unitary involution relative to the nontrivial automorphism of `L/K` is a full matrix algebra
over `L`.

- `unitaryInvolutionSplitting_of_isAlgClosed`: if every quadratic extension of `K` is
  algebraically closed, then `K` has this property, since central simple algebras over an
  algebraically closed field are matrix algebras (`exists_matrix_chart`, module
  `Langlands.Algebra.CentralSimpleScalarExtension`, applied with the trivial extension).
- `isAlgClosed_of_quadratic_of_equiv_real`: a quadratic extension of a field isomorphic to
  `ℝ` is algebraically closed: the algebraic closure has degree two
  (`FieldTheory.finrank_algebraicClosure_of_equiv_real`, module
  `Langlands.FieldTheory.RealAlgebraicClosure`), so the embedding of the quadratic extension
  into it is an isomorphism.
- `not_isQuadratic_of_isAlgClosed`: an algebraically closed field has no quadratic extension.
- `infiniteCompletion_unitaryInvolutionSplitting`: every archimedean completion `F_w` of a
  number field has the unitary splitting property. If `w` is real, `F_w ≅ ℝ` and the second
  item applies; if `w` is complex, `F_w ≅ ℂ` is algebraically closed (roots are transported
  through the isomorphism), so it has no quadratic extension and the condition is vacuous.

## Provenance

Over `ℝ`, the only quadratic extension is `ℂ`, over which every central simple algebra
splits; over `ℂ` there is no quadratic extension. This is the archimedean case of the local
input to Landherr's theorem (Platonov and Rapinchuk, *Algebraic Groups and Number Theory*
(1994), §6.7).
