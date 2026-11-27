# The Lie algebra of a connected reductive group in characteristic zero

The module `Langlands.GroupScheme.Lie.ReductiveLieAlgebraCharZero` proves that over a field `k`
of characteristic zero the dual-number tangent Lie algebra `Additive (lieKernel G k)` of a
connected reductive group scheme `G` is reductive: its radical equals its centre.

## Main results

- `isNilpotent_toEnd_of_mem_bracket_radical` in `SemisimpleLieAlgebraCharZeroProof`: for a finite-dimensional Lie algebra `L` over a
  field of characteristic zero and a finite-dimensional representation `V`, every element of
  `⁅L, rad L⁆` acts nilpotently on `V`. The statement is reduced to an algebraic closure `K` of `k`:
  the base change of the radical is a solvable ideal of `K ⊗ L`, so the element `1 ⊗ x` lies in
  `⁅K ⊗ L, rad (K ⊗ L)⁆`, where the Library's `Langlands.Algebra.isNilpotent_toEnd_of_mem_lie_radical`
  applies; nilpotence descends along the injective map `End_k V → End_K (K ⊗ V)`.
- `radical_le_center_of_hasTrivialUnipotentRadical` in the same module: if a smooth connected affine group `G` over
  `k` has trivial unipotent radical, the radical of its Lie algebra is central. Take a closed
  embedding `ρ : G → GL_n` (`affineLinearEmbeddingStatement`) and its tangent representation
  `dρ`. The image `A` of the ideal `⁅L, rad L⁆` consists of nilpotent endomorphisms and is
  normalized by the tangent matrices of `G`, so `MatrixRepresentation.eq_one_of_nilpotent_normalized`
  shows that every element of `⁅L, rad L⁆` is trivial; hence each element of the radical commutes
  with everything.
- `hasCentralRadical_of_isConnectedReductive`: **for a connected reductive group `G` over a field
  of characteristic zero, `HasCentralRadical k (Additive (lieKernel G k))`**, for the bracket
  `instAffineKernelLieRing (R := CommRingCat.of k) (A := k) G`. This is the previous result
  together with the reverse inclusion `centre ≤ radical`, which holds in every Lie algebra.

## Sources

The argument is the classical one showing that the Lie algebra of a reductive group in
characteristic zero is reductive (A. Borel, *Linear Algebraic Groups*, 2nd ed., §I.3 and §IV.14;
N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §5 for the nilpotence of `⁅L, rad L⁆` in
representations).
