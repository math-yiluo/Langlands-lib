# Proof of the real generic unitary classification on irreducible standard modules

Module `Langlands.Representation.Archimedean.RealGenericStandardUnitaryClassificationProof`.

## Statement

`Langlands.Archimedean.realGenericStandardUnitaryClassification` proves the Library proposition
`RealGenericStandardUnitaryClassificationStatement` (module
`RealGenericStandardUnitaryClassificationStatement`). For every `n` and every list `ds` of real
blocks with `realRank ds = n` whose `O(n)`-finite standard module (`realStandardRep n ds`,
`realStandardLie n ds`) is irreducible and infinitesimally unitary, there is a list `es` with
`IsRealGenericUnitaryInducingData es`, a concatenation of singleton unitary
square-integrable-modulo-center blocks and complementary pairs
`[realBlockTwist α δ, realBlockTwist (-α) δ]` with `0 < α < 1/2`, such that `es` is a standard
parameter of that module (`HasRealStandardParameter`: `realRank es = n` and an injective compact
and Lie intertwiner from the standard module of `es`). The empty list in rank zero is included.

## Proof

The Library theorem `realGenericStandardUnitaryClassification_of_generic` (module
`RealGenericStandardUnitaryClassificationOfGeneric`) proves the same conclusion under the
additional premise `IsRealGenericGKModule n (realStandardLie n ds)`. That premise holds for every
real standard module by `isRealGeneric_realStandardLie` (module `RealStandardGenericProof`), with
no use of irreducibility or unitarity. The proof applies the first theorem with the genericity
supplied by the second.

The genericity proof runs as follows (details in `RealStandardGenericProof.md`,
`RealCharacterStandardGeneric.md` and `RealTailKernelGrowth.md`).

1. A list of real characters gives a generic standard module: evaluation at the identity of the
   Library's continued Jacquet coefficient `canonicalJacquetMap` is a nonzero Whittaker
   functional.
2. An induction block of weight `0` has the standard module of its two characters.
3. For an induction block of weight `m ≠ 0`, the Library's ascending tail map from the standard
   module with the block replaced by two characters is surjective. Its kernel consists of
   functions polynomial of degree `< |m|` along the lower root group of the block, so the
   operators of degree `≤ k` of `U(𝔤)` restricted to the kernel span a space of dimension
   `O((k + 1)^(n (n - 1) - 1))`. A Whittaker functional that did not vanish on the kernel would
   make the kernel maximally faithful by Kostant's theorem, and that dimension would be at least
   `c (k + 1)^(n (n - 1))` with `c > 0`. Hence a Whittaker functional on the source vanishes on
   the kernel and descends to the target.

Induction on the blocks then gives genericity of every real standard module.

## Provenance

The proposition is the specialization of Badulescu–Renard, *Unitary dual of GL(n) at
archimedean places and global Jacquet–Langlands correspondence* (2010), Theorems 8.1 and 8.2,
p. 1131 (PDF p. 18, `badulescu-renard-2010-unitary-dual`), described in
`RealGenericStandardUnitaryClassificationStatement.md`. In the source, genericity of an
irreducible standard module is the converse half of Theorem 8.1 together with the paragraph after
it (all discrete series of `GL(n, ℝ)` are generic). Here it is supplied by
`isRealGeneric_realStandardLie`, whose proof uses Jacquet, *Archimedean Rankin–Selberg Integrals*
(2009), §7.2, p. 47 of the author-posted version (`jacquet-2009-archimedean-rankin-selberg`), and
Kostant, *On Whittaker vectors and representation theory*, Invent. Math. 48 (1978),
Theorem 3.9, p. 142 (PDF p. 42), through the Library's implementations. The classification of
generic unitary standard modules is the Library's
`realGenericStandardUnitaryClassification_of_generic`, whose Markdown gives its route and sources.
