# Ampleness from one affine section open on an abelian variety

Author: Worker 171.

Module `Langlands.AbelianScheme.AffineSectionAmple`. All declarations are in the
namespace `Langlands.AbelianScheme.AffineSectionAmple`.

## Main theorem

`isAmple_of_isAffineOpen_sectionOpen` states the following. Let `K : Type u` be any
field, `A : AbelianScheme (Spec (CommRingCat.of K))` an actual Library abelian scheme,
and `L : LineBundle A.X.left`. Suppose that for some `n ≥ 1` there is a section
`s : L.powSections n` whose generation open `L.sectionOpen s` is nonempty and affine.
Then `L.IsAmple`.

There is no hypothesis on the characteristic, perfection or algebraic closedness of
`K`, on the dimension of `A`, or on symmetry of `L`.

## Proof as implemented

1. The imported `CommonAffine.translationIso` from `GroupScheme.TranslationLaws` packages left translation by a section as an automorphism of
   `G.X` (inverse: translation by the inverse section); the instance makes every
   `(translation G s).left` an isomorphism of schemes. `CommonAffine.section_comp_translation`
   and `CommonAffine.translation_apply_section` compute translations on rational points and use
   commutativity to swap the roles of two rational points.
2. `exists_square_section` (any field). For a rational point `a`, the published
   theorem of the square `Langlands.GroupScheme.fieldTheoremOfTheSquare`, applied to
   the line bundle `L ^ n` and the points `a`, `a⁻¹`, gives
   `t_a^*(L^n) ⊗ t_{a⁻¹}^*(L^n) ≅ t_1^*(L^n) ⊗ L^n ≅ L^n ⊗ L^n`, and
   `tensorPowAddIso` identifies the last bundle with `L ^ (n + n)`. Transporting the
   tensor product of the two pulled-back sections gives a section of `L ^ (n + n)`
   whose generation open is `t_a⁻¹(L.sectionOpen s) ⊓ t_{a⁻¹}⁻¹(L.sectionOpen s)`.
   The generation-open computations use the published
   `tensorSectionGenerationLocus`, `lineBundlePullbackSectionOpen` and
   `trivializationOpen_mapIso`.
3. `isAmple_of_isAlgClosed` (algebraically closed `K`). The total space is
   irreducible (`SeparatingLineBundle.irreducibleSpace_of_smooth_of_isProper`),
   quasi-compact, Jacobson and separated. For a closed point `z`, view it as a
   rational point `z'`. The opens `t_{z'}⁻¹(U)` and `ι⁻¹ t_{z'}⁻¹(U)`, where
   `U = L.sectionOpen s` and `ι` is inversion, are nonempty, so
   `SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen` gives a rational point
   `a` in both. Commutativity shows that `z` lies in the generation open of the
   section of step 2 for `a`. The union of these generation opens is open and
   contains every closed point, hence (Jacobson space) is everything. Each such
   open is an intersection of two isomorphic preimages of the affine `U` in a
   separated scheme, hence affine (`IsAffineOpen.inf`). This is the definition of
   `IsAmple` with exponent `n + n`.
4. `isAmple_of_isAffineOpen_sectionOpen` (any field). Base change to
   `AlgebraicClosure K` with `AbelianScheme.baseChange`. The projection is affine and
   surjective, so the pulled-back section (`LineBundle.pullbackPowSection`, with
   generation open the preimage by `LineBundle.sectionOpen_pullbackPowSection`) has a
   nonempty affine generation open. Step 3 gives ampleness after base change and the
   published `fieldBaseChangeAmpleReflection` descends it.

## Provenance

This is the classical translation argument of Weil as written in D. Mumford,
*Abelian Varieties*, Chapter II, §6: the theorem of the square is Corollary 4
(printed p.59), and the proof of Application 1, implication (i) ⇒ (iii) (printed
p.61), uses exactly that `T_x^*(D) + T_{-x}^*(D)` lies in `|2D|` and that for any
point `u` one can choose `x` with `u ± x` avoiding the divisor. Registered source
`mumford-abelian-varieties-chapter-ii-scan`; Worker 171 read printed pp.58–61.
The implemented statement replaces "effective divisor with finite stabilizer" by
"section of a power with affine generation open", which is what the definition of
`IsAmple` in the Library requires; the proof follows the source's translation step
and does not use the source's finiteness criterion. Raynaud's version of the same
step for group schemes over a base is Lemma 5.3 of N. Guo, *Ample sheaves on group
homogeneous spaces over Prüfer bases* (arXiv 2209.02443v1), printed p.15,
registered source `guo-ample-sheaves-prufer-2209-02443-v1`.
