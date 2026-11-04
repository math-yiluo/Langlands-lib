# Descending character-linear conjugation on actual quotient kernels

This internal construction works at arbitrary universe `u`. Its initial
conjugation constructions are over any base scheme `S`. Its character-linear
conclusions are over `Spec k` for an arbitrary field `k`, with a supplied
commutative group scheme `D`. Every point identity is on every relative test
scheme, including nonreduced tests.

`LinearKernelTower.normalConjugation` bundles conjugation on a supplied monic
normal subgroup `i : K → H`, using the existing normalized-conjugation morphism.
`normalConjugation_comp` gives its ambient identity `h x h⁻¹`. The full actual
kernel of any homomorphism `p : E → Q` is normalized by the whole source:
composing a conjugate with `p` gives the identity because the middle point is
in the full kernel. This supplies `kernelConjugation p` and its analogous
ambient identity `kernelConjugation_comp`.

`kernelConjugation_act_lift` compares these actions in any commuting square
`r ≫ kernelι p = i ≫ s`, where `s : H → E`, `i : K → H`, and
`r : K → kernel p`. Given any action `b` of `H` on `K` with the ambient
conjugation identity, source conjugation on `kernel p` at the images of `h`
and `x` is `b.act h x ≫ r`. The proof cancels the monic full-kernel inclusion
and uses the square and homomorphism laws. This comparison needs no flatness
or surjectivity hypotheses.

`isCharacterLinearKernel_of_conjugation` assumes a quasi-compact, flat,
surjective map `q : E → D`, a closed additive embedding
`a : kernel p → Ga`, and a character `χ` of `D`. It also assumes that `a`
intertwines source conjugation with the weight action through `q` and `χ`.
The kernel of `q` then acts trivially: cancel the monic closed additive
embedding and use the identity action at the identity of `D`. The existing
fpqc action-descent theorem constructs an actual action of `D` on `kernel p`.
Its lift law gives the required ambient conjugation identity. Its character
identity is checked after locally lifting the acting point through `q`.
Together these data establish exactly the existing
`LinearKernelTower.IsCharacterLinearKernel D q p` predicate.

`isCharacterLinearKernel_of_local_lifts` weakens the place where the
intertwining identity must be checked. In addition to the same `q`, `a`, and
`χ`, it assumes quasi-compact, flat, surjective maps `s : H → E` and
`r : K → kernel p`, the commuting square above, and an action `b` with the
ambient conjugation identity. Character intertwining need only hold at
`h : H(T)` and `x : K(T)`. The proof first lifts the acting variable through
`s`, then lifts the kernel variable through `r` on a further refinement.
Naturality and `kernelConjugation_act_lift` identify the resulting equality
with the supplied source equality. The existing local equality criterion
reflects it back to the original test. No global lift of test-scheme points
is assumed.

`TriangularLayer.QuotientTerm.isCharacterLinearKernel_of_coordinate`
specializes this to two supplied actual affine fppf quotients: `A = H/F` and
`B = H/E`, with `E ≤ F`, and a represented monic normal subgroup `i : K → H`
whose full range is `F`. The ambient `H` is affine over `k`; `K` is affine
and locally of finite type. A coordinate `c : K → Ga` has the full internal
kernel `E.comap i`. Generic `AffineHomImageStatement` remains an explicit
premise. The existing comparison-kernel embedding theorem gives a closed
`a : kernel(B → A) → Ga` with `kernelRestriction ≫ a = c`. The actual
restriction `K → kernel(B → A)` is a base change of `H → B`, so it is
quasi-compact, flat and surjective. The local-lift theorem therefore applies
with the normal conjugation action on `K`, provided the given coordinate is
character-equivariant through a supplied quasi-compact, flat, surjective
`q : B → D`. This proves character linearity of the full actual comparison
kernel, retaining all image, quotient and equivariance premises explicitly.

The provenance is internal: this is a categorical derivation from the
published actual normalized conjugation, scheme-kernel, fpqc action descent,
quotient comparison and additive embedding interfaces. It makes no external
literature attribution. It imposes no smoothness or connectedness hypothesis
on the groups or kernels and proves neither generic image/quotient existence,
the explicit matrix character formula, a finite tower, nor a splitting
section. Those remain separate obligations of the parent task.
