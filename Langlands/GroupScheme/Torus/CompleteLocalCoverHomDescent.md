# Descent equivalence for homomorphisms with a prescribed special fibre

This derived construction packages
finite etale descent of actual group-scheme homomorphisms, using the included
`CompleteLocalDeformation.CoverDescent` and `HomRigidity` developments.

Let `A` be a noetherian local ring, `G,H` group schemes over `Spec A`, with
`G` affine. A local finite etale splitting cover `d` of `H` has carrier `B`.
Assume that the actual special fibre of `G_B` is diagonalizable. For every
actual special-fibre homomorphism `f₀ : H_k → G_k`,
`specialHomCoverEquiv d hG f₀` is an equivalence between global
homomorphisms whose special fibre is `f₀` and homomorphisms over `B` whose
special fibre is the canonical transport of `f₀` to the residue field of `B`.
The forward map is exactly actual base change; the accompanying simp lemma
records this without changing either Hom set.

Special-fibre naturality shows that base change preserves the prescribed
fibre. Faithfulness of pullback along the fpqc cover proves injectivity.
For surjectivity, the included descent theorem first proves agreement of the
two pullbacks over `B` tensor `B` using rigidity modulo the maximal ideal,
then applies actual fpqc Hom descent. Faithfulness of the residue-field
extension identifies the special fibre of the descended map with `f₀`.
`Equiv.ofBijective` packages this bijection.

The included HomRigidity and CoverDescent Markdown files describe those
proofs and their supporting finite-algebra rigidity in detail. This is
internal derived content for the descent step of Conrad's complete-local
deformation theorem. Completeness of `A`, target flatness, and target finite
type are not required for this equivalence. Neither an effective adic
comparison nor existence of a cover-level lift is asserted here.
