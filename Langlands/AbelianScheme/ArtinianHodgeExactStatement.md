# The degree-one Hodge sequence over an Artinian rational algebra

`Langlands.AbelianScheme.ArtinianHodgeExactStatement` takes an actual abelian
scheme over the spectrum of a commutative local Artinian \(\mathbf Q\)-algebra
\(R\). It ranges over every supplied finite affine open cover of its
underlying scheme. The maps are `closedFormClass` from compatible closed
one-forms to `AffineCechDeRham.H1` and `toStructureH1` from that module to
`structureH1`, the degree-one Čech classes of the functions. The proposition
asserts injectivity of the first map, surjectivity of the second, and that
`closedForms` and `structureH1` are finite free \(R\)-modules. It does not
restate exactness in the middle: `ker_toStructureH1` proves that the kernel
of `toStructureH1` is `hodgeF1`, which is defined as the image of
`closedFormClass`. Together these give a short exact sequence
0 → `closedForms` → `H1` → `structureH1` → 0.

## Source correspondence

In Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, §2.1.6, the exact sequence (2.1.6.5) on printed
p. 135 (PDF p. 163) is
\(0\to H^0(X,\Omega^1_{X/S})\to H^1_{\mathrm{dR}}(X/S)\to H^1(X,\mathcal O_X)\).
For an abelian scheme the source identifies the two ends with
\(\operatorname{Lie}^\vee_{X/S}\) and \(\operatorname{Lie}_{X^\vee/S}\),
which are locally free, and states that the last map is surjective, giving
(2.1.6.6). On an affine base the sheaf terms are modules.

The Lean terms match these as follows. On an abelian scheme every global
relative one-form is invariant, hence closed, so the compatible closed
one-forms of a cover correspond to the global one-forms. Since the scheme is separated
and every intersection of cover members is affine, the function Čech complex
of the cover computes \(H^1(X,\mathcal O_X)\). The two maps are the maps of
(2.1.6.5) in these degree-one Čech coordinates. Both ends have finite
rank, the relative dimension, so over the local base they are finite free.

Lan states (2.1.6.6) without requiring the base to be local, Artinian or a
\(\mathbf Q\)-algebra, so the proposition is a special case. It imposes no
finiteness or perfectness condition on the residue field.

The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
