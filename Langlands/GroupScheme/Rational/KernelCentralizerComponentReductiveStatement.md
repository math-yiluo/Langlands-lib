# Connected reductivity of full-kernel centralizer identity components

Author: Worker 1335. Worker 1107 independently checked the source scope used in
this specialization.

`Langlands.GroupScheme.RelativeRoot.KernelCentralizerComponentReductiveStatement.{u}`
is the character-kernel specialization of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition A.8.12, printed
pp.552–554 (PDF pp.578–580). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The Lean file defines a proposition; it does not prove this specialization.

For an arbitrary field `k : Type u`, let `G` be an actual group scheme over
`Spec (CommRingCat.of k)` with `IsConnectedReductive G`, and let `S` be an
actual commutative group scheme whose underlying group scheme is a split
torus. For any homomorphism `i : S.toGrp ⟶ G` and nonzero character
`a : characterLattice S`, suppose `j : C ⟶ G` represents
`RelativeRoot.kernelCentralizer i a`, is a closed subgroup inclusion, and
has smooth source `C`. The conclusion is the actual
`IsConnectedReductive (identityComponent C)`.

The published `identityComponent` construction needs smoothness and
affineness of `C`. The statement uses the supplied smoothness and derives
affineness: `j` is a closed immersion, hence affine, and its composite with
the affine structure morphism of `G` is the structure morphism of `C` by
`Over.w`. Thus affineness of `C` is not an extra hypothesis.
The conclusion includes smoothness, affineness, connectedness, and
triviality of the geometric unipotent radical of that constructed identity
component. It does not assume any of these reductivity conclusions.

The kernel is exactly the published `characterKernel a`, the
scheme-theoretic kernel of the actual character `S → Gm`. In particular,
no reduction, passage to a connected component, or primitivity hypothesis
is applied to the kernel. By `mem_kernelCentralizer`, a point belongs to
the represented functor exactly when it commutes with every point of
that full kernel after every test-scheme refinement. The centralizer
representative is not assumed connected. The identity component is
taken only after forming this full centralizer.

The source deduction is as follows. The kernel of a character of a split
torus is a diagonalizable affine group scheme of finite type and remains
linearly reductive over an algebraic closure. It acts on `G` by the actual
conjugation action restricted along `characterKernelι a`. Its
scheme-theoretic fixed functor is the defined `kernelCentralizer i a`.
Proposition A.8.12 therefore gives connected reductivity of the identity
component of any smooth closed representative of this functor. It does
not require the acting group scheme to be smooth. The diagonalizable
kernel description, finite type, geometric linear reductivity and the
application of A.8.12 are mathematical proof obligations of this
specialization, not consequences proved by this proposition definition.

The universe `u` is arbitrary; the field, group schemes and all relative
test schemes lie in this one universe. The statement imposes no
perfectness or characteristic restriction. It does not require `i` to be
a maximal split torus inclusion or `a` to be a relative root. It asserts
neither existence nor smoothness of a centralizer representative, and
constructs no rational reflection representative.
