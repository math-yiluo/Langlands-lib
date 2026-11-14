# Full central kernels from Galois-stable torus character images

This internal assembly connects the Library's full torus-kernel comparison,
actual character annihilators, and naturality of canonical descent transport.
It supplies the ambient-kernel invariance step for a supplied central isogeny;
it does not construct a numbered type-D vector quotient or compute its
integral character image.

For a central isogeny `p : G → Q` over a field `K`, assume that `G` is
connected reductive, `i : T → G` is a maximal torus, `i' : T' → Q` is a
closed subgroup inclusion with split torus source, and `t : T → T'`
satisfies `i ≫ p = t ≫ i'`. The theorem
`range_kernel_eq_torus_characterAnnihilator` identifies the full kernel
range in `G` with the image under `i` of the annihilator of the actual
integral image of character pullback along `t`. The existing
`IndexTwoKernel.kernelComparisonIso` identifies the full torus kernel
with the full group kernel and preserves their inclusions. Ranges are
unchanged by its source isomorphism; the published annihilator theorem
then identifies the torus-kernel range. No index-two hypothesis is used,
and the source torus need not be assumed split.

Over arbitrary schemes, `SubgroupFunctor.descentTransport_range_comp_baseChange`
proves that canonical descent transport commutes with the image of any
represented subgroup under a homomorphism from the original base. Writing
transport as the range of the pulled-back inclusion followed by the canonical
recovery map reduces the proof to functoriality of composition and the
naturality of that recovery map. The image is taken as a subgroup functor;
no claim that an arbitrary image is represented is needed.

Let `K/k` be any field extension, let `G` and the commutative source `T`
be defined over `k`, and let the preceding maximal-torus square exist
after base change to `K`. In particular, connected reductivity and
maximality are assumed on the base-changed objects, and the target torus
is split over `K`. For each `σ : K ≃ₐ[k] K`, the theorem
`range_galoisTranslate_kernel_eq_of_torus_characterImage` assumes that
ordinary Galois action preserves exactly the integral image of character
pullback along `t`. It proves equality between the full range of the
kernel inclusion and its canonical Galois translate in `G_K`.

The proof first replaces the ambient kernel range by the image of its
torus-kernel range. Naturality moves canonical transport through the
base-changed inclusion of `T` in `G`; the annihilator comparison and the
assumed integral-image stability then give the equality of torus ranges.
Every equality is between subgroup functors on all relative test schemes,
so neither reduction nor saturation removes infinitesimal information.
The kernel-invariance theorem has no restriction on the characteristic,
extension degree, or Dynkin type, and no separability or Galois-extension
hypothesis.

For a Galois extension, `Descent.centralIsogenyRecoveryOfStableTorusCharacterImage`
combines this result for every automorphism with the existing general
full-kernel descent construction. Assuming additionally that `G` is affine
and `Q` is affine over `K`, it returns `CentralIsogenyRecovery`: an actual
affine group over `k`, a central isogeny from `G`, a recovery isomorphism
of its base change with `Q`, and the exact equation recovering `p`.
These affine and Galois hypotheses apply only to this final construction;
it still permits infinite Galois extensions and every characteristic.

Application to the aligned type-D cover still requires an actual split
vector quotient, its numbered maximal-torus square and exact character
image, and the star-fixed-vertex input that ensures stability of that
image. The results here do not by themselves prove the host task's
aligned spin-cover existence statement.
