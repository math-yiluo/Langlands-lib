# Unipotent kernels from injectivity on a maximal torus

Module `Langlands.GroupScheme.Absolute.KernelMaximalTorusUnipotent`.

## Purpose and provenance

The proof of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 8.4.15 (printed p. 307, PDF p. 338) proves unipotence of the kernel
of the special-fibre map `ρ` in one sentence. Since `ρ` is injective on the
maximal torus `S` of the special fibre, it is injective on every torus, because
all maximal tori are conjugate. Hence the connected kernel contains no nontrivial
torus and is unipotent.

This module proves that step for an abstract homomorphism of group schemes. It
does not mention integral models, open cells or buildings. The statements and
their arrangement are internal design by Worker 4783 for Task 6203, which
Worker 282 and Worker 4783 share. Two published results do the work:

* `Langlands.GroupScheme.algClosedNoCocharacterUnipotent`: a smooth, connected,
  affine group over an algebraically closed field is unipotent if all of its
  cocharacters `𝔾_m → G` are trivial;
* `Langlands.GroupScheme.maximalTorusConjugacy`: in a smooth, connected, affine
  group over an algebraically closed field, any two maximal tori are conjugate
  by a rational point.

Applying this module to KP 8.4.15 requires two inputs that are not proved here.
First, a maximal torus of the special fibre (or, more generally, a subgroup into
which every cocharacter can be conjugated). Second, injectivity of `ρ` on that
subgroup. This module proves neither smoothness nor connectedness of any kernel,
nor the host theorem of Task 6203.

A *cocharacter* of a group scheme `G` over `S` is a homomorphism
`(Gm S).toGrp ⟶ G`. The trivial homomorphism is `0`.

## Kernels over an arbitrary base

Let `q : G ⟶ H` be a homomorphism of group schemes over a scheme `S`, and let
`kernelι q : kernel q ⟶ G` be the inclusion of its published scheme-theoretic
kernel.

* `kernelι_comp_eq_zero`: `kernelι q ≫ q = 0`. This is the commutative square of
  the published pullback `kernel_isPullback q`, which defines the kernel as the
  pullback of the unit section of `H`.
* `eq_zero_of_comp_kernelι_eq_zero`: if a homomorphism `z : J ⟶ kernel q`
  satisfies `z ≫ kernelι q = 0`, then `z = 0`. The underlying scheme morphism of
  `kernelι q` is a monomorphism, so it can be cancelled.

## Cocharacter conjugacy over an arbitrary base

Let `s : M ⟶ G` be a further homomorphism.

* `cocharacter_eq_zero_of_homConjugate`: suppose that
  1. (`hconj`) for every cocharacter `z` of `G` there is a cocharacter `w` of
     `M` with `HomConjugate z (w ≫ s)`, that is,
     `z ≫ (G.innerIso g).hom = w ≫ s` for some base point `g` of `G`; and
  2. (`hinj`) every cocharacter `w` of `M` with `w ≫ s ≫ q = 0` is `0`.

  Then every cocharacter `z` of `G` with `z ≫ q = 0` is `0`.

  *Proof.* Choose `w` and `g` as in (1). The published `innerIso_hom_comp` says
  that `q` intertwines the inner automorphism of `G` by `g` with the inner
  automorphism of `H` by the image of `g`. Hence
  `w ≫ s ≫ q = z ≫ q ≫ (inner automorphism of H) = 0`. By (2), `w = 0`, so
  `z ≫ (G.innerIso g).hom = 0`. Composing with the inverse automorphism gives
  `z = 0`.
* `cocharacter_injective_of_mono`: hypothesis (2) holds whenever the underlying
  scheme morphism of `s ≫ q` is a monomorphism. Cancel it from
  `w ≫ s ≫ q = 0 = 0 ≫ s ≫ q`.

## Over an algebraically closed field

Now let `k` be an algebraically closed field and `q : G ⟶ H` a homomorphism of
group schemes over `Spec k`.

* `isUnipotent_kernel_of_homConjugate`: assume that `kernel q` is smooth, affine
  and connected (as instances), and that `s : M ⟶ G` satisfies (1) and (2). Then
  `IsUnipotent (kernel q)`.

  *Proof.* By `algClosedNoCocharacterUnipotent`, it suffices that every
  cocharacter `z` of `kernel q` is `0`. The cocharacter `z ≫ kernelι q` of `G`
  is killed by `q` because of `kernelι_comp_eq_zero`. So it is `0` by
  `cocharacter_eq_zero_of_homConjugate`, and then `z = 0` by
  `eq_zero_of_comp_kernelι_eq_zero`.
* `exists_homConjugate_of_isMaximalTorus`: let `G` be smooth, affine and
  connected, and let `s : S.toGrp ⟶ G` be a maximal torus (`IsMaximalTorus s`,
  with `S` a commutative group scheme). Then every cocharacter `z` of `G` is
  conjugate to `w ≫ s` for some cocharacter `w` of `S`.

  *Proof.* The published `torusImageClosedTorusStatement` (proved in
  `Langlands.GroupScheme.Torus.ImageProof`) factors `z` as `p ≫ j`, where
  `j : Z ⟶ G` is a closed subgroup and `Z` is a torus. The published
  `exists_maximalTorus_extension_of_finiteType` puts `j` inside a maximal torus
  `j' : M ⟶ G` via some `f` with `f ≫ j' = j`. By `maximalTorusConjugacy` there
  are a base point `g` and an isomorphism `φ : M ≅ S` with
  `j' ≫ (G.innerIso g).hom = φ ≫ s`. Take `w = p ≫ f ≫ φ`.
* `isUnipotent_kernel_of_isMaximalTorus`: let `G` be smooth, affine and
  connected, let `kernel q` be smooth, affine and connected, and let `s` be a
  maximal torus of `G` such that every cocharacter `w` of `S` with
  `w ≫ s ≫ q = 0` is `0`. Then `IsUnipotent (kernel q)`. This combines the two
  previous results, and it is the form of KP's sentence quoted above.
