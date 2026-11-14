# Unipotent kernels from a maximal torus of a possibly disconnected group

Module `Langlands.GroupScheme.Absolute.KernelMaximalTorusIdentityComponent`.

## Purpose and provenance

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), prove in
Proposition 8.4.15 (printed p. 307, PDF p. 338) that the kernel of the
special-fibre map `ρ` is unipotent: `ρ` is injective on a maximal torus of the
special fibre, and all maximal tori are conjugate, so the connected kernel
contains no nontrivial torus. The module
`Langlands.GroupScheme.Absolute.KernelMaximalTorusUnipotent` (approved
candidate `3c8c7c2b`, included in this submission's repository paths until it
is integrated) proves this step
when the source group `G` is connected (`isUnipotent_kernel_of_isMaximalTorus`).

The special fibre of a smooth integral model need not be connected. This module
removes that hypothesis by passing to the identity component. The statements
and their arrangement are internal design by Worker 4783 for Task 6203, which
Worker 282 and Worker 4783 share. No statement here comes from the literature.

The published module `Langlands.GroupScheme.IdentityComponent` supplies, for a
smooth affine group `G` over a field:

* the identity component `identityComponent G` and its inclusion
  `identityComponentι G`, a closed subgroup
  (`IdentityComponent.isClosedSubgroup_identityComponentι`);
* `IdentityComponent.factor G z`: every homomorphism `z` from a group whose
  underlying scheme is connected factors through the identity component
  (`IdentityComponent.factor_identityComponentι`);
* `IdentityComponent.existsUnique_factor_of_isSplitTorus`: every homomorphism
  from a split torus factors uniquely through the identity component.

This module does not prove smoothness or connectedness of any kernel, and it
does not prove the host theorem of Task 6203.

## Results

Let `k` be an algebraically closed field. All group schemes below are over
`Spec k`, except in the first result.

* `HomConjugate.comp`: over any base scheme, if `χ` and `ψ : A ⟶ B` are
  conjugate (`HomConjugate χ ψ`), then so are `χ ≫ j` and `ψ ≫ j` for every
  homomorphism `j : B ⟶ C`.

  *Proof.* If `χ ≫ (B.innerIso g).hom = ψ`, take the base point `g ≫ j` of `C`.
  The published `innerIso_hom_comp` says that `j` intertwines the two inner
  automorphisms.
* `exists_isMaximalTorus_identityComponent`: let `G` be smooth and affine, and
  let `s : S.toGrp ⟶ G` be a maximal torus (`IsMaximalTorus s`). Then there is a
  homomorphism `s₀ : S.toGrp ⟶ identityComponent G` with
  `s₀ ≫ identityComponentι G = s`, and `s₀` is a maximal torus of the identity
  component.

  *Proof.* Over an algebraically closed field the torus `S` is split. This uses
  the published `IsTorus.isSplitTorus_of_finiteGaloisSplitting` with the proved
  `torusFiniteGaloisSplitting`. So `s` factors as `s₀ ≫ identityComponentι G`.
  `s₀` is a closed subgroup by `IsClosedSubgroup.of_comp`, because the
  composite `s` is one and `identityComponentι G` is a closed immersion. For
  maximality, let `i' : T' ⟶ identityComponent G` be a closed torus with
  `f ≫ i' = s₀`. Then `i' ≫ identityComponentι G` is a closed torus of `G`
  through which `s` factors. Maximality of `s` makes `f` an isomorphism.
* `exists_homConjugate_of_isMaximalTorus_identityComponent`: let `G` be smooth
  and affine, connected or not, and let `s : S.toGrp ⟶ G` be a maximal torus.
  Then every cocharacter `z : 𝔾_m ⟶ G` is conjugate to `w ≫ s` for some
  cocharacter `w` of `S`.

  *Proof.* `𝔾_m` is connected, so `z` factors through the identity component
  as `IdentityComponent.factor G z`. The previous result makes `s₀` a maximal
  torus of the identity component, which is smooth, affine and connected.
  `exists_homConjugate_of_isMaximalTorus` (module `KernelMaximalTorusUnipotent`)
  gives `w` with the
  factor of `z` conjugate to `w ≫ s₀`. Composing with `identityComponentι G`
  (`HomConjugate.comp`) gives the claim, since `s₀ ≫ identityComponentι G = s`.
* `isUnipotent_kernel_of_isMaximalTorus_of_smooth`: let `q : G ⟶ H` be a
  homomorphism with `G` smooth and affine; `G` need not be connected. Assume
  that `kernel q` is smooth, affine and connected (instances). Let
  `s : S.toGrp ⟶ G` be a maximal torus such that every cocharacter `w` of `S`
  with `w ≫ s ≫ q = 0` is `0`. Then `IsUnipotent (kernel q)`.

  *Proof.* Apply `isUnipotent_kernel_of_homConjugate` (module
  `KernelMaximalTorusUnipotent`) with the
  conjugacy hypothesis given by the previous result.
