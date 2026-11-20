# Local matrix representations with central kernel

`Langlands.GroupScheme.LocalCentralKernelRepresentationStatement.{u}` is a
`Prop`-valued definition. It states that a smooth, separated,
quasi-compact group scheme with connected residue-field fibres has, locally
on the base, a finite free matrix representation whose kernel is central.

## Hypotheses and conclusion

Let `S : Scheme.{u}` be arbitrary and let `G : GroupScheme S` have a smooth,
separated and quasi-compact structure morphism `G.X.hom`. For every
point `s : S`, the underlying topological space of the residue-field group
`RelativeIdentityComponent.residueFiber G s` (the base change of `G` to
`Spec κ(s)`) must be connected.

The conclusion holds for every point `s : S`. There are a commutative ring
`R : CommRingCat.{u}` and an open immersion `i : Spec R ⟶ S` whose image
contains `s`. There are also a natural number `m` and a
`MatrixRepresentation` `ρ` of the base change
`(GroupScheme.baseChange i).obj G` with index type `Fin m`. Such a `ρ` is a
morphism of group schemes over `Spec R` into
`GeneralLinear.groupScheme (Fin m) R`, the group scheme of invertible
`m × m` matrices over `R`. The kernel of `ρ` is central in the following
sense. Take any test scheme `U : Over (Spec R)` and any two points `g h` of
the base-changed group over `U`. If `g ≫ ρ.hom.hom = 1`, then
`g * h = h * g`.

The statement only asks that the kernel be contained in the centre. It does
not ask that the kernel equal the centre, and it does not ask that `ρ` be a
monomorphism.

## Source correspondence

SGA 3, Exposé XI, Corollary 6.11 applies to `G` locally of finite type and
quasi-separated over `S`, and to a subgroup `H` that is smooth, of finite
presentation, with connected fibres. Here take `H = G`. A smooth morphism is
locally of finite presentation, and with quasi-compactness and
quasi-separatedness it is of finite presentation. SGA 3 assumes only that `G`
is quasi-separated. The Lean statement assumes that `G` is separated, which
is stronger. Then the unit section is a closed immersion and the
infinitesimal neighbourhoods `G_n` are finite over the base. This hypothesis
holds where the statement is used, in the proof of
`Langlands.GroupScheme.SelfCentralizingTorusConjugacyQuotientAffineStatement`. The connected-fibre
hypothesis is exactly the residue-field condition above. Part (b) says
the following for quasi-compact `G`. There is `n > 0` with
`Centr_G(H) = Centr_G(H_n)`, where `H_n` is the `n`-th infinitesimal
neighbourhood of the unit section of `H`. With `H = G` the left side is the
centre `Z` of `G`. Corollary 6.10, on which 6.11 rests, is stated for
quasi-compact `S`. The Lean statement therefore restricts to an affine open
neighbourhood `Spec R` of `s`, which is quasi-compact, and over which `G` is
quasi-compact.
[SGA 3, Exposé XI, Corollaries 6.10 and 6.11](https://wstein.org/sga/SGA3/Expo11.pdf#page=33).

Exposé XVI, Proposition 3.1 lets `G(n)` be the `n`-th normal invariant of `G`
along the unit section (EGA IV 16), a locally free `O_S`-module of finite
rank. It lets `ρ_n` be the natural adjoint representation of `G` in
`GL_S(G(n))`, induced by the inner automorphisms `g ↦ int(g)` as in the
proof of Corollary 2.4. The first lines of the proof of 3.1 state that
`Z = Ker ρ_n` for `n` large, by Exposé XI, 6.11(b). This step does not use
the flatness of `Z` assumed in 3.1. Over an affine open neighbourhood of `s`
on which `G(n)` is free of some rank `m`, a basis turns `ρ_n` into a
homomorphism to the group of invertible `m × m` matrices. Its kernel is the
centre, so it is a `ρ` as in the conclusion. Equivalently, one may let `G`
act by conjugation on the coordinate algebra of `G_n`, a finite locally
free `O_S`-algebra. The kernel of that action is `Centr_G(G_n)`, which is
the centre for `n` large by 6.11(b).
[SGA 3, Exposé XVI, Proposition 3.1 and the beginning of its proof](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=13).

The statement is used in Task 7782 to prove
`Langlands.GroupScheme.SelfCentralizingTorusConjugacyQuotientAffineStatement`:
it supplies the local representations assumed by
`Langlands.GroupScheme.SelfCentralizingQuotientAffineOfRepresentationStatement`.

## Registered sources

- A. Grothendieck, SGA 3, Exposé XI, *Critères de représentabilité.
  Application aux sous-groupes de type multiplicatif des schémas en groupes
  affines*, Gille–Polo recomposition (December 2008), Corollaries 6.10 and
  6.11(b) with their proofs, printed pp. 117–118 (original pp. 177–179),
  one-based PDF pp. 33–34. `Expo11.pdf` in
  `sga3-exposes-xi-xii-xiv-gille-polo-2008`.
- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo
  recomposition (2008–2009), the proof of Corollary 2.4 (action through
  `int(g)` on the normal invariants), printed p. 312 (original pp. 506–507),
  one-based PDF p. 12; Proposition 3.1 and the beginning of its proof,
  printed pp. 313–314 (original pp. 509–510), one-based PDF pp. 13–14.
  `Expo16.pdf`, `sga3-expose-xvi-gille-polo-2009`,
  SHA-256 `3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.
