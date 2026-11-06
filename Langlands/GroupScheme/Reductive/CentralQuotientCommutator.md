# Commutators in the preimage of a unipotent subgroup under a central quotient

Authors: Worker 1428 (Lean proof and Markdown) and Worker 1499 (Markdown
revision and submission).

This internal helper module of the proof of
`Langlands.GroupScheme.CentralQuotientReductiveStatement` generalizes the
`Preimage` section of the published module `Adjoint/CenterQuotientCommutator`
(Worker 1499). That section handles the quotient of `G` by its full centre;
this module handles the quotient by any subgroup functor `N ≤ center G`. It is
derived content: the statements are chosen for this proof and are not items of
the cited literature. Everything is in the namespace
`Langlands.GroupScheme.CentralQuotient`. The proofs are those of the published
file, with one change. Two places there identify the kernel of `q` with the
centre. Here they use the inclusion `N ≤ center G` instead, through
`mem_center_of_comp_eq_one`. The published helpers
`CenterQuotient.hom_eq_one_of_isCentral`, `commutatorElement_comp`,
`comp_commutatorElement` and `commutatorElement_mul_right_of_commute` are
imported and reused unchanged.

Notation: `k` is a field and all group schemes are over `Spec k`. `center G` is
the Library centre subgroup functor (`Rational/Characters`). `IsCentral f`
means that every point of the source maps into `center G`. `⁅x, y⁆` is the
group commutator `x y x⁻¹ y⁻¹` of points.

## The preimage

Fix `q : G ⟶ Q`, `j : C ⟶ Q` and a subgroup functor `N` of `G`. The preimage
`H` is the Library group scheme `SubgroupPreimage.groupScheme q j`
(`Reductive/UnipotentRadicalQuotientReduction`). It is the fibre product of
`q` and `j`, with inclusion `ι : H ⟶ G` and projection `π : H ⟶ C`. Assume
`hq : RelativeRoot.IsFppfQuotient N q`, meaning that `q` is flat, surjective
and locally of finite presentation and that the range of its actual kernel is
exactly `N`. Assume also `hN : N ≤ center G`.

- `mem_center_of_comp_eq_one`: a point `x` of `G` with `q x = 1` lies in
  `center G`. Such a point lies in the range of the kernel of `q`, which is
  `N` by `hq`, so `hN` applies.
- `commutator_mem_center`: if two points `a, b` of `H` have commuting images
  in `C`, then `⁅ι a, ι b⁆` lies in `center G`. Its image under `q` is the
  image under `j` of `⁅π a, π b⁆ = 1`.
- `mem_center_of_comp_projection_eq_one`: if `π a = 1`, then `ι a` lies in
  `center G`, by the same argument.

Fix also a rational point `h` of `H` with `hcen : π h ∈ center C`. The group
`C` need not be commutative; only the image of `h` is assumed central.

- `commutator_rational_mem_center`: for every point `y` of `H`, `⁅ι h, ι y⁆`
  lies in `center G`, where `h` is pulled back to the test scheme of `y`. This
  is `commutator_mem_center`, since `π h` commutes with `π y`.
- `commutatorPoints`, `commutatorPoints_apply`, `commutatorPoints_naturality`,
  `commutatorHom`: the map `x ↦ ⁅ι h, ι x⁆` on the points of `H` is a group
  homomorphism. Its values are central, so
  `commutatorElement_mul_right_of_commute` applies. It is natural in the test
  scheme, so the Library constructor `homOfPoints` turns it into a
  group-scheme homomorphism `commutatorHom : H ⟶ G`. `comp_commutatorHom`
  gives its value on points.
- `range_commutatorHom_le_center`: the range of `commutatorHom` lies in
  `center G`.

- `commute_preimage` (**main result**): let `G` be smooth and affine with
  trivial unipotent radical, let `Q` be affine, and let `C` be smooth, affine,
  connected and unipotent, with `hq`, `hN` and `hcen` as above. Then for every
  point `x` of `H`, on any test scheme, `ι h` and `ι x` commute.

  Proof. The centre has a closed representative `z : Z ⟶ G`
  (`center_hasClosedRepresentative`). Since the range of `commutatorHom` lies
  in the centre, it factors as `ψ' ≫ z` with `ψ' : H ⟶ Z`
  (`SubgroupFunctor.IsRepresentedBy.factorHom`). For a point `x` in the
  kernel of `π`, `ι x` is central by `mem_center_of_comp_projection_eq_one`,
  so `⁅ι h, ι x⁆ = 1`. Since `z` is a monomorphism, `ψ'` kills the kernel of
  `π`. The projection `π` is a base change of `q`, so it is flat, surjective
  and quasi-compact. The Library fpqc descent of homomorphisms
  (`FpqcHomDescent.hom`) therefore descends `ψ'` to `d : C ⟶ Z` with
  `π ≫ d = ψ'`. The composite `d ≫ z : C ⟶ G` lands in the range of `z`,
  which is the centre, so it is central. By `hom_eq_one_of_isCentral` it is
  trivial. Hence `commutatorHom = π ≫ d ≫ z` is trivial too, and
  `⁅ι h, ι x⁆ = 1` for all `x`.

- `commute_rational_preimage`: in particular, `ι h` and `ι h'` commute for
  every rational point `h'` of `H`.

- `commute_of_lift`: keep the hypotheses on `G`, `Q`, `C`, `q` and `N`. Let
  `x, x'` be rational points of `G` and `c, c'` rational points of `C` with
  `q x = j c`, `q x' = j c'` and `c ∈ center C`. Then `x` and `x'` commute.
  The pairs `(x, c)` and `(x', c')` are rational points of the fibre product
  `H`, so `commute_rational_preimage` applies.

`CentralQuotientCore` uses `commute_of_lift` with `C` a smooth connected
unipotent normal subgroup of the quotient `Q` over an algebraically closed
field. It shows that the rational points of `G` lying over a central subgroup
of `C` commute.
