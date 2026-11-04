# Commutators in the preimage of a unipotent subgroup

Author: Worker 1499.

This internal helper module of the proof of
`Langlands.GroupScheme.CenterQuotientReductiveStatement` proves the step that
makes rational points of `G` lying over central rational points of a unipotent
subgroup of the quotient commute with the whole preimage. It is derived content: the statements are
chosen for this proof and are not items of the cited literature. Everything is
in the namespace `Langlands.GroupScheme.CenterQuotient`.

Notation: `k` is a field and all group schemes are over `Spec k`. `center G` is
the Library centre subgroup functor (`Rational/Characters`), `IsCentral f`
means that every point of the source maps into `center G`, and `⁅x, y⁆` is the
group commutator `x y x⁻¹ y⁻¹` of points.

## Central unipotent images

- `hom_eq_one_of_isCentral`: let `G` be smooth and affine with trivial
  unipotent radical (`HasTrivialUnipotentRadical G`), and let `U` be smooth,
  affine, connected and unipotent. A central homomorphism `f : U ⟶ G` is
  trivial: `f.hom.hom = 1`.

  Proof. It follows the pattern of the Library proof
  `HasTrivialUnipotentRadical.of_epi_of_finite_kernel_algClosed`
  (`CentralIsogeny/SemisimpleTransfer`). The Library's pointed image generation
  (`ImageGeneration.pointedImageGeneration`) gives a smooth, affine,
  geometrically connected closed subgroup `E` of `G` through which `f`
  factors, with a dominant factor map `U ⟶ E`. Since `E` is reduced, the factor
  map is injective on global functions, so `E` is unipotent
  (`IsUnipotent.of_appTop_injective`). The closed-image envelope of a central
  map lies in the centre (`closedImageEnvelope_le_center`), so the points of
  `E` are central, and `E` is normal. Trivial unipotent radical then forces
  `E` to be trivial, so its inclusion is `1`, and so is `f`.

## Commutator identities

For group schemes over an arbitrary base:

- `commutatorElement_comp`: a homomorphism preserves commutators of points.
- `comp_commutatorElement`: pulling back points along a test-scheme morphism
  preserves commutators.
- `commutatorElement_mul_right_of_commute` (any group): if `⁅a, y⁆` commutes with
  `x`, then `⁅a, x y⁆ = ⁅a, x⁆ ⁅a, y⁆`.

## The preimage

Fix `q : G ⟶ Q` and `j : C ⟶ Q`. The preimage `H` is the Library group scheme
`SubgroupPreimage.groupScheme q j` (`Reductive/UnipotentRadicalQuotientReduction`),
the fibre product of `q` and `j`, with inclusion `ι : H ⟶ G` and projection
`π : H ⟶ C`. Assume `hq : RelativeRoot.IsFppfQuotient (center G) q`: `q` is
flat, surjective and locally of finite presentation, and the range of its
kernel is exactly `center G`.

- `commutator_mem_center`: if two points `a, b` of `H` have commuting images
  in `C`, then `⁅ι a, ι b⁆` lies in `center G`. Its image under `q` is the image
  under `j` of `⁅π a, π b⁆ = 1`, so it lies in the kernel of `q`.
- `mem_center_of_comp_projection_eq_one`: if `π a = 1`, then `ι a` lies in
  `center G`, by the same argument.

Fix also a rational point `h` of `H` with `hcen : π h ∈ center C`. The group
`C` need not be commutative; only the image of `h` is assumed central.

- `commutator_rational_mem_center`: for every point `y` of `H`, `⁅ι h, ι y⁆`
  lies in `center G` (with `h` pulled back to the test scheme of `y`). This is
  `commutator_mem_center`, since `π h` commutes with `π y`.
- `commutatorPoints`, `commutatorHom`: the map `x ↦ ⁅ι h, ι x⁆` on the points
  of `H` is a group homomorphism. Its values are central by
  `commutator_rational_mem_center`, so
  `commutatorElement_mul_right_of_commute` applies. It is natural in the test
  scheme, so the Library constructor `homOfPoints` turns it into a
  group-scheme homomorphism `commutatorHom : H ⟶ G`. `comp_commutatorHom`
  states its value on points.
- `range_commutatorHom_le_center`: the range of `commutatorHom` lies in
  `center G`.

- `commute_preimage` (**main result**): let `G` be smooth and affine with
  trivial unipotent radical, `Q` affine, and `C` smooth, affine, connected and
  unipotent, with `hq` and `hcen` as above. Then for every point `x` of `H` (on
  any test scheme), `ι h` and `ι x` commute.

  Proof. The centre has a closed representative `z : Z ⟶ G`
  (`center_hasClosedRepresentative`), and `commutatorHom` factors as
  `ψ' ≫ z` with `ψ' : H ⟶ Z`, since its range lies in the centre
  (`SubgroupFunctor.IsRepresentedBy.factorHom`). The kernel of `π` maps to
  points `x` with `ι x` central (`mem_center_of_comp_projection_eq_one`), so
  `⁅ι h, ι x⁆ = 1` there, and `ψ'` kills the kernel of `π`; here `z` is a
  monomorphism. The projection `π` is the base change of `q`, so it is flat,
  surjective and quasi-compact. The Library fpqc descent of homomorphisms
  (`FpqcHomDescent.hom`) descends `ψ'` to a homomorphism `d : C ⟶ Z` with
  `π ≫ d = ψ'`. The composite `d ≫ z : C ⟶ G` is central, because it lands in
  the range of `z`, which is the centre. By `hom_eq_one_of_isCentral` it is
  trivial, hence so is `commutatorHom = π ≫ d ≫ z`. Its value `⁅ι h, ι x⁆` is
  therefore `1` for all `x`.

- `commute_rational_preimage`: in particular `ι h` and `ι h'` commute for every
  rational point `h'` of `H`.

- `commute_of_lift`: under the same hypotheses on `G`, `Q`, `C`, `q`, let
  `x, x'` be rational points of `G` and `c, c'` rational points of `C` with
  `q x = j c`, `q x' = j c'` and `c ∈ center C`. Then `x` and `x'` commute.
  The pairs `(x, c)` and `(x', c')` are rational points of the fibre product
  `H`, and `commute_rational_preimage` applies.

In the proof of the target, `C` is a smooth connected unipotent subgroup of the
quotient `Q` (over an algebraically closed field), and `commute_of_lift` shows
that the rational points of `G` lying over the centre of `C` commute.
