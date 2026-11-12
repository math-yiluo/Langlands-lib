# The split symplectic group is reductive

This internal module proves that the split symplectic group scheme
`SymplecticMatrix.groupScheme l R` (defined in `SymplecticMatrix.Basic`) is reductive:

* `isConnectedReductive l K`: over every field `K`, `groupScheme l (CommRingCat.of K)` is a
  connected reductive group in the sense of the Library's `IsConnectedReductive`. That means
  smooth, affine, connected, and with trivial unipotent radical after base change to an
  algebraic closure of `K`.
* `isPseudoReductive l K`: the same group is pseudo-reductive over `K` itself.
* `isReductive l R`: over every commutative ring `R`, `groupScheme l R` is a reductive group
  scheme. That means smooth and affine, with pseudo-reductive geometric fibres.

No assumption is made on `l` (it may be empty) or on the characteristic.

## Homomorphisms into the symplectic group

These are built from the block matrices of `SymplecticMatrix.Generation`:

* `leviHom A : GL l A →* symplecticGroup l A`, `g ↦ levi g = [[g, 0], [0, (g⁻¹)ᵀ]]`.
* `upperHom hS φ` and `lowerHom hS φ`: for a symmetric matrix `S` and a ring map `φ`, the
  homomorphisms `t ↦ upper (t • φ(S))` and `t ↦ lower (t • φ(S))` from the additive group
  of `A` (written multiplicatively as `Multiplicative (Fin 1 → A)`).

These are natural in the coefficient algebra (`leviTrans`, `upperTrans`, `lowerTrans`). The
published `Corepresented.groupSchemeMap` turns them into homomorphisms of group schemes:

* `leviMap R : GeneralLinear.groupScheme l R ⟶ groupScheme l R`;
* `upperMap R hS`, `lowerMap R hS : VectorGroup.groupScheme R 1 ⟶ groupScheme l R`, for a
  symmetric `S` over `R`.

`pointsEquiv_leviMap`, `pointsEquiv_upperMap` and `pointsEquiv_lowerMap` compute them on
points over every test scheme `T`, with `φ = scalarMap T`.

## Connectedness

* `comp_mem_range_identityComponentι`: let `φ : H ⟶ G` be a homomorphism over a field, with
  `G` smooth and affine and `H` connected. Then every point `z ≫ φ` lies in the identity
  component of `G`. It factors through `IdentityComponent.factor G φ`.
* `connectedSpace_groupScheme_of_isAlgClosed`: over an algebraically closed field `k`, the
  Library's criterion `IdentityComponent.connectedSpace_of_forall_mem_range` reduces
  connectedness to showing that every rational point lies in the identity component. A
  rational point is a symplectic matrix over `Γ(Spec k, ⊤)`. Transport it to `k` along
  `Γ(Spec k, ⊤) ≅ k`. The big-cell decomposition `exists_eq_upper_mul_lower_mul_levi_mul_upper`
  writes it as `upper X * lower Z * levi A * upper Y` with symmetric `X`, `Z`, `Y`. These
  factors are the images of the rational point `1` of `𝔾ₐ` under `upperMap X`, `lowerMap Z`
  and `upperMap Y`, and of the rational point `A` of `GL_l` under `leviMap`. `𝔾ₐ` is
  connected (`connectedSpace_vectorGroup`, the spectrum of a polynomial ring), and so is
  `GL_l` (the Library's `connectedSpace_generalLinear`). The identity component is a
  subgroup, so it contains the product.
* `connectedSpace_groupScheme l K`: for a general field `K`, connectedness descends from the
  algebraic closure. This uses `connectedSpace_of_baseChange` along the surjective map
  `toAlgebraicClosure K`, and the comparison `baseChangeModelIso` between the base change
  and the model over the algebraic closure.

## Trivial unipotent radical

This section follows the Library's proof for the special linear group
(`Reductive/SpecialLinear`), with symplectic matrices in place of `SL_n`.

* `constantPoint T g` is the point of the group over `T` given by a symplectic matrix `g`
  over the base field.
* `mulVec_mem_fixedSubmodule`: let `i : H ⟶ Sp` have normal range. Then the subspace of
  `K^{l ⊕ l}` fixed by `H` (through the inclusion into `GL_{l ⊕ l}`) is stable under every
  symplectic matrix over `K`. Normality conjugates `H` by constant points.
* `hasTrivialUnipotentRadical l K`: let `H` be a unipotent group with a normal homomorphism
  into `Sp`. Unipotence gives a nonzero fixed vector. By `eq_top_of_forall_mulVec_mem` from
  `SymplecticMatrix.Generation`, the stable fixed subspace is everything. So `H` acts
  trivially on every standard basis vector, its points map to `1`, and the range of `i` is
  trivial. When `l` is empty there is nothing to prove.

Base change to the algebraic closure and the iso `baseChangeModelIso` with
`HasTrivialUnipotentRadical.of_iso` give the geometric statement in `isConnectedReductive`. Base change to a
geometric point with `IsPseudoReductive.of_iso` gives the fibres in `isReductive`.

## Provenance

These are standard facts about the split symplectic group. The proofs were written for this
module from the cited Library and Mathlib results. Connectedness uses the big-cell
decomposition rather than a Bruhat decomposition. The radical argument is adapted from the
Library's special linear case.
