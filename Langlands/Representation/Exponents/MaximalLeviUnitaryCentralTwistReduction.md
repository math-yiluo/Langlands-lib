# The unitary-central-twist step of the maximal-Levi reducibility theorem

Lean module: `Langlands.Representation.Exponents.MaximalLeviUnitaryCentralTwistReduction`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques* (2026 version,
literature ID `renard-2026-representations-groupes-reductifs-padiques`), VII.1.3, first
paragraph of the proof (printed p.224, PDF p.230). If the central character of
`i_P^G ρ` is not unitary, Renard twists by an unramified character `χ` of `G` that makes
it unitary, by "an argument from the proof of VI.8.5". The statement
`MaximalLeviUnitaryCentralTwistStatement` in
`Langlands.Representation.Exponents.MaximalLeviReducibilityReductionStatements` records
this step for the represented-parabolic interface. Its conclusion is that
`i_P^G(ρ ⊗ χ_M)` has a unitary central character, where `χ_M` is
`leviRestrictedCharacter p l χ`.

This module proves that statement, with one premise: Milne's theorem that parabolic
subgroups are the dynamic `P(λ)` (Milne, *Algebraic Groups*, Theorem 25.1), stated in the
Library as `ParabolicDynamicStatement` and not yet proved there. It is used only to put
the center of `G(F)` inside the parabolic points `P(F)`. Renard does not spell out this
step. The rest of the proof uses results the Library already proves.

The proof does not use the supercuspidality premise, maximality of `M`, or
irreducibility beyond the existence of a central character.

## Declarations

### Central elements and semidirect decompositions

Namespace `Langlands.Aubert.General`. Let `G` be a group and `P = M ⋉ U` a semidirect
decomposition (`IsSemidirectDecomposition P M U`) with `Z(G) ≤ P` (premise `hZP`).

- `IsSemidirectDecomposition.projection_mem_center`: the Levi projection of a central
  `z` is central in `M`. Proof: for `m ∈ M`, `m z = z m` in `P`. Apply the projection,
  which is a homomorphism fixing `M`.
- `parabolicCenterProjection h hZP : Z(G) →* Z(M)` is this projection, with
  `parabolicCenterProjection_coe` its value.
- `continuous_parabolicCenterProjection`: it is continuous when the projection
  `P → M` is continuous for the subspace topologies.
- `normalizedInduction_acts_of_center_le_parabolic`: let `G` be a locally compact
  nonarchimedean topological group and `U` closed. Suppose a smooth representation `A` of
  `M` has central character `χ : Z(M) →* ℂˣ`. Then each `z ∈ Z(G)` acts on the normalized
  induction `(normalizedInductionFunctor h hU).obj A` by the scalar
  `χ(parabolicCenterProjection h hZP z)`.

  Proof: for a section `f` and `x ∈ G`, `f(x z) = f(z x)` because `z` is central. View
  `z` as an element `q` of `P`. The covariance rule `normalizedInductionFunctor_covariant`
  gives `f(q x) = δ_P(q)^{1/2} · A(m_q) f(x)`, with `m_q` the Levi projection of `q`. The
  half modulus is `1` on central elements
  (`closedHalfCharacter_eq_one_of_mem_center`), and `A(m_q)` is the scalar `χ(m_q)`.

The Library's `normalizedInductionCentralCharacter_acts` needs `Z(G) ≤ M`. This lemma
needs only `Z(G) ≤ P`, which is what Milne's theorem gives.

### Represented parabolics

Namespace `Langlands.Aubert.General.RepresentedParabolic`. Here `k` is a field,
`p : P ⟶ G` a closed subgroup, `l : M ⟶ P` and `r : U ⟶ P` subgroups with `r` the geometric
unipotent radical, and the multiplication `M × U → P` an isomorphism (`hmul`). The
semidirect decomposition of the point images is the Library's
`isSemidirectDecomposition_pointImage`.

- `center_le_pointImage_of_parabolicDynamic (hD) (hG) (p) (hp)`: for `k` a nonarchimedean
  local field, `G` connected reductive and `p` parabolic, the center of `G(k)` lies in
  `pointImage p`, assuming `ParabolicDynamicStatement`.

  Proof: a central point `z` lies in the scheme center
  (`rationalCenterComparison`, read from right to left). Milne's theorem gives a
  cocharacter `λ` with `range p = P(λ)`. The scheme center lies in the dynamic
  centralizer `Z_G(λ)` (`center_le_dynamicCentralizer`), which lies in `P(λ)`
  (`Dynamic.centralizer_le_parabolic`). So `z` is in the range of `p` on `k`-points.
- `pointMultiplication_inv`: a point `q` of `P` equals `l(x) r(y)`, where `(x, y)` is
  `q` composed with the inverse of the multiplication isomorphism.
- `pointImage_projection_coe`: for `x = p(q)` in `pointImage p`, the Levi projection of
  `x` is `(l ≫ p)(x')`, where `x'` is the first component of the decomposition of `q`.
  Proof: by `pointMultiplication_inv`, `x = (l ≫ p)(x') · (r ≫ p)(y')`, and the
  projection is characterized by `projection_eq_iff`.
- `continuous_pointImage_projection`: for any field `k` with a topology and affine `G`, with
  `G(k)` carrying the point topology `RationalPointFamily.pointTopology`, the Levi
  projection `pointImage p → pointImage (l ≫ p)` is continuous.

  Proof: `rationalPointSubgroupHomeomorph` identifies `pointImage p` with `P(k)`, carrying
  the point topology of `P`. By `pointImage_projection_coe`, the projection is then the
  point map of the scheme morphism `inv (subgroupMultiplication l r) ≫ fst ≫ l ≫ p` from
  `P` to `G`. Point maps of scheme morphisms are continuous
  (`continuous_rationalPointMap`). The topology on the Levi points is the subspace
  topology, so continuity into `G(k)` suffices (`continuous_induced_rng`).

### The main theorem

- `maximalLeviUnitaryCentralTwist_of_parabolicDynamic (hD : ParabolicDynamicStatement.{u}) :
  MaximalLeviUnitaryCentralTwistStatement.{u, v}`.

  Proof. Let `ρ` be an irreducible smooth representation of `M(k)`.

  1. Schur's lemma (`CuspidalSupport.rationalPointCentralCharacter`) gives a central
     character `ω_ρ` of `ρ`. Since `ρ` is irreducible it is nonzero
     (`Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible`), so `ω_ρ` has open
     kernel (`SmoothRep.HasCentralCharacter.isOpen_ker`).
  2. `center_le_pointImage_of_parabolicDynamic` puts `Z = Z(G(k))` inside `pointImage p`.
     Set `ω_G(z) = ω_ρ(m_z)`, with `m_z` the Levi projection of `z` transported to `M(k)`
     by the inverse of `leviPointsEquiv : M(k) ≃ pointImage (l ≫ p)`. The map `z ↦ m_z` is continuous
     (`continuous_parabolicCenterProjection` with `continuous_pointImage_projection`), so
     `ω_G` has open kernel.
  3. `normalizedInduction_acts_of_center_le_parabolic`, applied to the pullback of `ρ` to
     the Levi point image, shows that `z ∈ Z` acts on `i_P^G ρ` by `ω_G(z)`.
  4. `exists_positive_unramifiedCharacter_norm_mul_eq_one` (module
     `PositiveUnramifiedCentralTwist`, the VI.8.5 argument) gives an unramified `χ` with
     `‖χ(z) ω_G(z)‖ = 1` on `Z`. `twistUnitaryCentralCharacter` then makes
     `(i_P^G ρ) ⊗ χ` have the unitary central character `χ|_Z · ω_G`.
  5. `leviInductionUnramifiedTwistIso` (module `MaximalLeviTwistReduction`) gives
     `i_P^G(ρ ⊗ χ_M) ≅ (i_P^G ρ) ⊗ χ`. `UnitaryCentralCharacter.ofEquiv` transports the
     unitary central character along this isomorphism.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
