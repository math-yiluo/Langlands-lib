# Restriction of affine similitude points

This is an internal comparison between two actual affine test schemes and
their existing similitude point coordinates. It is derived from the scalar
tower identity, the relative Gamma–Spec maps, and the pullback point
adjunction. It does not import an additional assertion from the literature.

Let R → S → T be a tower of commutative rings in the same universe, with the
specified R-algebra and S-algebra structures and `IsScalarTower R S T`.
Write X = Spec_S T, Y for X viewed over Spec R, and Z = Spec_R T.

## The actual affine test identification

`restrictedAffineTestIso R S T` constructs an isomorphism i : Y ≅ Z in
schemes over Spec R. Both underlying scheme morphisms are the identity of
Spec T, as proved in `restrictedAffineTestIso_hom_left` and
`restrictedAffineTestIso_inv_left`. Compatibility with the base morphisms
uses `IsScalarTower.algebraMap_eq R S T` and contravariant composition of
spectrum maps. No arbitrary isomorphism is supplied as an assumption.

`restrictedAffineTestIso_sections` compares the actual relative section maps.
Let q_R : Γ_R(Z) → T be the affine-section isomorphism and let
q_res : Γ_R(Y) → T be `restrictedAffineSectionsEquiv` from
`AffineScalarExtension`. Then

    q_R ∘ Γ_R(i⁻¹) = q_res.

The proof reduces equality of algebra maps to equality of ring maps. Both
normalization maps are the forward `Scheme.ΓSpecIso T` map, and the section
map induced by the underlying identity of Spec T is the identity.

## Original coordinates of a pullback point

Now let A be an R-algebra, possibly noncommutative, with finite basis b and
R-linear algebra involution σ. Let G be its constructed similitude group
scheme. For each point x : X → G_S of the actual scalar pullback,
`originalAffinePoint b σ x` is the morphism Z → G obtained by the pullback
point adjunction followed by precomposition with i⁻¹. Its underlying scheme
map is exactly x followed by the first pullback projection; this is
`originalAffinePoint_left`.

`baseChangedAffinePointsEquiv_eq_originalAffinePoint` proves

    baseChangedAffinePointsEquiv(T,b,σ)(x)
      = affinePointsEquiv(b,σ,T)(originalAffinePoint(b,σ,x)).

The proof uses the generic affine/global point comparison on Z, naturality
of global-section points along i⁻¹, and the section-map identity above.
Functoriality then identifies the coefficient changes. Thus the normalized
pullback coordinates agree with the original R-affine coordinates through
this specified geometric map.

## Scalar extension in original affine coordinates

Combining this identity with `scalarExtensionIso_affinePoints` proves
`scalarExtensionIso_originalAffinePoints`:

    affinePointsEquiv(b_S,σ_S,T)(x ≫ scalarExtensionIso(S,b,σ))
      = baseChangeTowerSimilitudes(S,T,σ)
          (affinePointsEquiv(b,σ,T)(originalAffinePoint(b,σ,x))).

The right side is the existing tensor-tower expansion of similitudes from
T ⊗_R A to T ⊗_S (S ⊗_R A). This comparison holds for every compatible
commutative-ring tower and every affine test point of the specified model.
Specialization to the rational, real and complex Harris presentations and
the subsequent matrix-coordinate comparison remain separate work.
