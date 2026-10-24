# Normalized affine points under scalar extension

This internal construction compares the actual scalar-extension isomorphism of
similitude group schemes with tensor-tower expansion on affine test algebras.
It uses the existing constructions in `SchemeScalarExtension`,
`InvolutionBaseChangeTower`, and `CorepresentedAffineComparison`; it makes no
additional claim from the Harris literature.

Let R, S and T be commutative rings in the same universe, with compatible
R-algebra and S-algebra structures forming a tower R → S → T. Let A be an
R-algebra, possibly noncommutative, with a finite basis b indexed by a finite
type and an R-linear algebra involution σ. Write X = Spec_S T and let G be the
similitude scheme constructed from b and σ.

## Relative section normalization

`restrictedSections R S X` is the ring of global sections of X with the
R-action induced by the composite structural morphism X → Spec S → Spec R.
The existing section algebra over S and its proved scalar-tower compatibility
allow the relative affine-section S-algebra equivalence to be restricted to R.
`restrictedAffineSectionsEquiv` is the resulting R-algebra equivalence

    Γ_R(X viewed over R) ≃ₐ[R] T.

`restrictedAffineSectionsEquiv_ringHom` identifies its underlying ring map
with the forward map of Mathlib's actual `Scheme.ΓSpecIso T`. Thus the
normalization uses the original structural scalar actions and the ordinary
spectrum section map.

## Affine points of the pullback

`baseChangedAffinePointsEquiv` is a multiplicative equivalence

    Hom_S(Spec_S T, G ×_Spec R Spec S) ≃* Sim(σ_T).

First, `baseChangedPointsEquiv` uses the pullback adjunction and the
corepresented global-section point equivalence. Then the similitude functor
maps the section algebra isomorphism just constructed. The theorem
`baseChangedAffinePointsEquiv_apply` identifies this second step with the
existing coefficient-change homomorphism `σ.baseChangeMap`.

## Scalar-extension formula

For every actual point x of the pullback over Spec_S T,
`scalarExtensionIso_affinePoints` proves

    affinePointsEquiv(b_S, σ_S)(x ≫ scalarExtensionIso(S,b,σ))
      = baseChangeTowerSimilitudes(S,T,σ)(baseChangedAffinePointsEquiv(T,b,σ)(x)).

The right side expands T ⊗_R A to T ⊗_S (S ⊗_R A), preserving the scalar
multiplier. The left side uses the affine point equivalence of the model
constructed after scalar extension, and the actual group-scheme isomorphism.

The proof first applies the generic comparison between global-section and
affine point coordinates to the target model. The already proved
`scalarExtensionIso_points` gives its formula before section normalization.
Finally, `baseChangeTowerSimilitudes_naturality` commutes tensor-tower expansion
with the section algebra map. Explicit source scalar structures and local
transparency settings only guide elaboration of these existing maps.

This unit supplies normalized affine coordinates for one scalar extension.
It does not yet identify them with the affine coordinates of a separately
presented rational test scheme, or establish the Harris direct-versus-iterated
matrix-coordinate and reflex-conjugacy results.
