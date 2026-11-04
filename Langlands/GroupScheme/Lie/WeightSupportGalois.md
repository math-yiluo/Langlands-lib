# Galois transport of actual action weight spaces

This is an internal construction from the published actual dual-number Lie
kernels, their coefficient maps and scheme-base-change comparisons, and the
canonical Galois action on character lattices. The proof route uses twisted
coefficient algebras and the actual action differential. Worker 1264 contributed
the coefficient-twist proof design and the published differential comparison;
Worker 1445 implemented the semilinear and weight-support transport here. No
external structural theorem or weight-support invariance premise is used.

Let `k` and `K` be commutative rings in a common arbitrary universe `u`, with
`K` a `k`-algebra. Let `G` be a group scheme over `Spec k` with affine structure
morphism, and let `G_K` be its actual scheme pullback. Write
`L(G,A) = Additive (lieKernel G A)` for the module obtained from the identity
kernel on dual numbers over a coefficient algebra `A`.

`Lie.kernelCoefficientMap_comp` and `Lie.kernelCoefficientMap_id` prove
composition and identity for the actual maps on these kernels. Given an actual
`k`-algebra equivalence from `A` to `B`, `Lie.kernelCoefficientEquiv` applies it
to the dual-number coefficients to define a semilinear equivalence
`L(G,A) ≃ₛₗ L(G,B)`. Its inverse applies the inverse algebra equivalence.

For `σ : K ≃ₐ[k] K`, let `E` be the published linear equivalence
`Lie.kernelBaseChangeLinearEquiv k K G K` from `L(G_K,K)` to `L(G,K)`.
`Lie.baseChangeGaloisEquiv k K G σ` is the actual `σ`-semilinear equivalence

```text
x ↦ E⁻¹ (lieKernelMapLinear G σ.toAlgHom (E x)).
```

The inverse is obtained from the inverse coefficient equivalence. This
construction needs no field, splitting, finite-dimensionality or smoothness
hypothesis.

For a commutative `K`-algebra `A`, `Lie.GaloisTestAlgebra σ A` has the same
underlying ring as `A` and the `K`-algebra map `algebraMap K A ∘ σ`.
When `A` has a compatible `k`-algebra structure, that structure is retained,
and compatibility with `k → K` follows because `σ` fixes `k`.
`Lie.galoisTestIso` identifies its affine test scheme with the original test
whose structure map was changed by `Spec σ`; its underlying scheme map is the
identity. `Lie.galoisTestPoint` expresses the published canonical descent point
on this twisted affine test. The theorem
`Lie.affineBaseChangeEquiv_galoisTestPoint` proves that the original and twisted
points agree after the actual comparison over `k`.

For any commutative group scheme `T` over `Spec k`, let `ρ` be the published
`characterLattice.galoisRepresentation k K T`. If `χ` is a character of `T_K`
and `s` an `A`-point, `Lie.characterValue_galoisRepresentation` proves

```text
characterValue (ρ σ χ) s
  = characterValue χ (galoisTestPoint k K σ A T.toGrp s).
```

Both sides are units of the same underlying ring `A`. The implemented proof
uses the published character transport formula on global units, naturality
along the twisted-test isomorphism, and the spectrum/global-sections
identification. `Lie.characterValue_eq_globalUnits` and
`Lie.pointsEquiv_galoisTestIso_inv` isolate these two conversions.

For the coefficient image of a Lie vector, the theorem
`Lie.kernelBaseChangeLinearEquiv_galois_vector` proves that mapping the
semilinearly transported vector to `A`, then applying the base-change
comparison, equals mapping the original vector to the twisted algebra and
applying its comparison. This is equality in the original `k`-group's Lie
kernel over the underlying ring `A`. It follows from coefficient-map
composition and naturality of the published kernel comparison.

Now assume that `k` and `K` are fields. Let `a : AutomorphicAction T.toGrp U`
be an actual action over `Spec k`, where `T` is any commutative group scheme
and `U` has affine structure morphism. Write `a_K` for the pulled-back action.
`RelativeRoot.mem_actionWeightSpace_iff_differential` expresses intrinsic
weight-space membership by the eigenvector equality for the actual differential,
after every coefficient-algebra extension and at every acting point.
`RelativeRoot.galois_mem_actionWeightSpace` proves

```text
x ∈ actionWeightSpace a_K χ
  → baseChangeGaloisEquiv k K U σ x ∈ actionWeightSpace a_K (ρ σ χ).
```

The proof tests the original membership on the twisted algebra and twisted
point. It transports the resulting differential equality through the published
linear base-change comparison, using
`AutomorphicAction.differential_baseChange`, the point comparison, the vector
comparison and the character-value identity above. Injectivity of the comparison
detects the required equality on the actual pulled-back group.

`RelativeRoot.actionWeightSpace_galois_ne_bot` uses injectivity of the semilinear
equivalence to retain a nonzero vector.
`RelativeRoot.actionWeightSpace_galois_ne_bot_iff` applies the same argument to
`σ.symm` and cancels the two canonical character actions using the published
representation law. Thus

```text
actionWeightSpace a_K (ρ σ χ) ≠ ⊥ ↔ actionWeightSpace a_K χ ≠ ⊥.
```

The character may be zero. The equivalent whole-group intrinsic support
assertion is `RelativeRoot.mem_actionWeightSupport_top_galois_iff`.
`RelativeRoot.restricted_actionWeightSpace_galois_ne_bot_iff` gives the same
conclusion for a descended action restricted along an actual homomorphism
`j : T.toGrp ⟶ H`, using the published restriction/base-change compatibility.
`RelativeRoot.weightSpace_galois_ne_bot_iff` specializes to the original adjoint
weight spaces using the published conjugation comparisons.

The support results retain arbitrary field extensions and every coefficient
algebra test. They require no splitness of `T_K`, finite type, smoothness,
reductivity, perfectness, separability or density of rational points. They
concern the whole target group's intrinsic support, or a restriction of its
acting group; they do not assert transport for an arbitrary subgroup functor.
They do not establish positivity of weights, construct a Borel subgroup or prove
the ambient maximal-split Levi-centralizer statement.
