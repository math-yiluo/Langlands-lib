# Tensor compatibility of equal-composite pullback comparisons

This is a derived module-sheaf prerequisite for the tensor law of the intrinsic
kernel character. It uses the actual sheaf tensor and canonical pullback
comparisons already in the Library. It introduces no linearization or character
as input.

For schemes `U`, `X`, `Y`, maps `p : X → Y` and `a,b : U → X`, and an equation
`h : a ≫ p = b ≫ p`, write `E_M` for
`equalCompositeIso p a b h M`. This is the canonical comparison from `a* p* M`
to `b* p* M`, in the ordinary-to-translated direction used by its consumer.
The following assertions hold for arbitrary module sheaves, without a local
rank assumption.

`compHom_tensor` proves compatibility of the generalized pullback-composition
comparison with the canonical tensor comparison. Its proof substitutes the
equal composite and applies the published `pullbackTensorComposition` theorem.
`equalCompositeIso_tensor` then proves

```
E_(M⊗N) ≫ b*(tensor comparison for p) ≫ tensor comparison for b
  = a*(tensor comparison for p) ≫ tensor comparison for a ≫ (E_M ⊗ E_N).
```

The proof cancels the tensor of the two composition isomorphisms for `b`,
applies the composition theorem on both sides, and uses tensor functoriality.
Neither of these laws requires tensor-comparison invertibility.

`tensorUnitMap_hom` states that contracting two endomorphisms `e,d` of the
structure module by `O ⊗ O ≅ O` gives their composite `e ≫ d`. It follows from
naturality of both explicit tensor unitors and their equality on the tensor
unit. `pullbackTensor_unit` proves compatibility of the canonical pullback
comparison with this contraction, using the published left-unitor pullback law.
These are proved coherence laws, rather than extra assumptions.

`tensorPullbackTrivialization preservation p α β` constructs a trivialization
of `p*(M ⊗ N)` from actual trivializations `α : p*M ≅ O_X` and `β : p*N ≅ O_X`.
It uses, in order, the canonical tensor comparison for `p`, the tensor of `α`
and `β`, and the left unitor `O_X ⊗ O_X ≅ O_X`. Its explicit hypothesis
`pullbackTensorComparisonIsIsoStatement` says that the existing canonical
pullback tensor comparison is invertible for every scheme map. This module
does not prove that separate preservation assertion.

For a map `a`, let `φ_a(α)` be `a*α` followed by `pullbackUnitIso a`.
`tensorPullbackTrivialization_pullback_hom` proves that `φ_a` of the tensor
trivialization is the iterated tensor comparison, followed by
`φ_a(α) ⊗ φ_a(β)` and the unit contraction. The proof uses naturality of the
canonical tensor comparison and `pullbackTensor_unit`.

`equalCompositeUnitAut_intertwine` expresses the defining normalized action as

```
E_M ≫ φ_b(α) = φ_a(α) ≫ equalCompositeUnitAut p a b h α.
```

It follows by canceling the trivialization and unit isomorphisms in the defining
composite. Finally, `equalCompositeUnitAut_tensor` proves the exact equation

```
equalCompositeUnitAut p a b h (tensorPullbackTrivialization preservation p α β)
  = equalCompositeUnitAut p a b h α ≪≫ equalCompositeUnitAut p a b h β.
```

The implemented proof cancels the isomorphism `φ_a` of the tensor
trivialization, applies the preceding tensor-comparison and intertwining laws,
combines the two component comparisons by tensor functoriality, and contracts
the two unit automorphisms by `tensorUnitMap_hom`. Thus the tensor action is
the composite in the displayed order. Extracting its value at one will give
the product of the two action scalars.

The provenance is internal derivation from the published module-sheaf
constructions and their proved composition and unitor coherence. The module
contains no abelian-scheme geometric assertion, constant-functions theorem,
effective descent, or duality claim.
