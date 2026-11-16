# Monomorphisms on relative dynamic unipotent subgroups

This module is internal derived work for the reductive monomorphism problem.
It constructs the map on actual relative dynamic unipotent subgroup schemes
induced by a homomorphism of corepresented affine groups and proves its
closedness for a monomorphism. Its provenance is the existing orbit-defined
dynamic subgroup, affine corepresentation and Laurent-polynomial grading
interfaces, together with the algebra theorem in
`Langlands.CommutativeAlgebra.GradedEpimorphism`. It does not assert a separate
translation of a numbered literature result.

Let `R` be any commutative ring in universe `u`. Let `F` and `F'` be group-valued
functors on commutative `R`-algebras, whose underlying set-valued functors are
corepresented by `R`-algebras `B` and `C`, with corepresentations `e` and `e'`.
Write `G` and `G'` for the corresponding affine group schemes. Given
`χ : Gm → G` and `f : G → G'`, `unipotentMap χ f` is the homomorphism

`U_G(χ) → U_G'(χ ≫ f)`.

These are the actual quotient-coordinate representatives from
`Dynamic.Representability`. `unipotentMap_comp` says that this map commutes with
their inclusions into the ambient groups. It is constructed using the
all-test-scheme inclusion `Dynamic.unipotent_le_comap` and the unique
factorization through the represented target subgroup.

The main theorem, `isClosedImmersion_unipotentMap`, assumes only that
`f.hom.hom` is a monomorphism of schemes over `Spec R`. It proves that the
underlying scheme map of `unipotentMap χ f` is a closed immersion. There are no
field, DVR, smoothness, reducedness, finite type or finite presentation
assumptions. All constructions and proofs allow an arbitrary universe `u`.

The coordinate constructions and their proof roles are as follows:

- `pullback f : C →ₐ[R] B` is the actual classifying coordinate map of `f`.
  `augmentation e : B →ₐ[R] R` is its group's counit, with `R`-linearity
  obtained from the structure morphism of the identity section.
  `augmentation_pullback` follows from preservation of that section.
- `coaction_pullback` says that this coordinate map intertwines the two
  conjugation coactions. The proof applies spectrum faithfulness to the
  naturality of the orbit map. `coeff_coaction_pullback` takes coefficients.
- `unipotentAugmentation χ` descends the counit to `B ⧸ unipotentIdeal χ`:
  the identity belongs to the subgroup on every affine test scheme, so its
  classifying map kills the defining ideal. `unipCoaction_zero` identifies
  degree zero with the scalar given by this augmentation, using the defining
  degree-zero generators of the ideal.
- `unipotentPullback χ f` is the actual classifying coordinate map of the
  induced subgroup homomorphism. Applying spectrum faithfulness to
  `unipotentMap_comp` proves `unipotentPullback_mk`, its compatibility with the
  ambient quotient maps. Quotient surjectivity then descends augmentation and
  coefficient compatibility. `unipotentPullback_homogeneous` shows that every
  homogeneous degree is preserved.

For the final proof, monicity of `f` and the source subgroup inclusion makes
their composite monic. The factorization square therefore makes
`unipotentMap χ f` monic, as recorded by `mono_unipotentMap`. The two quotient
coordinate algebras have nonnegative grading by `unipCoaction_coeff_neg`; their
degree-zero components are precisely their augmentation scalars by
`unipCoaction_zero`. The component and augmentation compatibility just proved
supplies the remaining hypotheses of
`GradedLine.isClosedImmersion_specMap_of_mono`, which gives the desired closed
immersion of the actual induced map.

This module establishes the relative unipotent step. Relative cell comparison,
the centralizer or torus step, and the reductive matrix and host assertions
remain separate obligations.
