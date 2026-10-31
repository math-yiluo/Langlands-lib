# Natural and conjugate central Lie eigensubsheaves

This module constructs actual eigensubsheaves of the relative Lie sheaf,
using the natural and conjugate imaginary-field characters appearing in
Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.89–90 / PDF pp.97–98.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The construction here is an internal eigensubsheaf prerequisite for
comparison with the source's tensor factors.

The source's imaginary quadratic field `E` is called `L`, its CM field
`F` is called `K`, and its central division algebra `B` is called `A`
here. The abelian scheme is called `B` in Lean. The construction needs
only a CM number field `L`, a number field `K` with an `L`-algebra
structure, a rational algebra `A` with a central `K`-algebra structure,
an actual `K`-scheme `s : S ⟶ Spec K`, an actual abelian scheme `B/S`,
and an algebra homomorphism `i : A →ₐ[ℚ] End0 B`. It does not require
faithfulness, the division-algebra condition, quadratic degree, or a
signature. The original Harris data specialize these parameters.

`imaginaryLieAction` differentiates the actual rational action along
`L → K → A`. It is an actual ring homomorphism into endomorphisms of
`B.Lie`. `imaginaryLieCharacter` is the actual structure character
`L → K → Γ(S, ⊤)` when `conjugate = false`; for `true`, it is
precomposed with Mathlib's actual CM complex conjugation on `L`.
`imaginaryLieCharacter_restrict` identifies the restricted scalar with
the actual natural or conjugate structure section on every open.

`lieEigensheaf` uses the actual simultaneous scalar eigensubsheaf
construction. Its sections on `U` consist exactly of those `x` such
that every `r : L` satisfies

```text
d(i(algebraMap K A (algebraMap L K r)))(x)
  = secHom s U (algebraMap L K (if conjugate then conj_L r else r)) • x.
```

Here `d` is the constructed rational Lie differential `lieMap0`.
`mem_lieEigenSections` proves this exact formula, and `lieEigensheafι`
is the actual inclusion monomorphism.

`imaginaryLieAction_commutes` derives commutation with the full `A`
action from centrality of `algebraMap K A`, then maps that equality
through the actual Lie action. It respects the convention
`f * g = g ≫ f` for categorical endomorphisms.
`lieEigensheafAction` therefore constructs the full ring action on
each eigensubsheaf, and its inclusion is equivariant.

For any actual rational homomorphism intertwining the `A` actions,
`lieEigensheafMap` restricts its actual Lie differential to each
eigensubsheaf. The section formula, inclusion square, identity and
composition laws, and intertwining of the full restricted `A` actions
are proved. `lieEigensheafIso` applies this construction to an actual
equivariant rational isomorphism, including its rational inverse; it
constructs an actual isomorphism of module sheaves. No separate Lie
isomorphism is assumed.

The source defines `Lie⁺` and `Lie⁻` as tensor factors over
`O_S ⊗_ℚ L`, with the natural and conjugate structure maps. This
module constructs the corresponding eigencondition subsheaves, but
does not yet identify them with those tensor factors. It asserts no
direct-sum decomposition, local freeness, prescribed rank, equivalence
with the source's compatibility or trace conditions, or arbitrary
base-change comparison. Those require further proofs. In particular,
the eigensubsheaf is not asserted to be the completed source `Lie⁺`
construction.
