# Selected conjugacy witnesses through a common target

This internal construction composes actual conjugacy witnesses for group
schemes over an arbitrary base scheme `S : Scheme.{u}`. It imports only
`Langlands.GroupScheme.InnerAutomorphismHom` and imposes no field, smoothness,
connectedness, closedness or Borel hypotheses.

Let `i : B ⟶ G`, `i' : B' ⟶ G` and `j : C ⟶ G` be group-scheme morphisms.
Suppose base points `g, h` of `G` and isomorphisms `φ : B ≅ C`,
`ψ : B' ≅ C` satisfy

```text
i  ≫ (G.innerIso g).hom = φ.hom ≫ j,
i' ≫ (G.innerIso h).hom = ψ.hom ≫ j.
```

The theorem `comp_innerIso_hom_of_common_target` proves the exact equation

```text
i ≫ (G.innerIso (h⁻¹ * g)).hom = (φ ≪≫ ψ.symm).hom ≫ i'.
```

The proof first inserts `ψ.inv ≫ ψ.hom` into `j`, replaces `ψ.hom ≫ j`
using the second input equation, and cancels the inner automorphism with its
inverse. This gives `j ≫ (G.innerIso h).inv = ψ.inv ≫ i'`.
The published multiplication and inversion laws for `innerIso`, followed by
the first input equation and categorical associativity, give the result.
The multiplication order follows `innerIso_mul_hom`, whose right-hand side
applies the right factor's inner automorphism first.

The definition `conjugatingDataOfCommonTarget` takes the two selected witnesses
as dependent pairs, each containing a base point and an isomorphism together
with its embedding equation. It returns a dependent pair of the same shape
for `i` and `i'`. Its point is definitionally `d'.1⁻¹ * d.1`; its isomorphism is
definitionally `d.2.1 ≪≫ d'.2.1.symm`. The lemmas
`conjugatingDataOfCommonTarget_point`, `conjugatingDataOfCommonTarget_iso`
and `conjugatingDataOfCommonTarget_spec` expose these projections and the
retained equation.

This is derived algebraic content designed by Worker 1293 and implemented by
Worker 135. Its provenance is the published categorical inner-automorphism
laws; it invokes no external structural theorem. The dependent-pair shape
supports subsequent assembly of the Borel conjugacy theorem from separately
constructed witnesses to a common Borel. This unit does not construct those
input witnesses or prove the full Borel conjugacy statement.
