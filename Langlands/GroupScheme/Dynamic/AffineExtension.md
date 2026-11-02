# Orbit extensions over affine test schemes

This module is a helper for the representability of dynamic subgroups
([`Representability`](Representability.md)). Fix a base scheme `S` and a morphism
`f : Spec A ⟶ S`. The module compares two ways of extending a morphism from `𝔾_m` to `𝔸¹`:

- along `Spec A ×_S 𝔾_{m,S} ⊆ Spec A ×_S 𝔸¹_S`. This is the setting of the published dynamic
  notions (`Langlands.GroupScheme.Dynamic.Basic`): orbit extensions and limits.
- along `Spec A[X, X⁻¹] ⊆ Spec A[X]`. Here a morphism into an affine scheme is a ring map.

Over affine test schemes the two kinds of extension correspond. This is what turns
"the limit exists" into a condition on ring maps. The module builds on the objects of
[`Uniqueness`](Uniqueness.md): `polynomialScheme f`, `polynomialPoint f`,
`polynomialPointInv f`, `laurentScheme f`, `laurentInclusion f`, `laurentUnit f`,
`polynomialC A`, `polynomialToLaurent A`, `polynomialSections f` and `polynomialProj f`.

## Sources and provenance

This is internal infrastructure. It formalizes the first sentence of the proof of
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), Lemma 2.1.4 (printed p. 49,
PDF p. 75): "the `R`-map `α_v` corresponds to the `k`-algebra map `k[V] → R[t, 1/t]` … `α_v`
extends to an `R`-morphism `𝔸¹_R → V_R` if and only if `α_v^*` has image contained in the
subring `R[t] ⊆ R[t, 1/t]`." The source takes `𝔾_{m,R}` and `𝔸¹_R` to be `Spec R[t, 1/t]` and
`Spec R[t]`. In the Library, `𝔾_{m,S}` and `𝔸¹_S` are group and ring objects over a general
base `S`, and the dynamic notions use the fibre products `T ×_S 𝔾_{m,S}` and `T ×_S 𝔸¹_S`.
This module proves the comparison needed to move between the two descriptions.

## The polynomial point is an isomorphism

- `specHomEquiv_polynomialPointInvLeft`: the ring map of `polynomialPointInvLeft f` is
  `polynomialSections f`.
- `polynomialPoint_comp_polynomialPointInv`: `polynomialPoint f ≫ polynomialPointInv f = 𝟙`.
  Together with the published `polynomialPointInv_comp_polynomialPoint`, this shows that
  `polynomialPoint f : Spec A[X] ⟶ Spec A ×_S 𝔸¹_S` is an isomorphism. Proof: both sides are
  morphisms into the affine scheme `Spec A[X]`, so it suffices to compare ring maps
  `A[X] ⟶ Γ(Spec A[X])` (`Gm.specHomEquiv`). They agree on constants, by the first component
  of `polynomialPoint`, and on `X`, by its second component (`Polynomial.ringHom_ext'`).

## The Laurent point

- `laurentPoint f : Spec A[X, X⁻¹] ⟶ Spec A ×_S 𝔾_{m,S}` is the point whose first component is
  the projection to `Spec A` and whose `𝔾_m`-component is the unit `X`.
- `laurentInclusion_comp_polynomialPoint`: `laurentInclusion f ≫ polynomialPoint f` equals
  `laurentPoint f` followed by the inclusion `Spec A ×_S 𝔾_{m,S} ⊆ Spec A ×_S 𝔸¹_S`. This is
  the published `laurentInclusion_polynomialPoint`, restated with `laurentPoint`.
- `laurentSections f : A[X, X⁻¹] ⟶ Γ(Spec A ×_S 𝔾_{m,S})` sends `a` to its pullback along the
  first projection and `X` to the coordinate unit (`LaurentPolynomial.eval₂`).
  `laurentPointInvLeft f` is the corresponding morphism `Spec A ×_S 𝔾_{m,S} ⟶ Spec A[X, X⁻¹]`,
  and `laurentPointInv f` is the same morphism over `S`. `laurentPointInvLeft_comp` shows it is
  compatible with the projections to `Spec A`.
- `laurentPointInv_comp_laurentPoint`: `laurentPointInv f ≫ laurentPoint f = 𝟙`. So
  `laurentPoint f` is a split epimorphism. The module does not prove that it is an isomorphism;
  the splitting is all that is used.

## Moving extensions between the two settings

Let `Y` be a scheme over `S` and `o : Spec A ×_S 𝔾_{m,S} ⟶ Y`.

- `laurentInclusion_comp_of_whiskerLeft`: if `e : Spec A ×_S 𝔸¹_S ⟶ Y` extends `o`, then
  `polynomialPoint f ≫ e : Spec A[X] ⟶ Y` extends `laurentPoint f ≫ o` along
  `Spec A[X, X⁻¹] ⊆ Spec A[X]`.
- `whiskerLeft_comp_of_laurentInclusion`: conversely, if `e : Spec A[X] ⟶ Y` extends
  `laurentPoint f ≫ o` along `Spec A[X, X⁻¹] ⊆ Spec A[X]`, then `polynomialPointInv f ≫ e`
  extends `o`. The proof uses the splitting `laurentPointInv f` and
  `polynomialPoint_comp_polynomialPointInv`.

## Evaluation at zero

- `polynomialEvalZero A : A[X] ⟶ A` is evaluation at `0`. `polynomialC_comp_polynomialEvalZero`
  says that it is a retraction of `polynomialC A`.
- `polynomialZero f : Spec A ⟶ Spec A[X]` (over `S`) is `Spec` of evaluation at `0`.
- `polynomialZero_comp_polynomialPoint`: `polynomialZero f ≫ polynomialPoint f` is the zero
  section `(𝟙, 0)` of `Spec A ×_S 𝔸¹_S`.
- `evalZero_polynomialPointInv`: for `e : Spec A[X] ⟶ Y`, the value at zero
  (`Dynamic.evalZero`) of `polynomialPointInv f ≫ e` is `polynomialZero f ≫ e`. This is how
  limits are read off from ring maps.

## Naturality in the coefficients

Let `ψ : A' ⟶ A` be a ring map.

- `laurentCoeffMap ψ : A'[X, X⁻¹] ⟶ A[X, X⁻¹]` applies `ψ` to coefficients
  (`AddMonoidAlgebra.mapRingHom`). `polynomialC_comp_polynomialToLaurent_comp_laurentCoeffMap`
  and `laurentCoeffMap_T` describe it on constants and on the monomials `T m`.
- `laurentMap a : Spec A[X, X⁻¹] ⟶ Spec A'[X, X⁻¹]`, for a morphism `a : Spec A ⟶ Spec A'` over
  `S` (with `f : Spec A ⟶ S` and `g : Spec A' ⟶ S`), is `Spec` of `laurentCoeffMap` applied to
  the ring map of `a`.
- `laurentPoint_comp_whiskerRight`: `laurentPoint f ≫ (a × 𝔾_m) = laurentMap a ≫ laurentPoint g`.
  This lets every orbit map be computed from the orbit map of a universal point.
