# Galois equivariance of geometric reciprocity on a finite Galois Weil kernel

Author: Worker 1839. This is a derived construction and theorem unit for task
`37d6d58f-e378-4630-8a8c-0f3d7212a970`. All declarations are in
`Langlands.Weil.Local`. It specializes the generic conjugation theorem
`LocalClassField.WeilReciprocityTransport.reciprocity_conjugation` of
`Langlands.ClassFieldTheory.Local.WeilReciprocityConjugation` (Worker 1556) to
the actual finite Galois quotient of `Langlands.Weil.Local.FiniteGaloisQuotient`
and the conjugation `finiteGaloisWeilConjugation` of
`Langlands.Weil.Local.FiniteGaloisReciprocity` (both Worker 1556). It discharges
every explicit hypothesis of that generic theorem.

## Setting

Fix a prime `p`, p-adic fields `F : PadicField.{u} p` and `E : PadicField.{v} p`,
an embedding `f : F.Carrier →ₐ[Padic p] E.Carrier`, and
`hGal : IsGalois F.Carrier E.Carrier` for the algebra structure
`extensionAlgebra F E f`. Write `ε = extensionClosureEquiv F E f` for the chosen
ring isomorphism of algebraic closures `\bar F ≃ \bar E`. For
`g : localWeilGroup F`, write `G = localProjection F g`, an automorphism of
`\bar F`, and `σ_g = finiteGaloisQuotient F E f hGal g` in `Gal(E/F)`. Write
`c_g = finiteGaloisWeilConjugation F E f hGal g`. It is the automorphism of the
actual Weil group `W_E` that corresponds to conjugation by `g` on the image of
`extensionWeilMap F E f`.

## Closure automorphism

`closureConjugation F E f g` is the ring automorphism `θ_g = ε ∘ G ∘ ε⁻¹` of
`\bar E`. The following lemmas describe it.

- `closureConjugation_apply` states `θ_g (ε x) = ε (G x)`.
- `closureConjugation_symm_apply` states `θ_g⁻¹ (ε x) = ε (G⁻¹ x)`.
- `closureConjugation_algebraMap` proves that on `E` the automorphism is
  `σ_g`: `θ_g (algebraMap E \bar E x) = algebraMap E \bar E (σ_g x)`. The proof
  writes `algebraMap E \bar E x` as `ε` of `extensionFieldEmbedding F E f x`. It
  then uses the published action formula `finiteGaloisQuotient_apply`, which
  says that `σ_g` acts on `E` through this embedding as `G`.

`localProjection_finiteGaloisWeilConjugation` proves that for every
`w : localWeilGroup E` and every `y` in `\bar E`

`localProjection E (c_g w) y = θ_g (localProjection E w (θ_g⁻¹ y))`.

To prove it, write `y = ε x`. The published `extensionClosureLift_galoisMap`
evaluates a Galois element of `E` on `ε x` through `extensionGaloisMap F E f`.
The published identity `extensionWeilMap (c_g w) = g * extensionWeilMap w * g⁻¹`
and `localProjection_extensionWeilMap` give
`extensionGaloisMap (localProjection E (c_g w)) = G * extensionGaloisMap (localProjection E w) * G⁻¹`.
Evaluate this at `x` and apply `closureConjugation_apply` and
`extensionClosureLift_galoisMap` once more. This gives the formula.
`localProjection_finiteGaloisWeilConjugation_closure` restates it in the form
`localProjection E (c_g w) (θ_g x) = θ_g (localProjection E w x)`, which is the
hypothesis `hc` of the generic theorem.

## Base automorphism

`baseConjugation F E f hGal g` is `σ_g` as a ring automorphism of `E`.

- `baseConjugation_compatible` is the algebra-map square
  `algebraMap ∘ σ_g = θ_g ∘ algebraMap` required by `FiniteArtinTransport`.
- `padicGaloisEquiv F E f hGal g` is `σ_g` restricted to scalars `Padic p`, using
  the published `extensionAlgebra_isScalarTower`.
- `continuous_baseConjugation` and `continuous_baseConjugation_symm` give
  continuity of `σ_g` and `σ_g⁻¹` for `E.canonicalTopologicalData.topology`.
  The proofs apply the published spectral-norm isometry `extension_isometry`
  to `padicGaloisEquiv` and to its inverse. The canonical topology is the one
  given by that norm.
- `orderHom_baseConjugation` proves that `σ_g` preserves the canonical integer
  order of units. This is the published `PadicField.CanonicalTransport.ord_map`
  for the `Padic p`-algebra automorphism `padicGaloisEquiv F E f hGal g`.

## Equivariance

`reciprocityUnits_finiteGaloisWeilConjugation` takes
`e : LocalFactor.RankOne.ReciprocityCandidate E` with
`GeometricWeilReciprocityRelation E E.canonicalTopologicalData e`, and states for
all `g` and `w`

`reciprocityUnits E e (c_g w) = Units.mapEquiv σ_g (reciprocityUnits E e w)`.

That is, `e(g w g⁻¹) = σ_g(e(w))`. The proof applies
`WeilReciprocityTransport.reciprocity_conjugation` with base automorphism
`σ_g`, closure automorphism `θ_g` and Weil automorphism `c_g`. The hypotheses
are discharged as follows.

- The compatible square is `baseConjugation_compatible`.
- The projection compatibility is `localProjection_finiteGaloisWeilConjugation_closure`.
- Continuity of `σ_g` and `σ_g⁻¹` is given by the two continuity lemmas above.
- Order preservation is `orderHom_baseConjugation`.
- Degree preservation is the published `localDegree_finiteGaloisWeilConjugation`.
- The local candidate relation of `e` is the pair `⟨he.1, he.2.1⟩`: the
  geometric order law and the profinite norm-residue relation contained in
  `GeometricWeilReciprocityRelation`. The residue-normalization clause is not
  used.

`smul_units_val` records that the action of `Gal(E/F)` on `Eˣ`, found by
instance search, acts on the underlying field element.

`finiteGaloisKernelReciprocity_conjugateKernel` is the kernel form. For
`x : localWeilGroup F` and `n` in the kernel of the finite Galois quotient,

`finiteGaloisKernelReciprocity F E f hGal e (conjugateKernel q x n) = q x • finiteGaloisKernelReciprocity F E f hGal e n`,

where `q = finiteGaloisQuotient F E f hGal`. This is exactly the equivariance
premise `hr` of `GroupExtensionPushout.Section.cocycle` and
`Section.toContinuousMonoidHom` in `Langlands.GroupTheory.ExtensionPushout`. To
prove it, write `n = j y`, where `j = finiteGaloisQuotientKernelEquiv`. Then
`conjugateKernel q x (j y) = j (c_x y)` by
`extensionWeilMap_finiteGaloisWeilConjugation`. Both sides reduce to inverse
reciprocity values by `finiteGaloisKernelReciprocity_apply`, and the previous
theorem applies. The Galois automorphism commutes with inversion.

## Scope and provenance

Provenance is derived. The unit composes published definitions and theorems and
the cited helper modules. Classically, this is the Galois compatibility of local
reciprocity with conjugation, Tate's condition (W2) of the definition of a Weil
group (Tate 1979, *Number theoretic background*, (1.1), printed pp.3–4). Nothing
here relies on that source: the proof is the uniqueness-transport argument
described above.

This unit does not construct a map into `CompletionClassExtension`. It does not
identify the class of the resulting factor cocycle with a fundamental class.
Those remain obligations of the host task
`LocalWeilClassMapExistenceStatement`.
