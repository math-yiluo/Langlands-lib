# Reduction of the twisted residue quotient to apartment points

This module is internal and derived from published Library results. It reduces the
published, unproved `UnramifiedTwistedResidueQuotientStatement` to the case of a
twisted-fixed point that lies on the standard apartment. It proves that reduction
completely. It does not prove the apartment case, and it attributes nothing to a
numbered result of the literature. This is the usual "without loss of generality"
step: replace the cocycle by a cohomologous one and conjugate everything by a group
element.

Notation: F is a nonarchimedean local field in universe u, K = `inertiaFixedField F`,
Γ = Aut(K/F) (written `K ≃ₐ[F] K`), G is an affine group scheme over F, G_K =
`baseChanged F K G` and G(K) = `rationalPoints G_K`. For σ ∈ Γ and g ∈ G(K), σ(g)
means `rationalConjugate F K G σ g`. As in the target module, a private instance
(`extendedAffineHom`) supplies `IsAffineHom` for the structure morphism of G_K.

## The conclusion predicate

`TwistedResidueQuotientTransport.Conclusion B φ cφ y` takes
`B : MaximalUnramified.BuildingData F G_K`, φ ∈ Γ, an element cφ ∈ G(K) and a point y of
`B.ReducedBuilding`. Its body is the conclusion of
`UnramifiedTwistedResidueQuotientStatement`, copied verbatim, with the building
`UnramifiedBuildingDescent.buildingData …` replaced by B and the cocycle value `c φ`
replaced by cφ. The same three residue-field `letI` declarations come first: κ =
`𝓀[F]` is finite through `Fintype.ofFinite`, and Ω = `IsLocalRing.ResidueField
(fixedFieldIntegers F)` gets the algebra structure `(residueToFixedField F).toAlgebra`
and the algebraic-closure structure `fixedFieldResidueIsAlgClosure F`. The body then
says that there exist:

1. a group scheme R over Spec κ with `IsConnectedReductive R`;
2. a subgroup P of G(K) with P ≤ `B.fixer y`;
3. a surjective homomorphism q from P to the Ω-points of the base change of R to Ω;
4. a map θP : P → P with (θP g : G(K)) = cφ · φ(g) · cφ⁻¹;
5. q (θP g) = `descentBasePoint … R (q g)` (canonical Frobenius descent along
   `FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω`);
6. for every Y with `B.HasChamberClosurePresentation Y y` and every g ∈ P with q g = 1,
   (g • ·) '' Y = Y;
7. for any two such Y, Y', some h ∈ P has Y' = (h • ·) '' Y.

## Transport lemmas

* `image_smul_image_smul`: translating a set of the reduced building by a and then by
  b is the same as translating by b * a.
* `Conclusion.smul`. Let g₀ ∈ G(K). If `Conclusion B φ (g₀⁻¹ * cφ * φ(g₀)) y` holds, then
  `Conclusion B φ cφ (g₀ • y)` holds. Proof: keep R. Take P' to be the image of P under
  conjugation by g₀, let e : P ≃* P' be `(MulAut.conj g₀).subgroupMap P`, and set
  q' = q ∘ e⁻¹ and θ' = e ∘ θP ∘ e⁻¹. Then:
  - P' fixes g₀ • y.
  - q' is surjective.
  - The twist identity follows from g₀ · (g₀⁻¹ cφ φ(g₀)) φ(h) (g₀⁻¹ cφ φ(g₀))⁻¹ · g₀⁻¹
    = cφ · φ(g₀ h g₀⁻¹) · cφ⁻¹, since φ acts by a group automorphism.
  - The Frobenius identity is unchanged, because e⁻¹ ∘ e = id.
  - For kernel fixation and transitivity, a chamber Y is presented through g₀ • y
    exactly when g₀⁻¹ • Y is presented through y (published
    `HasChamberClosurePresentation.smul`). Each element of P' acts as g₀ h g₀⁻¹.

## Cohomologous cocycles

Let c : Γ → G(K) and g₀ ∈ G(K).

* `twistCocycle c g₀` is the function σ ↦ g₀⁻¹ · c σ · σ(g₀).
* `twistCocycle_mul`: if c satisfies c(στ) = c σ · σ(c τ), then so does
  `twistCocycle c g₀`. The proof uses `rationalConjugate_mul` and group algebra.
* `exists_twistCocycle_eq_one`: assume G is locally of finite type over F, and c is
  trivial on the fixing subgroup of a finite subextension E. Then `twistCocycle c g₀` is
  trivial on the fixing subgroup of a finite subextension, namely E ⊔ E', where E' is
  given by the published `TwistedGeneratorReduction.exists_finite_fixing_rationalPoints`
  so that its fixing subgroup fixes g₀.
* `twistCocycle_smul_action`: for a `MaximalUnramified.SemilinearApartmentData A` of B,
  if c σ • A.action σ (g₀ • z) = g₀ • z, then
  `twistCocycle c g₀ σ` • A.action σ z = z. The proof uses the published semilinearity
  `SemilinearApartmentData.action_smul`.

## Statements

`UnramifiedTwistedResidueQuotientApartmentStatement.{u}` copies the binder telescope of
`UnramifiedTwistedResidueQuotientStatement` verbatim, from F through the cocycle and
finiteness hypotheses on c. Then, in place of an arbitrary twisted-fixed point y, it takes an
apartment point x of `B = UnramifiedBuildingDescent.buildingData iT _ hiT D C h6` with
c σ • A.action σ (B.apartmentMap x) = B.apartmentMap x for every σ ∈ Γ, where
A = `UnramifiedBuildingDescent.semilinearData iT _ hiT C h6 hD`. For every φ ∈ Γ satisfying
the same Frobenius-lift hypothesis as in the target, it concludes
`Conclusion B φ (c φ) (B.apartmentMap x)`. That is the target's conclusion at the point
`B.apartmentMap x`.

`UnramifiedTwistedResidueQuotientApartmentReductionStatement.{u}` is the implication
`UnramifiedTwistedResidueQuotientApartmentStatement.{u} →
UnramifiedTwistedResidueQuotientStatement.{u}`.

`unramifiedTwistedResidueQuotientApartmentReduction` proves this implication. Given the
target data and a twisted-fixed point y, the published
`IntegerValuationBuildingData.exists_smul_apartmentMap` writes y = g₀ • B.apartmentMap x.
The apartment statement is then applied to the cocycle `twistCocycle c g₀`. Its
hypotheses come from `twistCocycle_mul`, from `exists_twistCocycle_eq_one` (G is smooth
since it is connected reductive, hence locally of finite type) and from
`twistCocycle_smul_action`. The value of `twistCocycle c g₀` at φ is
g₀⁻¹ · c φ · φ(g₀), so `Conclusion.smul` turns the resulting conclusion at
B.apartmentMap x into the target conclusion at y. The only axioms are propext,
Classical.choice and Quot.sound.

## Role and limits

This is step (i) of a proof of `UnramifiedTwistedResidueQuotientStatement`.
It lets the remaining construction work at an apartment point, where the parahoric
model statement `UnramifiedParahoricModelStatement` and the kernel-fixation module
`UnramifiedRadicalChamberFixation` apply to `apartmentMap '' {x}`. The module constructs
no residue quotient or Frobenius descent, and it does not prove the apartment statement.
