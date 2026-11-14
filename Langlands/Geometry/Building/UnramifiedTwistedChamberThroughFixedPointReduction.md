# Reduction of twisted-stable chambers to one topological generator

This module proves a conditional reduction to
`UnramifiedTwistedChamberThroughFixedPointStatement.{u}` at arbitrary universe `u`. It does
not prove the unconditional target: the single-generator statement
`UnramifiedTwistedGeneratorChamberStatement.{u}` (the residue-field and Lang's-theorem core)
remains an outstanding input.

## The statement

`UnramifiedTwistedChamberThroughFixedPointReductionStatement.{u}` is the Prop-valued
definition

`UnramifiedTwistedGeneratorChamberStatement.{u} →
UnramifiedTwistedChamberThroughFixedPointStatement.{u}`.

Both statements have the same data and hypotheses (a connected reductive `F`-group `G` over a
nonarchimedean local field `F`, `K = inertiaFixedField F` its maximal unramified extension,
`Γ = Aut(K/F)`, a torus `T → G` whose scalar extension is maximal `K`-split, the
`Γ`-stable apartment class `D` with centralizer datum `C`, axiom V 6, a crossed homomorphism
`c : Γ → G(K)` trivial on the fixing subgroup of a finite subextension, and a point `y` of the
reduced building fixed by every twisted action `z ↦ c σ • action σ z`). The hypothesis gives a
`φ ∈ Γ` whose integer powers meet every coset of the fixing subgroup of every finite-dimensional
intermediate field, and a translated chamber `Y = g · facet(x₀)` through `y` that is stable under
the twisted action of `φ` alone. The conclusion asks for such a chamber stable under the twisted
action of every `σ ∈ Γ` and states that it is a chamber (`IsChamber`).

The theorem `unramifiedTwistedChamberThroughFixedPointReduction` proves the reduction
statement; it is `unramifiedTwistedChamberThroughFixedPoint_of_generator`.

## Proof

The chamber `Y`, the element `g`, and the points `x₀` and `x` are those of the hypothesis. The
`IsChamber` clause and the presentation clauses are immediate. The work is to upgrade stability
under `φ` to stability under every `σ`. Write `K/F` for `inertiaFixedField F` over `F`.

**Openness.** The main step is to find a finite-dimensional intermediate field `E` whose fixing
subgroup fixes `Y` pointwise for the twisted action. Points of `Y` have the form
`g • apartmentMap w`, and
`c ρ • action ρ (g • apartmentMap w) = c ρ • ρ(g) • apartmentMap (ρ w)`
(`action_smul`, `action_apartmentMap`; lemma `twisted_smul_apartmentMap`). So it suffices that
the fixing subgroup of `E` fixes `c`, fixes `g`, and acts trivially on the apartment. Take `E`
to be the compositum `E_c ⊔ E_χ ⊔ E_g` of three finite-dimensional intermediate fields, which
is finite-dimensional (`IntermediateField.finiteDimensional_sup`):

- `E_c` is the field in the hypothesis on `c`, so `c ρ = 1` on its fixing subgroup.
- `E_g` comes from `exists_finite_fixing_rationalPoints`. For finitely many `K`-points of the
  scalar extension of an affine `k`-group of finite type, where `K/k` is algebraic, there is a
  finite-dimensional intermediate field whose fixing subgroup fixes them under
  `rationalConjugate`. The proof sends each point to an algebra homomorphism from the
  finite-type coordinate ring (`GaloisPoint.coordinates`, `baseChangeCoeffEquiv`). It then
  applies `IdentityComponent.exists_finite_fixing_algHoms` and transports back with
  `baseChangeCoeffEquiv_rationalConjugate` and `GaloisPoint.coordinates_conjugate`. The
  finite-type instance comes from smoothness of `G` (`hG.smooth`).
- `E_χ` comes from `exists_finite_fixing_characters`: the fixing subgroup of some
  finite-dimensional intermediate field acts trivially on the character lattice `X^*(T_K)`
  through `characterLattice.galoisRepresentation`. Its hypotheses are that `T_K` is split
  (`hiT.isSplitSubtorus.1`), that `T_K → G_K` is a monomorphism, and that there is `b ∈ Kˣ` that
  is fixed by every automorphism and is not a root of unity. Here `b` is
  `MaximalUnramified.baseUniformizerUnit F`, the image of a uniformizer of `F`. It is fixed
  because automorphisms fix `F` (`baseUniformizerUnit_fixed`). It is not torsion because its
  integer order is `1` (`orderUnits_baseUniformizerUnit`; `baseUniformizerUnit_zpow_eq_one`).
  The cocharacter lattice is finitely generated. For each generator `ν` push the cocharacter
  point `ν(b) ∈ T(K)` into `G(K)`, and take the field of `exists_finite_fixing_rationalPoints`
  for these finitely many points. If `ρ` fixes `ν(b)` in `G(K)`, then it fixes `ν(b)` in `T(K)`
  (`rationalConjugate_map` and injectivity of the monomorphism on points; `map_injective`,
  `rationalConjugate_eq_of_map`). Then `rationalCharacterEval_galois` and
  `rationalCharacterEval_cocharacterPoints` give `b ^ ⟨ρ χ, ν⟩ = b ^ ⟨χ, ν⟩`. As `b` is not
  torsion, `⟨ρ χ - χ, ν⟩ = 0` (`latticePairing_galois_sub_eq_zero`). This holds on generators,
  so `latticePairing (ρ χ - χ) = 0`, and the perfect pairing
  (`hT.isPerfPair_latticePairing`) gives `ρ χ = χ`.

**Trivial action on the apartment.** Let `ρ` fix every character and let `x₁` be a point of
the apartment fixed by every automorphism. The Library theorem
`unramifiedGaloisFixedApartment` supplies `x₁`, and `KPApartmentData.Apartment.ext` turns its
statement into fixedness under `KPApartmentData.galoisAction`. Then `ρ` acts trivially on the
reduced translation space (`galoisTranslationAction_eq_self`): if `ρ⁻¹` fixes every relative
root `a`, then for a representative `w` the difference `galoisCocharacterAction ρ w - w` pairs
to zero with every root (`eval_galoisCocharacterAction_right`), so it lies in the root
annihilator (`mem_rootAnnihilator`) and its class vanishes (`galoisTranslationAction_mk`). The
hypothesis on `ρ⁻¹` holds because the fixing subgroup of `E_χ` is a subgroup, so `ρ⁻¹` also
fixes every character. Writing `z = (z -ᵥ x₁) +ᵥ x₁` and using `KPApartmentData.galoisAction_vadd` gives
`ρ z = z` (`galoisAction_eq_self`, `semilinearData_apartment_eq_self`). The apartment action of
`semilinearData` is by definition `KPApartmentData.galoisAction`.

**Density.** `A.twistedAction c hc : Γ →* Equiv.Perm` is the twisted action as a group
homomorphism; it uses the crossed-homomorphism identity `hc` (`twistedAction_apply`). The set
stabilizer `setStabilizer τ Y = {σ | τ σ '' Y = Y}` of a homomorphism `τ : Γ →* Perm X` is a
subgroup. It contains `φ` by hypothesis, and it contains the fixing subgroup of `E` by the
openness step. For any `σ`, the generator hypothesis applied to `E` gives `n` with
`σ⁻¹ φ ^ n` in the fixing subgroup, and `σ = φ ^ n (σ⁻¹ φ ^ n)⁻¹` lies in the stabilizer
(`twisted_image_eq_of_generator`, `twisted_image_eq_of_presentation`).

The lemma `twisted_image_eq_of_generator_data` assembles these steps for fixed data. The final
theorem introduces the target's data, derives the affine, monomorphism and smoothness
instances from the hypotheses, applies the hypothesis `UnramifiedTwistedGeneratorChamberStatement`
to the same data, and returns its chamber with the stability proved above. The `IsChamber`
clause is `isChamber_of_presentation`: by the definition of
`IntegerValuationBuildingData.IsChamber`, `g · facet(x₀)` with `x₀` on no affine root
hyperplane is a chamber.

## Auxiliary declarations

All auxiliary declarations live in the namespace
`Langlands.Geometry.Building.TwistedGeneratorReduction`. They are
`exists_finite_fixing_rationalPoints`, `map_injective`, `rationalConjugate_eq_of_map`,
`latticePairing_galois_sub_eq_zero`, `exists_finite_fixing_characters`,
`galoisTranslationAction_eq_self`, `galoisAction_eq_self`, `setStabilizer`,
`mem_setStabilizer`, `twisted_smul_apartmentMap`, `twisted_image_eq_of_generator`,
`twisted_image_eq_of_presentation`, `isChamber_of_presentation`, `baseUniformizerUnit_fixed`,
`baseUniformizerUnit_zpow_eq_one`, `semilinearData_apartment_eq_self` and
`twisted_image_eq_of_generator_data`. Their statements are those described above. The general
lemmas are stated for an arbitrary field extension `K/k` (algebraic where needed). The module
also has a private instance `extendedAffineHom` for the affine structure map of `G_K`, built
from the affine structure map of `G`.

## Provenance

This is an internal reduction. Mathematically it is the standard fact used implicitly in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 9.10.1 (proof of
(4) ⇒ (1)) and the proof of Theorem 10.6.1: the action of `Γ = Gal(K/F)` on a chamber factors
through a finite quotient, and `Γ` is topologically generated by a Frobenius element, so an
`f`-rational Borel subgroup (stability under Frobenius) yields a `Γ`-stable chamber. The Lean
proof does not use a Frobenius element or the Krull topology. It uses only the coset property
of `φ` in the hypothesis and the finite-subextension fixing subgroups constructed above. It does
not prove the hypothesis `UnramifiedTwistedGeneratorChamberStatement`, nor any
fixed-point-existence, metric or cocycle-vanishing statement.
