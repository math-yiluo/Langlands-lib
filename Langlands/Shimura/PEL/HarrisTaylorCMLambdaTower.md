# The λ-adic cohomology of the CM tower with coefficients W: level change, the finite-adelic action, isotypic parts and their Galois representations

This module defines the maps induced by the transporters of small CM levels
on the Library's `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` with Harris's
coefficient systems `W`. It also defines the tower cohomology
`H^d(S, W)_λ = colim_U H^d(S_U ×_F F̄, W)_λ` as a smooth representation of the
finite-adelic similitude group `GG(A_f)` over `K_λ`, with the commuting action
of `Gal(F̄/F)`, and the action of the level Hecke algebra on its fixed vectors.
It states the fixed-vector comparison of Harris–Taylor as a proposition. For a
representation `τ` of `GG(A_f)` over an extension field `M` of `K_λ`, it
defines the isotypic part, its fixed vectors at a level and the two
multiplicity spaces. Under explicit finiteness, continuity and fixed-vector
hypotheses, these become continuous Galois representations of `F` over `M`,
with Euler polynomials given by geometric Frobenius at unramified places.
All declarations are in namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5, printed p. 312, considers "the `JL(π_f)`-isotypic component of
`H^{n-1}(S_K(N), W)`, which we denote `H^{n-1}(S_K(N), W)[π]`", where
`JL(π_f)` is an irreducible admissible representation of `GG(A_f)` and `K(N)`
is a level. On printed p. 313 he considers `λ`-adic representations `σ` of
`Gal(F̄/F)` unramified at all but finitely many places, with local factor
(5.6) defined through the eigenvalues `β` of `σ(Fr_w)` for a geometric
Frobenius `Fr_w`. Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.2, printed p. 96, form the cohomology of the
tower as the colimit `H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)` over
sufficiently small levels, let `g ∈ G(A^∞)` act through the maps between
levels related by conjugation by `g`, and note that
`H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}` for `V ⊂ U`. On
printed p. 97 they conclude that `H^i(X, L_ξ)` is an admissible
`G(A^∞) × Gal(F^ac/F)`-module. Kottwitz (1992), *On the λ-adic
representations associated to some simple Shimura varieties*, §1, printed
p. 655, uses the Hecke multiplicity space
`W^i(π_f) = Hom_{H_K}(π_f^K, H^i(S_K, F))` with the commuting Galois action.

The Library already contains:

* the space `H^d(S_U ×_F F̄, W)_λ` at one small level `U`
  (`cmHarrisLambdaCohomology`);
* the same cohomology as a functor of scaled levels, whose morphisms are
  transporters together with a power of `ℓ` that makes the lattice maps
  integral (`cmHarrisScaledLambdaCohomology`);
* the identification of the two at every scaled level, with its laws
  (`HarrisTaylorCMScaledLambdaComparison`);
* the descent of such a functor to small levels by inverting `ℓ`
  (`HarrisTaylorCMScaledDescent`);
* generic towers, fixed vectors, Hecke modules, isotypic parts and their
  Galois representations for any level-trivial presheaf on the small CM levels
  (`HarrisTaylorCMSmallLevelGaloisTower`, `HarrisTaylorCMSmallLevelGaloisIsotypic`).

This module combines them. The transporter maps on the `ℓ`-component use the
algebraic representation `ρ` on Harris's lattices, rescaled by `ℓ^e`; dividing
by `ℓ^e` needs `ℓ` inverted, which holds in `K_λ`. The action of `g` on
`H^d(S, W)_λ` through this rescaled lattice map is a construction internal to
the Library. Harris (1999), Proposition 4.10, printed p. 311, states the
equivariance only away from `ℓ` and `p`, and none is attributed to him here.

The module proves no finiteness, continuity or unramifiedness of the
cohomology and does not prove the fixed-vector comparison. These are the
published propositions `CMHarrisLambdaCohomologyFiniteDimensional`,
`CMHarrisLambdaCohomologyContinuous` and `CMHarrisLambdaCohomologyUnramifiedAt`,
and the proposition `CMHarrisLambdaTowerFixedVectorComparison` stated here.
They are explicit hypotheses wherever they are used. The representation `τ`
is arbitrary; no irreducibility, admissibility or smoothness is assumed. No
statement of Harris, Harris–Taylor or Kottwitz is formalized as a theorem.

## Inputs

The section variables are those of the published
`HarrisTaylorCMLambdaCohomology`. They are the CM data `E`, `F`, `A`,
`D : CentralSimpleUnitaryData E F A n`, `L`, `C`, the conditional geometric
statements `preservation` … `htor`, the representability statement `q`, a
number field `K`, a finite place `p` of `ℚ`, a finite-dimensional `K`-vector
space `W` with an algebraic representation `ρ`, and the statements `existence`
and `geometry`. Further:

* `hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity … U.obj`, rigidity
  at every small level;
* `[∀ U, HasDerivedCategory (ModuleSheaf ((cmGeometricSchemeTower …).obj U) R)]`
  and `[HasDerivedCategory (ModuleCat R)]` for
  `R = HarrisCoefficientIntegers K p`;
* `l : FinitePlacesAbove K p`, a place `λ` of `K` above `p`, with completion
  `K_λ = FiniteCompletion K l.1`, and a degree `degree = d`.

Write `ℓ = harrisCoefficientPrime p` and `Γ = Field.absoluteGaloisGroup F`.
The published inputs are:

* `HarrisTaylorCMLambdaCohomology`: `cmHarrisLambdaCohomology … U ρ p existence
  geometry (hRigid U) l degree : Action (ModuleCat K_λ) Γ`, the space
  `H^d(S_U ×_F F̄, W)_λ` with its Galois action, and the propositions
  `CMHarrisLambdaCohomologyFiniteDimensional`,
  `CMHarrisLambdaCohomologyContinuous` and `CMHarrisLambdaCohomologyUnramifiedAt`.
* `HarrisTaylorCMScaledGaloisCohomology`: `cmHarrisScaledLambdaCohomology … l
  degree : (CMScaledLevel D ρ p)ᵒᵖ ⥤ Action (ModuleCat K_λ) Γ`, written `G`.
* `HarrisTaylorCMScaledLambdaComparison`: the isomorphisms
  `cmHarrisScaledLambdaComparison … l degree X : G(X) ≅ H^d(S_{X.level} ×_F F̄, W)_λ`,
  written `ψ X`, and the three laws `cmHarrisScaledLambdaComparison_raise`,
  `cmHarrisScaledLambdaComparison_shift` and
  `cmHarrisScaledLambdaComparison_levelTrivial`. These are the propositions
  `CMScaledTransportRaise D ρ p K_λ G O ψ`, `CMScaledTransportShift D ρ p G O ψ`
  and `CMScaledTransportLevelTrivial D ρ p G O ψ` of the descent module, for
  `O U = H^d(S_U ×_F F̄, W)_λ`.
* `HarrisTaylorCMScaledDescent`: for `hℓ : (ℓ : K_λ) ≠ 0`, `cmScaledDescent D ρ p
  hℓ hraise hshift : (SmallCMLevel D)ᵒᵖ ⥤ Action (ModuleCat K_λ) Γ`, with value
  `O U` at `U` and map `cmScaledDescentMap … b` at a transporter `b`, and
  `isLevelTrivial_cmScaledDescent`.
* `harrisCoefficientPrime_ne_zero_completion p l : (ℓ : K_λ) ≠ 0`.
* `HarrisTaylorCMSmallLevelGaloisTower` and
  `HarrisTaylorCMSmallLevelGaloisIsotypic`: for a level-trivial
  `H : (SmallCMLevel D)ᵒᵖ ⥤ Action (ModuleCat K_λ) Γ`, the tower `towerAction`,
  the fixed legs, `TowerFixedVectorComparison`, `towerHeckeModule`, and the
  isotypic and multiplicity spaces with their Galois representations.

## Declarations

Below, `…` stands for the explicit section arguments
`D C preservation … htor q p ρ existence geometry hRigid l degree`.

### Level change

* `cmHarrisLambdaLevelCohomology … : (SmallCMLevel D)ᵒᵖ ⥤ Action (ModuleCat K_λ) Γ`
  is `cmScaledDescent` applied to `harrisCoefficientPrime_ne_zero_completion p l`
  and the raise and shift laws of `ψ`. Write `H` for it.
* `cmHarrisLambdaLevelCohomology_obj`: `H(U)` is, by definition, the Library's
  `cmHarrisLambdaCohomology` at level `U` (`rfl`).
* `cmHarrisLambdaLevelCohomology_map`: for a transporter `b : V ⟶ U`, `H(b)` is
  `cmScaledDescentMap D ρ p K_λ G O ψ b`. That is
  `(ℓ^{e_b})⁻¹ • (ψ ⟨U, e_b⟩).inv ≫ G(f_b) ≫ (ψ ⟨V, 0⟩).hom`, where `e_b` is
  the least exponent for which `ℓ^{e_b} ρ(b)` maps Harris's lattice at `U` into
  the one at `V`, and `f_b : ⟨V, 0⟩ ⟶ ⟨U, e_b⟩` is the scaled morphism with
  transporter `b` (`rfl`). Since `H` is a functor, these maps compose, and the
  map of an identity is the identity. Since `H` takes values in
  `Action (ModuleCat K_λ) Γ`, each map commutes with `Gal(F̄/F)`.
* `isLevelTrivial_cmHarrisLambdaLevelCohomology`: `H` is level-trivial: a
  transporter from `U` to itself whose element lies in `U` acts by the
  identity. It is `isLevelTrivial_cmScaledDescent` with the level-trivial law
  of `ψ`.

### The tower cohomology and the finite-adelic action

* `cmHarrisLambdaTowerCohomology … : Action (SmoothRep K_λ GG(A_f)) Γ`, where
  `GG(A_f) = D.rationalInvolution.FiniteAdelicPoints`, is `towerAction H`. It is
  `H^d(S, W)_λ = colim_U H^d(S_U ×_F F̄, W)_λ`. It is a smooth representation of
  `GG(A_f)` (not of its opposite) over `K_λ`, with an action of `Γ` by
  `GG(A_f)`-equivariant maps. Being a representation, the action of `GG(A_f)` is
  an action of the group.
* `cmHarrisLambdaTowerCohomology_ρ_ι_apply`: `γ ∈ Γ` acts on the class of
  `x ∈ H(U)` as the class of `γ x`.
* `cmHarrisLambdaTowerCohomology_representation_ι_apply`: `g ∈ GG(A_f)` sends
  the class of `x ∈ H(U)` to the class at the conjugate level
  `restrictedConj … (op g⁻¹) U` of the image of `x` under the map of the
  transporter `restrictedConjArrow … (op g⁻¹) U`.
* `cmHarrisLambdaTowerCohomology_comm`: the actions of `γ ∈ Γ` and
  `g ∈ GG(A_f)` on `H^d(S, W)_λ` commute.

### Fixed vectors and the level Hecke algebra

For a small level `U`, write `K_U = inverseOpposite U.obj`, the ordinary
compact open subgroup `{g | op g⁻¹ ∈ U}` of `GG(A_f)`.

* `CMHarrisLambdaTowerFixedVectorComparison …` is the proposition
  `TowerFixedVectorComparison H`: for every small level `U`, the map from
  `H^d(S_U ×_F F̄, W)_λ` to `H^d(S, W)_λ` is injective, and its image is the set
  of vectors fixed by `K_U`. It is the fixed-vector form of Harris–Taylor's
  `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`, and it is
  stated, not proved.
* `cmHarrisLambdaTowerFixedLeg … U` is the `Γ`-equivariant map from
  `H^d(S_U ×_F F̄, W)_λ` to the `K_U`-fixed vectors of `H^d(S, W)_λ`
  (`towerFixedLeg`).
* `cmHarrisLambdaTowerFixedLegIso … hfix U`, for
  `hfix : CMHarrisLambdaTowerFixedVectorComparison …`, is the resulting
  isomorphism of Galois actions (`towerFixedLegIso`).
* `cmHarrisLambdaTowerHeckeModule … U` is the `K_U`-fixed vectors of
  `H^d(S, W)_λ` as a module over the published `LevelHeckeAlgebra K_λ K_U`,
  with `Γ` acting by module maps (`towerHeckeModule`).
* `cmHarrisLambdaTowerHeckeModule_ρ_smul`: each `γ ∈ Γ` commutes with every
  element of the Hecke algebra.

### Isotypic parts and multiplicity spaces

Let `M` be a field with `[Algebra K_λ M]`, and let
`τ : Representation M GG(A_f) V` be a representation on an `M`-module `V`.
Write `X_M = H^d(S, W)_λ ⊗_{K_λ} M`.

* `cmHarrisLambdaTowerExtendScalars … M` is `X_M`, a smooth representation of
  `GG(A_f)` over `M` with the commuting action of `Γ` (`towerExtendScalars`).
* `cmHarrisLambdaTowerIsotypic … M τ` is the `τ`-isotypic part `X_M[τ]`, with
  the restricted actions of `GG(A_f)` and `Γ` (`towerIsotypic`).
* `cmHarrisLambdaTowerIsotypicFixedVectors … M τ U` is the `K_U`-fixed vectors
  of `X_M[τ]`, with the action of `Γ` (`towerIsotypicFixedVectors`). For
  `d = n - 1`, `τ = JL(π_f)` and `U` Harris's level `K(N)`, this is Harris's
  `H^{n-1}(S_K(N), W)[π]`.
* `cmHarrisLambdaTowerMultiplicity … M τ` is `Hom_{GG(A_f)}(τ, X_M)`, with `Γ`
  acting by composition (`towerMultiplicity`).
* `cmHarrisLambdaTowerHeckeMultiplicity … M τ U` is
  `Hom_{H(K_U)}(τ^{K_U}, X_M^{K_U})`, for the level Hecke algebra `H(K_U)` of
  `K_U` over `M`, with `Γ` acting by composition (`towerHeckeMultiplicity`).
* `cmHarrisLambdaTowerIsotypicEvaluation_surjective`: the evaluation map
  `V ⊗ Hom_{GG(A_f)}(τ, X_M) → X_M[τ]` is surjective.
* `cmHarrisLambdaTowerIsotypicEvaluation_galois`: for every `γ ∈ Γ`, the
  evaluation map intertwines `id ⊗ γ`, with `γ` acting on the multiplicity
  space by composition, and the action of `γ` on `X_M[τ]`.
* `cmHarrisLambdaTowerExtendScalarsFixedVectorsIso … M hfix U`: under `hfix`,
  the isomorphism of Galois actions between
  `H^d(S_U ×_F F̄, W)_λ ⊗_{K_λ} M` (`baseChangeAction`) and `X_M^{K_U}`
  (`towerExtendScalarsFixedVectorsIso`). Through it, the Hecke multiplicity
  space corresponds to Kottwitz's `Hom_{H(K_U)}(τ^{K_U}, H^d(S_U ×_F F̄, W)_λ ⊗ M)`,
  for the Hecke module structure transported from `X_M^{K_U}`. No
  Hecke-linearity of this isomorphism is stated.

### Galois representations

Assume in addition that `M` is a topological ring with
`hKM : Continuous (algebraMap K_λ M)`, and fix
`hfix : CMHarrisLambdaTowerFixedVectorComparison …`, a small level `U`, and

* `hfin : CMHarrisLambdaCohomologyFiniteDimensional … U … l degree`;
* `hcont : CMHarrisLambdaCohomologyContinuous … U … l degree`.

These are the published propositions at level `U`.

* `cmHarrisLambdaIsotypicFixedVectorsObjects … M hKM hfix U hfin hcont τ :
  Objects F M` is the continuous finite-dimensional Galois representation of
  `F` over `M` on `H^d(S_U, W)[τ]` (`towerIsotypicFixedVectorsObjects`).
* `cmHarrisLambdaMultiplicityObjects … M hKM hfix U hcont τ hgen : Objects F M`
  is the Galois representation on `Hom_{GG(A_f)}(τ, X_M)`, assuming this space
  is finite-dimensional over `M` (instance argument) and that `V` is spanned by
  the translates `τ g u` of the `K_U`-fixed vectors `u` (`hgen`)
  (`towerMultiplicityObjects`).
* `cmHarrisLambdaHeckeMultiplicityObjects … M hKM hfix U hcont τ : Objects F M`
  is the Galois representation on `Hom_{H(K_U)}(τ^{K_U}, X_M^{K_U})`, assuming
  this space is finite-dimensional over `M` (instance argument)
  (`towerHeckeMultiplicityObjects`).
* Euler polynomials. Let `v` be a finite place of `F`, `ι` a closure embedding
  at `v`, and `hu : CMHarrisLambdaCohomologyUnramifiedAt … U … l degree v`.
  Then `hasEulerPolynomialAt_cmHarrisLambdaIsotypicFixedVectorsObjects`,
  `hasEulerPolynomialAt_cmHarrisLambdaMultiplicityObjects` and
  `hasEulerPolynomialAt_cmHarrisLambdaHeckeMultiplicityObjects` state that the
  representation has Euler polynomial at `v` equal to
  `(geometricFrobenius (ModuleCat M) v A ι).hom.charpoly.reverse`, where `A` is
  the space of the representation. This is `det(1 − X · σ(Fr_v))` for a
  geometric Frobenius along `ι`. For the isotypic fixed vectors, the statement
  uses the finiteness of `X_M^{K_U}` from `finite_towerExtendScalarsFixedVectors`,
  which the characteristic polynomial needs.

For `M = K_λ` with its own topology, the published
`Langlands.GaloisRepresentation.LambdaAdic F K l.1` is `Objects F K_λ`, so
these are `λ`-adic representations in the Library's sense.

## Proof outline

Every definition is a specialization, and every theorem is the corresponding
published theorem applied to `H` and `isLevelTrivial_cmHarrisLambdaLevelCohomology`.
The value and the maps of `H` are given by `rfl`. The finiteness instance
needed by `towerIsotypicFixedVectorsObjects` is `hfin`, which is by definition
`FiniteDimensional K_λ H(U)`, that is `Module.Finite K_λ H(U)`.

## Provenance

The constructions are internal. They specialize the published tower and
isotypic modules to the Library's `λ`-adic cohomology with Harris's
coefficient systems, through the descent from scaled levels. The objects are
those of Harris (1999), §5:

* printed p. 312 (PDF p. 14): "the `JL(π_f)`-isotypic component of
  `H^{n-1}(S_K(N), W)`, which we denote `H^{n-1}(S_K(N), W)[π]`";
* printed p. 313 (PDF p. 15): `λ`-adic representations unramified at all but
  finitely many places, and the local factor (5.6) through the eigenvalues of
  `σ(Fr_w)` for a geometric Frobenius `Fr_w`.

The source is `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`. The tower,
the action of `GG(A_f)` by conjugation of levels, and the fixed-vector
comparison are those of Harris–Taylor (2001), III.2, printed pp. 96-97
(PDF pp. 104-105; the displays on p. 96 were read on a rendered image). The
source is `harris-taylor-2001-geometry-cohomology-simple-shimura`, PDF SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Harris–Taylor do not state the fixed-vector comparison as a separate result;
`CMHarrisLambdaTowerFixedVectorComparison` is its fixed-vector form for every
level at once. The Hecke multiplicity space is that of Kottwitz (1992), §1,
printed p. 655: `W^i(π_f) = Hom_{H_K}(π_f^K, H^i(S_K, F))`. The source is
`kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

The Euler polynomial is the Library's `HasEulerPolynomialAt`, the reversed
characteristic polynomial of a geometric Frobenius. Its roots are the inverses
of the eigenvalues `β` in (5.6). The normalization of (5.6) by `|β|` is not
formalized.
