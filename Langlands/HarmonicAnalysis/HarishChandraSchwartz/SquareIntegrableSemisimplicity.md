# Square-integrable representations are unitary and semisimple (Waldspurger, Lemma III.1.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity`,
namespace `Langlands.HarishChandraSchwartz`. It imports and uses:

- `SchurOrthogonality` (published): `invariantForm`, `invariantForm_add_left`,
  `invariantForm_smul_left`, `invariantForm_swap`, `invariantForm_rho`, `invariantForm_self`,
  `invariantForm_self_re_pos`, `formIntegrand_self`, `isUnitarizable_of_isSquareIntegrable`;
- `CentralSubgroupCoefficients` (through `SchurOrthogonality`):
  `IsSquareIntegrableModCentralSubgroup`, `centralSubgroupCoefficientNorm_mk`;
- `Smooth.Contragredient.AdmissibleDualityProof`: `isAdmissible_smoothContragredient_of_compact_cofinal`,
  `smoothBidual_surjective_of_compact_cofinal`, `smoothBidual_injective_of_compact_cofinal`;
- `Smooth.Contragredient.ExactProof`: `contragredientMap_surjective_of_injective_of_compact_cofinal`;
- `Smooth.Admissibility.EmbeddingProof`: `isAdmissible_of_injective`;
- `Unitary.AdmissibleSemisimplicityProof`: `admissibleUnitarySemisimplicity`;
- `Unitary.HermitianDual`: `InvariantPositiveForm.smoothDualEquiv`, `smoothDualEquiv_apply`,
  `toSmoothDual_apply_action`, `rightFunctional`; `Unitary.Basic`: `IsUnitarizable.of_injective`;
- `FiniteVectors`: `FiniteVectors.orbitSubrepresentation`, `FiniteVectors.self_mem_orbitSpan`;
  `ScalarSubReduction`: `ScalarSubReduction.inclusion`, `ScalarSubReduction.inclusion_injective`;
- Mathlib: `Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`,
  `Representation.irreducible_iff_isSimpleModule_asModule`,
  `isSemisimpleModule_of_isSemisimpleModule_submodule'`,
  `IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top`,
  `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`, `finsum_eq_sum_of_support_subset`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

Lemma III.1.3, printed p. 264 (PDF p. 30): "Toute représentation admissible de carré intégrable
de `G` est unitaire et semi-simple." Proof (same page; the bar is on the first coefficient, checked
on the page image): for a finitely generated subrepresentation `V'` with generators
`v₁, …, vₙ`, `V̌' = V̌ / Ann V'`, and
`(v̌₁, v̌₂) ↦ Σᵢ ∫_{A_G\G} conj⟨π(g) vᵢ, v̌₁⟩ ⟨π(g) vᵢ, v̌₂⟩ dg`
is a positive definite `G`-invariant Hermitian form on `V̌'`. Hence `V̌'` is unitary, and so is
`V'`; admissible unitary representations are semisimple, so `V'` is; `V` is the union of its
finitely generated subrepresentations, hence semisimple; every irreducible subrepresentation is
unitary by the above, so `V` is unitary.

## Scope: abstract data and explicit hypotheses

The setting is that of `SchurOrthogonality`: `G` is a topological group, `A` a normal subgroup
contained in the center (`hA`), `G ⧸ A` carries a Borel structure and a Haar measure `μ`.
Representations are `Representation ℂ G V` without topology. The hypotheses of each result:

- `unitaryCentralCharacterComap`: an injective intertwiner `f : σ → ρ` (`hf`).
- `IsSquareIntegrableModCentralSubgroup.of_injective`: `hcof` (every open subgroup contains a
  compact open subgroup), `f`, `hf` and `hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ`.
- `unitaryCentralCharacterDual`: none beyond `IsTopologicalGroup G`.
- `IsSquareIntegrableModCentralSubgroup.smoothContragredient`: `[μ.IsInvInvariant]`, `hcof`, `hρ`.
- `dualInvariantForm`, `isUnitarizable_smoothContragredient_of_admissible`: `hcof`,
  `hρ : IsAdmissible ρ` and an invariant positive form (resp. `IsUnitarizable ρ`).
- `eq_zero_of_forall_orbit`, `subrepresentation_asAlgebraHom_apply`,
  `subrepresentationAsModuleEquiv`: none (any group `G`).
- `isUnitarizable_orbitSubrepresentation`, `isSemisimpleRepresentation_of_isSquareIntegrable`,
  `isUnitarizable_of_isSquareIntegrableModCentralSubgroup`: `[μ.IsInvInvariant]`, `hcof`, `hρ`.
- `isUnitarizable_of_isInternal`: `[DecidableEq ι]`, an internal direct sum
  `hint : DirectSum.IsInternal p` of `ℂ[G]`-submodules `p i` of `ρ.asModule`, and an invariant
  positive form on each `(Subrepresentation.ofSubmodule' (p i)).toRepresentation`.

Square integrability (`IsSquareIntegrableModCentralSubgroup`) is the published predicate:
admissibility, a unitary character of the full center, and square integrability on `G ⧸ A` of
all smooth matrix coefficients. Waldspurger's `A_G`, the unimodularity of `G / A_G` and `hcof` for
his `G` are not established here.

## Definitions

- `unitaryCentralCharacterComap c f hf`: the unitary central character of `ρ` transported to `σ`
  along an injective intertwiner.
- `unitaryCentralCharacterDual c`: the unitary central character `c⁻¹` of `smoothContragredient ρ`.
- `dualInvariantForm b hcof hρ`: for an invariant positive form `b` on admissible `ρ`, the
  invariant positive form `⟪ℓ₁, ℓ₂⟫ = b(E⁻¹ ℓ₂, E⁻¹ ℓ₁)` on `smoothContragredient ρ`, where
  `E = b.smoothDualEquiv hcof hρ : v ↦ b(v, -)`.
- `subrepresentationAsModuleEquiv S`: the `ℂ[G]`-linear equivalence between
  `S.toRepresentation.asModule` and the submodule `Subrepresentation.asSubmodule S` of
  `ρ.asModule` (identity on elements).

## Results

- `IsSquareIntegrableModCentralSubgroup.of_injective`: square integrability passes along injective
  intertwiners (in particular to subrepresentations).
- `IsSquareIntegrableModCentralSubgroup.smoothContragredient`: the smooth contragredient of a
  square-integrable representation is square integrable.
- `isUnitarizable_smoothContragredient_of_admissible`: the smooth contragredient of an admissible
  unitarizable representation is unitarizable.
- `eq_zero_of_forall_orbit`: a linear functional on the orbit subrepresentation of `x` that
  vanishes on all `σ(g) x` vanishes.
- `isUnitarizable_orbitSubrepresentation`: the subrepresentation spanned by the orbit of one
  vector of a square-integrable `ρ` is unitarizable.
- `isSemisimpleRepresentation_of_isSquareIntegrable` (**Lemma III.1.3, semisimplicity**): a
  square-integrable `ρ` is semisimple (`ρ.IsSemisimpleRepresentation`).
- `isUnitarizable_of_isInternal`: invariant positive forms on the summands of an internal direct
  sum of subrepresentations add up to an invariant positive form on `ρ`.
- `isUnitarizable_of_isSquareIntegrableModCentralSubgroup` (**Lemma III.1.3, unitarity**): a
  square-integrable `ρ` is unitarizable (`IsUnitarizable ρ`), without irreducibility.

## Proof notes

The implemented route follows Waldspurger's, with these derived variations: cyclic
subrepresentations (one generator) replace finitely generated ones; the smooth dual of the
subrepresentation is used directly (square integrability transfers because smooth functionals
extend along injective intertwiners, `contragredientMap_surjective_of_injective_of_compact_cofinal`)
instead of `V̌ / Ann V'`; and the form is written with `g⁻¹`.

1. Transfer to subrepresentations: the central character acts on `σ` because `f` is injective; a
   coefficient `ℓ(σ(g) x)` of `σ` equals the coefficient `ℓ'(ρ(g) f(x))` of `ρ` for an extension
   `ℓ'` of `ℓ`.
2. Transfer to the contragredient: every smooth functional on `V̌` is evaluation at some
   `v ∈ V` (`smoothBidual_surjective_of_compact_cofinal`), so its coefficients are
   `ℓ(ρ(g⁻¹) v)`; their norm functions on `G ⧸ A` are those of `ρ` composed with `q ↦ q⁻¹`, which
   preserves `μ`.
3. Contragredient of a unitary admissible representation: `E` is an equivariant
   conjugate-linear bijection, and the transported form is positive definite and invariant.
4. Cyclic subrepresentation `V'` of `x`: on `X = V̌'` take the published `invariantForm` with
   the smooth functional `ℓ = ` evaluation at `x`, i.e. `(l₁, l₂) ↦ ∫ l₁(σ(g⁻¹) x) conj l₂(σ(g⁻¹) x)`,
   and `⟪l₁, l₂⟫ = (l₂, l₁)`. If `l ≠ 0`, some `l(σ(g) x) ≠ 0` (`eq_zero_of_forall_orbit`), so
   `ℓ(X(g⁻¹) l) ≠ 0` and `0 < Re (X(g⁻¹) l, X(g⁻¹) l) = Re (l, l)` (`invariantForm_self_re_pos`,
   `invariantForm_rho`): the form is definite. Then `X` is unitarizable, so is its smooth dual
   (step 3), and `V'` embeds in it by `smoothBidual` (`IsUnitarizable.of_injective`).
5. Semisimplicity: each cyclic subrepresentation is admissible and unitarizable, hence semisimple
   (`admissibleUnitarySemisimplicity`); as `ℂ[G]`-submodules of `ρ.asModule`
   (`subrepresentationAsModuleEquiv`) they span, so `ρ.asModule` is semisimple
   (`isSemisimpleModule_of_isSemisimpleModule_submodule'`).
6. Unitarity: write `ρ.asModule` as an internal direct sum of simple submodules
   (`IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top`). Each summand is an irreducible
   square-integrable subrepresentation, unitarizable by `isUnitarizable_of_isSquareIntegrable`.
   `isUnitarizable_of_isInternal` sets `⟪x, y⟫ = Σᶠᵢ bᵢ(xᵢ, yᵢ)` over the components; on a finite
   set containing the supports this is a finite sum, which gives sesquilinearity, symmetry and
   positivity termwise; definiteness because each `bᵢ(xᵢ, xᵢ)` is real and `≥ 0`; invariance
   because the components of `ρ(g) x` are `ρ(g) xᵢ`.

## Relation to the Library

- `SchurOrthogonality` proves unitarity for irreducible square-integrable representations
  (`isUnitarizable_of_isSquareIntegrable`); this module removes irreducibility and proves
  semisimplicity.
- `AdmissibleSemisimplicityProof` (admissible unitarizable ⇒ semisimple) and `HermitianDual`
  (`v ↦ b(v, -)`) are used as stated. The Library's unitarity of contragredients
  (`Langlands/VirtualRepresentation/Supercuspidal/UnitaryDual`) is specific to `GL_n`; the generic version
  `isUnitarizable_smoothContragredient_of_admissible` is proved here.
- `FiniteVectors.orbitSubrepresentation` and `ScalarSubReduction.inclusion` are reused.

## Open obligations

The hypotheses `hcof`, the inversion invariance of the Haar measure on `G ⧸ A_G` and the
identification of `A` with Waldspurger's `A_G` for actual reductive groups are not proved here.
