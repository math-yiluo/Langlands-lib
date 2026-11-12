# Base-changed Čech complexes of relative spaces and their comparison maps

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.CechData`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures.

## Notation

`R : Type u` is a commutative ring and `f : X ⟶ Spec R` a morphism of schemes.
`relSpace f S`, `relProj f S`, `relMap f s` and `structureHom f S V` are the
notations of the Library module
`Langlands.AlgebraicGeometry.Picard.RelativeAffineSections`: `Spec S ×_R X`, its
projection to `Spec S`, the base-change map along `s : S →ₐ[R] A`, and the ring map
`S → Γ(relSpace f S, V)`. Covers are the ported FLT ordered affine covers
`Scheme.OrderedAffineCover`. A cover `K` has a finite linearly ordered index type
`K.ι` and affine opens `K.U i` covering the space. `K.Idx p` is the type of strictly
increasing maps `Fin (p + 1) → K.ι`, and `K.inter σ` is `⨅ j, K.U (σ j)`.
`OModulePresheaf.unit π` is the structure sheaf of `π` as an FLT `OModulePresheaf`.
Its ordered Čech cochains are `cochain K p = ∀ σ : K.Idx p, Γ(V, K.inter σ)`,
with the alternating Čech differential `d K p`.

## `Cover` section

`S` and `A` are `R`-algebras and `s : S →ₐ[R] A`.

- `isAffineHom_relMap s` (instance): `relMap f s` is affine, as a base change of
  the affine morphism `Spec.map s` (`isPullback_relMap`).
- `pullCover s K` (abbrev): the ordered affine cover of `relSpace f A` with the
  same index type and opens `relMap f s ⁻¹ᵁ K.U i`.
- `preimage_iInf_of_finite`: preimages commute with finite infima of opens.
- `pullCover_inter`: `(pullCover f s K).inter σ = relMap f s ⁻¹ᵁ K.inter σ`.
- `isAffineOpen_inter`: if `relProj f S` is separated, every `K.inter σ` is
  affine. This uses Mathlib's `isAffineHom_diagonal_iff`: in a separated scheme
  over an affine base, the intersection of two affine opens is affine.
- `isSeparated_relProj`, `isProper_relProj`: `relProj f S` is separated (proper)
  if `f` is, as a base change of `f`.
- `appLE_congr`: `appLE` maps of equal morphisms agree.
- `structureHom_comp_appLE s V W h`: for `W ≤ relMap f s ⁻¹ᵁ V`,
  `structureHom f S V ≫ (relMap f s).appLE V W h = ofHom s ≫ structureHom f A W`.
  This is the commutativity of the base-change square on sections.
- `algebraIsPushout_sections_of_eq`: the Library's `algebraIsPushout_sections` for
  an open `W` that is only propositionally equal to `relMap f s ⁻¹ᵁ V`.

## `Complex` section

`P` is an `R`-algebra, `K` an ordered affine cover of `relSpace f P`, and `A₀` a
`P`-algebra.

- `cplx f K A₀ p` (abbrev): `A₀ ⊗[P] (unit (relProj f P)).cochain K p`, the Čech
  cochains of the structure sheaf of `relSpace f P`, base-changed to `A₀`.
- `dif f K A₀ p : cplx p →ₗ[A₀] cplx (p + 1)`: the base change
  `LinearMap.baseChange A₀` of the FLT differential `d K p`.
- `dif_comp_dif`: `dif (p + 1) ∘ₗ dif p = 0`, from the FLT `d_comp_d`.
- `subsingleton_cplx`: `cplx p` is trivial when `p` exceeds the number of opens,
  since then `K.Idx p` is empty.
- `flat_cochain` (instance): if `f` is flat and separated, the cochains
  `(unit (relProj f P)).cochain K p` are flat `P`-modules. They are a finite
  product of the sections over the affine opens `K.inter σ`, which are flat
  (`flat_structureHom`).

## `Comparison` section

Here `A` is a `P`-algebra (with `R → P → A` a scalar tower), and `M` is an
`A₀`-module with a compatible `P`-module structure.

- `testCover f K A` (abbrev): `pullCover` of `K` along `P → A`.
- `testCover_inter`: its intersections are the preimages of those of `K`.
- `secMap f K σ`: the ring map `Γ(relSpace f P, K.inter σ) ⟶
  Γ(relSpace f A, (testCover f K A).inter σ)` given by `appLE` of `relMap`.
- `structureHom_comp_secMap`: the square with `P → A` and the structure maps
  commutes.
- `compMap f K j p` for `f` separated and `j : M →ₗ[P] A`: the additive map
  `cplx f K A₀ p ⊗[A₀] M → (unit (relProj f A)).cochain (testCover f K A) p`.
  It is the Library's `cechTensorMap` for the families `Γ(relSpace f P, K.inter σ)`
  and `Γ(relSpace f A, (testCover f K A).inter σ)`. The algebra structures are given
  by `structureHom` and `secMap`, and the pushout property is
  `algebraIsPushout_sections_of_eq` on the affine opens `K.inter σ`. A local
  tactic macro `intro_insts p A` reintroduces these local instances inside proofs.
- `compMap_tmul`: `(a ⊗ x) ⊗ m ↦ (σ ↦ structureHom (j (a • m)) * secMap σ (x σ))`.
- `compMap_injective`: injective if `f` is flat and `j` is injective
  (`cechTensorMap_injective`).
- `exists_compMap_eq_iff j 𝔞 hj y`: if the image of `j` is exactly the ideal `𝔞`
  of `A`, a cochain `y` is in the image iff every `y σ` lies in the extension of
  `𝔞` to the sections over `(testCover f K A).inter σ`
  (`mem_range_cechTensorMap_iff`).
- `secMap_res`, `d_secMap`: `secMap` commutes with restriction maps and hence with
  the FLT Čech differentials.
- `compMap_dif`: `compMap (p + 1) ((dif p).rTensor M y) = d (compMap p y)`, the
  comparison is a map of complexes (`cechTensorMap_differential`).
- `compMap_mul_eq_zero`: if `j m * j m' = 0` for all `m, m'`, products of
  components of values of `compMap` vanish (`cechTensorMap_mul_eq_zero`).
- For a `P`-algebra map `h : A →ₐ[P] A'`: `testCover_inter_le`, the ring maps
  `testMap f K h σ` between the sections over the two test covers (by `appLE`),
  and `secMap_comp_testMap`, `structureHom_comp_testMap` (the evident triangles
  and squares commute).
- `compMap_natural j j' h φ hφ y σ`: if `φ : M →ₗ[A₀] M'` satisfies
  `j' (φ m) = h (j m)`, then
  `testMap σ (compMap j p y σ) = compMap j' p (φ.lTensor _ y) σ`
  (`cechTensorMap_natural`).

## `Finiteness` section

Here `A₀` is a `P`-algebra with a compatible `R`-algebra structure, and the
coefficients are `M = A₀` with `j = id`.

- `compMap_smul_tmul_one`: `compMap id p ((a • y) ⊗ 1) σ` equals
  `structureHom a * compMap id p (y ⊗ 1) σ`.
- `toCochain f K A₀ p : cplx p →ₗ[A₀] (unit (relProj f A₀)).cochain (testCover f K A₀) p`:
  `y ↦ compMap id p (y ⊗ 1)`. Linearity over `A₀` is `compMap_smul_tmul_one`.
- `toCochain_dif`: `toCochain` intertwines `dif` with the FLT differential of the
  test cover (`compMap_dif`).
- `toCochain_bijective` for `f` flat: injectivity is `compMap_injective` composed
  with `TensorProduct.rid`. Surjectivity is `exists_compMap_eq_iff` for the ideal
  `⊤`, whose extension is `⊤`.
- `equivCochain`: the resulting `A₀`-linear equivalence. So the base-changed
  complex `cplx f K A₀` is isomorphic to the FLT Čech complex of the structure
  sheaf of `relSpace f A₀` for the pulled-back cover.
- `finiteCohomology_dif`: if `A₀` is noetherian and `f` is proper and flat,
  `FiniteCohomology (dif f K A₀)` holds (see
  `Langlands.Algebra.PushoutCechNaturality`). Proof: `relProj f A₀` is proper, so
  the FLT theorem `OModulePresheaf.cechFinite_unit_of_isProper` gives finite Čech
  cohomology of its structure sheaf. Then `finiteCohomology_of_equiv` transfers it
  along `equivCochain` and `toCochain_dif`.

## Provenance

Internal infrastructure for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`. It is
derived from the ported FLT ordered Čech complexes, Mathlib's base change of
affine sections, and the Library modules
`Langlands.AlgebraicGeometry.Picard.RelativeAffineSections` and
`Langlands.Algebra.PushoutIdealTensor`. No literature statement is formalized.
