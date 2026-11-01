# The bi-Čech resolution

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.Complex`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

Let `𝒲 : BiCover P`, given by `f : P ⟶ X`, `g : P ⟶ Y` and ordered affine covers `𝒰`, `𝒱`,
and let `F : P.Modules`.

## Definitions

- `TIdx 𝒲 n = Σ pq : antidiagonal n, 𝒰.Idx pq.1 × 𝒱.Idx pq.2`. Its elements are a bidegree
  `(p, q)` with `p + q = n` and tuples `s`, `t`; `tidx h s t` builds one.
- `term 𝒲 F n = ⨁_{x : TIdx n} sheafOn F (biOpen s t)` is a finite biproduct of the
  modules `CechResolution.sheafOn` of the Library. `πT` denotes its projections.
- `horC` and `verC` are the components of the two Čech differentials. They are defined by
  matching on the bidegree. `D 𝒲 F n = biproduct.lift (horC + (-1)^p • verC)` is the
  differential of the bi-Čech complex.
- `ε 𝒲 F : F ⟶ term 𝒲 F 0` collects the units `F ⟶ sheafOn F (biOpen s t)`.
- `bicechComplex 𝒲 F` is the cochain complex `CochainComplex.of (term 𝒲 F) (D 𝒲 F)`, and
  `bicechAug 𝒲 F : F[0] ⟶ bicechComplex 𝒲 F` is the augmentation.

## Results

- `toT V x` reads off the components of a section `x` of `term n` over `V` as an element
  of `TSec 𝒲 F n V` (see `BiCech.Sections`). It is injective and surjective
  (`toT_injective`, `toT_surjective`). It satisfies `toT_D` (`toT (D x) = DT (toT x)`) and
  `toT_ε` (`toT (ε m) = augT m`).
- `D_D` and `ε_D` follow from `DT_DT` and `DT_augT`, using injectivity of `toT` on every
  open.
- `exact_bicechSc n` and `exact_augSc` state exactness of `Kⁿ ⟶ Kⁿ⁺¹ ⟶ Kⁿ⁺²` and of
  `F ⟶ K⁰ ⟶ K¹`. Both use the Library criterion `CechResolution.exact_of_locally`. A
  section is restricted to `V ∩ f⁻¹(𝒰.U a) ∩ g⁻¹(𝒱.U b)`, which contains the given point,
  and `DT_preimT` or `augT_eq_of_DT_eq_zero` applies there.
- `mono_ε` holds because the opens `biOpen (a) (b)` cover `P`; it uses the sheaf property
  of `F`.
- `quasiIso_bicechAug 𝒲 F : QuasiIso (bicechAug 𝒲 F)`. Its proof is the same reduction as
  the Library's `CechResolution.quasiIso_cechAug_of_exact`.

No hypothesis on `F`, `f`, `g` or the covers is needed here.

Provenance: internal. The bi-Čech complex is the total complex of the double Čech complex
of the two pulled-back covers. It is a resolution because the double complex is locally
contractible.
