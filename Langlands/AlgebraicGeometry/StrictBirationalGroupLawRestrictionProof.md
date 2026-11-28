# Proof that birational group laws over a DVR are strict on a dense open

`Langlands.AlgebraicGeometry.strictBirationalGroupLawRestriction.{u}` proves the Library
proposition `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestrictionStatement.{u}`,
imported from `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestrictionStatement`. Its type
is exactly that closed proposition.

```lean
theorem strictBirationalGroupLawRestriction :
    StrictBirationalGroupLawRestrictionStatement.{u}
```

## Statement proved

Let `R` be a discrete valuation ring and `f : X ⟶ Spec R` smooth, separated, locally of finite
type, quasi-compact and surjective. For every `m : BirationalGroupLaw f` there is an open `X'` of
`X` with `FibreGenerizationDense f X'` (`X'` is `R`-dense) and `m.IsStrictOn X'` (module
`Langlands.AlgebraicGeometry.StrictBirationalGroupLaw`).

```lean
def StrictBirationalGroupLawRestrictionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    Smooth f → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Surjective f →
    ∀ m : BirationalGroupLaw f,
      ∃ X' : X.Opens, FibreGenerizationDense f (X' : Set X) ∧ m.IsStrictOn X'
```

This is Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.2 Proposition 2, printed
p. 115, with proof on printed pp. 115–117, in the case of a discrete valuation ring (literature
ID `bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is PDF page
`p + 7`). Separatedness and surjectivity of `f` are not used by the proof.

## The source proof

BLR take the open `U` on which `m` is defined and the universal translations `Φ`, `Ψ` are open
immersions, `V = Φ(U)`, `W = Ψ(U)`, and the `S`-dense open `Z = U ∩ V ∩ W`. The set `T₁` of points
`x` of `X` such that `Z` is not dense in `x ×_S X` is constructible (BLR 2.5/1) and misses the
generic points of the fibres of `X`; over a discrete valuation ring its closure is nowhere dense
in every fibre. With `T₂` defined by the second projection, `X' = X − (closure T₁ ∪ closure T₂)`
is `S`-dense and `Z ∩ (X' ×_S X')` is `X'`-dense for both projections. With
`U' = U ∩ (X' ×_S X') ∩ m⁻¹(X')`, BLR then check fibre by fibre, after base change to a point `a`
of `X'`, that `U'`, `Φ(U')` and `Ψ(U')` are `X'`-dense for both projections.

## The implemented proof

The Lean proof follows this outline with two changes. It does not prove that `T₁` is
constructible: it proves directly that every generic point of a fibre of `X` has a neighbourhood
whose specializations lie outside `T₁` and `T₂`, by generic flatness. And it checks the density
conditions on generic points of fibres instead of after base change to points.

Notation: `p₁, p₂` are the projections of `X ×_S X`, `D = m.domain`, `Φ` and `Ψ` are
`leftTranslation f m.domain m.mul m.mul_comp` and `rightTranslation f m.domain m.mul m.mul_comp`,
and `F = fibreGenericPoints f`. A point is fibre generic for a map when it has no proper
generization with the same image (`StrictBirationalGroupLawRestriction.IsFibreGeneric`).

1. `Z = D ∩ range Φ ∩ range Ψ` is open, and contains every point generic in its fibre over `S`,
   by the fields `domain_dense`, `leftTranslation_dense` and `rightTranslation_dense` of
   `BirationalGroupLaw` and `fibreGenericPoints_subset_iff`.
2. For `ξ ∈ F` and `i = 1, 2`, every point generic in its `pᵢ`-fibre over `ξ` is generic in its
   fibre over `S`, hence lies in `Z`. `exists_open_forall_isFibreGeneric_mem` (module
   `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGenericNeighbourhood`),
   applied to the smooth quasi-compact projections `pᵢ`, gives an open neighbourhood of `ξ` on
   whose specializations of `ξ` the property
   `G x`: *every point generic in its `p₁`-fibre or `p₂`-fibre over `x` lies in `Z`*
   holds. It rests on
   `StrictBirationalGroupLawRestriction.exists_notMem_forall_minimal_mem` (module
   `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.GenericRegularity`).
3. `exists_opens_of_forall_fibreGeneric` (module
   `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.DvrDenseOpen`) gives an open
   `X' ⊇ F` on which `G` holds; this is the step using the discrete valuation ring.
   `FibreGenerizationDense f X'` follows from `F ⊆ X'` by `fibreGenericPoints_subset_iff`.
4. `U'` is the open `{y | p₁ y ∈ X', p₂ y ∈ X', y = D.ι u with m.mul u ∈ X'}`, the image of
   `m.mul⁻¹(X')` under the open immersion `D.ι` intersected with `p₁⁻¹(X') ∩ p₂⁻¹(X')`. The four
   inclusions of `IsStrictOn` hold by construction (the last since `D.ι` is injective).
5. The six density conditions come from `translation_density` (module
   `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.TranslationDensity`), applied
   to the underlying maps of `p₁`, `p₂`, `D.ι`, `Φ`, `Ψ` and `m.mul`. Its hypotheses are: the
   identities `Φ ≫ p₁ = D.ι ≫ p₁`, `Φ ≫ p₂ = m.mul`, `Ψ ≫ p₁ = m.mul`, `Ψ ≫ p₂ = D.ι ≫ p₂`
   (`pullback.lift_fst`, `pullback.lift_snd`); open embeddings for open immersions; existence
   of fibre generic generizations (`exists_fibreGenericPoint_specializes`); the fact that `p₂`
   maps `p₁`-fibre generic points into `F` and `p₁` maps `p₂`-fibre generic points into `F`
   (`isFibreGeneric_snd`, `isFibreGeneric_fst`, module
   `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGeneric`); and
   property `G` on `X'`, with `range D.ι = D` (`Scheme.Opens.range_ι`).

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Helper modules

- `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.GenericRegularity`: generic
  regularity of a nonzerodivisor modulo extended ideals, and the ring form of step 2.
- `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGeneric`: fibre generic
  points and lifting of generizations in fibre products.
- `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGenericNeighbourhood`:
  the scheme form of step 2.
- `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.TranslationDensity`: the six
  density conditions from generic points.
- `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.DvrDenseOpen`: the choice of
  `X'` over a discrete valuation ring.
