module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField
public import StacksFrontier.Topology.Sober.Generization
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Normalization and reduction

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components. The
normalization morphism of `X` factors canonically through the reduction of `X`, the closed
subscheme cut out by the nilradical, and that factor is the normalization morphism of the
reduction.

## Main definitions

* `AlgebraicGeometry.Scheme.normalizationToReduction` is the canonical factor of the
  normalization morphism through the reduction.
* `AlgebraicGeometry.Scheme.homeomorphNilradicalSubscheme` identifies the underlying space of the
  reduction of `X` with that of `X`.
* `AlgebraicGeometry.Scheme.genericPointResidueSpectrumReductionIso` identifies the coproduct of
  the spectra of the residue fields at the generic points of the reduction with the one of `X`.
* `AlgebraicGeometry.Scheme.toNormalizationScheme` is the morphism from that coproduct to the
  normalization of `X`.
* `AlgebraicGeometry.Scheme.normalizationReductionIso` is the isomorphism of the normalization of
  `X` with the normalization of the reduction of `X`.

## Main results

* `AlgebraicGeometry.Scheme.finite_irreducibleComponents_reduction`: the reduction inherits the
  finiteness of irreducible components of quasi-compact opens, so it can itself be normalized.
* `AlgebraicGeometry.Scheme.normalizationToReduction_subschemeι` is the factorization equation.
* `AlgebraicGeometry.Scheme.existsUnique_iso_normalizationScheme_reduction`: the normalization of
  `X` is the normalization of the reduction of `X`, uniquely isomorphic to it over the reduction
  and compatibly with the morphisms from the generic-point residue spectra. Its two components
  are `AlgebraicGeometry.Scheme.normalizationReductionIso_hom_normalization` and
  `AlgebraicGeometry.Scheme.genericPointResidueSpectrumReductionIso_hom_toNormalizationScheme`.

## Implementation notes

The normalization of `X` is the relative normalization of `X` in the coproduct of the spectra of
the residue fields at its generic points. That coproduct is a coproduct of spectra of fields,
hence reduced, and relative normalization of a reduced scheme is reduced; so the normalization of
`X` is a reduced scheme and the factorization through the reduction is the one supplied by Tag
0356.

The reduction is taken to be `X.nilradical.subscheme`, the closed subscheme of the ideal sheaf
`X.nilradical`; its underlying space is all of `X`, which is what makes the finiteness transfer
below a purely topological statement about a homeomorphism.

That the factor through the reduction is the normalization of the reduction rests on the
coproducts of the spectra of the residue fields at the generic points of `X` and of its reduction
being the same: the closed immersion of the reduction is a homeomorphism, so it matches up the
generic points, and it is surjective on stalks, so it is an isomorphism on residue fields. With
that identification in hand, the statement is the universal property of relative normalization
over an intermediate scheme integral over the target (Tag 035I), applied to the factorization of
the generic-point residue morphism through the reduction.

The comparison of the two coproducts is phrased with the morphisms
`AlgebraicGeometry.Scheme.reductionResidueSpecHom`, whose stated source and target are the
summands indexed as `Limits.Sigma.whiskerEquiv` indexes them, rather than with `Spec.map` of the
residue-field map directly: the two spellings of the point of `X` are definitionally but not
syntactically equal, which is enough to break the motive of a rewrite.

## References

* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Scheme

/-! ### Transfer of finiteness of irreducible components along a homeomorphism -/

/-- A homeomorphism carries irreducible components to irreducible components. -/
private theorem image_mem_irreducibleComponents_of_homeomorph {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T) {s : Set S}
    (hs : s ∈ irreducibleComponents S) : e '' s ∈ irreducibleComponents T := by
  have h := preimage_mem_irreducibleComponents hs e.symm.isOpenEmbedding
    (by rcases hs.1.nonempty with ⟨x, hx⟩; exact ⟨x, hx, e.symm.surjective x⟩)
  convert h using 1
  ext y
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · exact fun hy ↦ ⟨e.symm y, by simpa using hy, by simp⟩

/-- Finiteness of the set of irreducible components transfers along a homeomorphism. -/
private theorem finite_irreducibleComponents_of_homeomorph {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T)
    (hT : (irreducibleComponents T).Finite) : (irreducibleComponents S).Finite := by
  have : Finite (irreducibleComponents T) := hT
  exact Finite.of_injective (fun Z : irreducibleComponents S =>
    (⟨e '' Z.1, image_mem_irreducibleComponents_of_homeomorph e Z.2⟩ :
      irreducibleComponents T))
    fun _ _ h ↦ Subtype.ext (Set.image_injective.mpr e.injective (congrArg Subtype.val h))

/-! ### The reduction can be normalized -/

/-- The reduction of `X` is homeomorphic to `X`: the closed immersion of the reduction is a
closed embedding, and it is surjective because the nilradical ideal sheaf is supported
everywhere. -/
noncomputable def homeomorphNilradicalSubscheme (X : Scheme.{u}) :
    X.nilradical.subscheme ≃ₜ X :=
  X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    (fun x ↦ Set.mem_range.mp
      (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial))

/-- The reduction of `X` has the same finiteness property for irreducible components of
quasi-compact opens as `X` itself, hence can be normalized whenever `X` can. -/
theorem finite_irreducibleComponents_reduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∀ U : X.nilradical.subscheme.Opens,
      IsCompact (U : Set X.nilradical.subscheme) → (irreducibleComponents U).Finite := by
  intro U hU
  let eX := X.homeomorphNilradicalSubscheme
  let V : X.Opens := ⟨eX '' (U : Set X.nilradical.subscheme), eX.isOpen_image.mpr U.2⟩
  exact finite_irreducibleComponents_of_homeomorph
    ((eX.image (U : Set X.nilradical.subscheme)).trans (Homeomorph.setCongr rfl))
    (hX V (hU.image eX.continuous))

/-! ### The normalization is reduced -/

/-- The coproduct of the spectra of the residue fields at the generic points is reduced. -/
private theorem isReduced_genericPointResidueSpectrum (X : Scheme.{u}) :
    IsReduced (genericPointResidueSpectrum X) := by
  unfold genericPointResidueSpectrum
  have : ∀ i, IsReduced ((sigmaOpenCover
      (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).X i) := by
    change ∀ η : genericPoints X, IsReduced (Spec (.of (X.residueField η.1)))
    intro η
    infer_instance
  exact IsReduced.of_openCover _ (sigmaOpenCover _)

/-- The normalization of `X` is a reduced scheme: it is the relative normalization of `X` in a
coproduct of spectra of fields. -/
theorem isReduced_normalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsReduced (X.normalizationScheme hX) := by
  have := quasiCompactFromGenericPointResidueFields X hX
  have := quasiSeparatedFromGenericPointResidueFields X
  have := isReduced_genericPointResidueSpectrum X
  change IsReduced (fromGenericPointResidueFields X).normalization
  infer_instance

/-! ### The canonical factorization through the reduction -/

/-! ### The generic-point residue spectrum of the reduction -/

/-! ### The normalization of `X` is the normalization of its reduction -/

end AlgebraicGeometry.Scheme

end
