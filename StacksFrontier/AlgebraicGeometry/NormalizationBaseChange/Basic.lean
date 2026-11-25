module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Functorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.Topology.Sober.Generization
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Normalization and extension of the ground field

Let `X` be a scheme locally of finite type over a field `k` and let `K/k` be an extension of
fields.  The normalization of the base change `X_K` maps canonically to the base change of the
normalization of `X`.

The construction is the one of the source: a flat morphism carries generic points to generic
points, so it induces a morphism on the coproducts of the generic-point residue spectra, and
functoriality of relative normalization then supplies a morphism of normalizations over it.
Applying this to the projection `X_K ⟶ X`, which is flat because `Spec K ⟶ Spec k` is, and
pairing the result with the structure morphism of `X_K` gives the comparison morphism into the
fibre product.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.genericPointResidueSpectrumMap` is the morphism of generic-point
  residue spectra induced by a flat morphism.
* `AlgebraicGeometry.normalizationSchemeMap` is the morphism of normalizations induced by a flat
  morphism.
* `AlgebraicGeometry.baseChangeNormalization` is the base change to `K` of the normalization
  morphism of `X`.
* `AlgebraicGeometry.normalizationBaseChangeComparison` is the canonical comparison from the
  normalization after base change to the base change of the normalization.

## Main results

* `AlgebraicGeometry.mem_genericPoints_of_generalizingMap`: a map along which generalizations
  lift carries generic points to generic points.
* `AlgebraicGeometry.normalizationSchemeMap_normalization`: the induced morphism of
  normalizations commutes with the normalization morphisms.
* `AlgebraicGeometry.normalizationBaseChangeComparison_comp_fst` and
  `AlgebraicGeometry.normalizationBaseChangeComparison_comp_snd` identify the two projections of
  the comparison, and
  `AlgebraicGeometry.normalizationBaseChangeComparison_comp_baseChangeNormalization` identifies
  its composite with the base-changed normalization morphism.

## Implementation notes

Schemes over a field are represented as objects of the over category, and base change is the
pullback functor on that category.  Local finite type over a field implies local
Noetherianness, which supplies the finiteness of irreducible components of quasi-compact opens
required to normalize; this is
`AlgebraicGeometry.finite_irreducibleComponents_of_locallyOfFiniteType`.

The source deduces that the projection `X_K ⟶ X` carries generic points to generic points from
the fact that it is surjective, open and generizing.  Openness is not needed: lifting
generalizations alone gives the conclusion, and a flat morphism lifts generalizations by
`AlgebraicGeometry.Flat.generalizingMap`.  Flatness of the projection is base change from
`Spec K ⟶ Spec k`, which is flat because every module over a field is flat.

The two remaining assertions of Tag 0C3N — that the comparison is a universal homeomorphism in
general, and an isomorphism for a separable extension — are not proved here.

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Generic points and lifting of generalizations -/

/-- A map along which generalizations lift carries generic points of irreducible components to
generic points of irreducible components. -/
theorem mem_genericPoints_of_generalizingMap
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [T0Space S] [T0Space T]
    [QuasiSober S] [QuasiSober T] {f : S → T} (hf : GeneralizingMap f)
    {x : S} (hx : x ∈ genericPoints S) : f x ∈ genericPoints T := by
  refine (mem_genericPoints_iff_forall_specializes_eq (f x)).2 fun y hy ↦ ?_
  obtain ⟨x', hx', rfl⟩ := hf hy
  simp [(mem_genericPoints_iff_forall_specializes_eq x).1 hx x' hx']

namespace Scheme

variable {X Y : Scheme.{u}}

/-- A flat morphism of schemes carries generic points of irreducible components to generic
points of irreducible components. -/
theorem Hom.mem_genericPoints_of_flat (f : X ⟶ Y) [Flat f]
    {x : X} (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y :=
  mem_genericPoints_of_generalizingMap (Flat.generalizingMap f) hx

/-! ### Functoriality of the generic-point residue spectrum -/

/-- The morphism of generic-point residue spectra induced by a flat morphism: on the summand at
a generic point `η` it is the residue-field morphism at `η`, landing in the summand at the
image of `η`. -/
noncomputable def Hom.genericPointResidueSpectrumMap (f : X ⟶ Y) [Flat f] :
    genericPointResidueSpectrum X ⟶ genericPointResidueSpectrum Y :=
  Sigma.desc fun η : genericPoints X ↦
    Spec.map (f.residueFieldMap η.1) ≫
      Sigma.ι (fun ξ : genericPoints Y ↦ Spec (.of (Y.residueField ξ.1)))
        ⟨f η.1, f.mem_genericPoints_of_flat η.2⟩

/-- The restriction of `AlgebraicGeometry.Scheme.Hom.genericPointResidueSpectrumMap` to the
summand at a generic point. -/
theorem Hom.ι_genericPointResidueSpectrumMap (f : X ⟶ Y) [Flat f] (η : genericPoints X) :
    Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ≫
        f.genericPointResidueSpectrumMap =
      Spec.map (f.residueFieldMap η.1) ≫
        Sigma.ι (fun ξ : genericPoints Y ↦ Spec (.of (Y.residueField ξ.1)))
          ⟨f η.1, f.mem_genericPoints_of_flat η.2⟩ :=
  Sigma.ι_comp_desc _ _

/-- The induced morphism of generic-point residue spectra lies over the given morphism. -/
theorem Hom.genericPointResidueSpectrumMap_fromGenericPointResidueFields (f : X ⟶ Y) [Flat f] :
    f.genericPointResidueSpectrumMap ≫ fromGenericPointResidueFields Y =
      fromGenericPointResidueFields X ≫ f :=
  Sigma.hom_ext _ _ fun η ↦
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ fromGenericPointResidueFields Y)
          (f.ι_genericPointResidueSpectrumMap η)).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (Spec.map (f.residueFieldMap η.1) ≫ ·)
              (genericPointResidueSpectrum_ι_fromGenericPointResidueFields Y
                ⟨f η.1, f.mem_genericPoints_of_flat η.2⟩)).trans <|
            (Hom.SpecMap_residueFieldMap_fromSpecResidueField f η.1).trans <|
              (congrArg (· ≫ f)
                  (genericPointResidueSpectrum_ι_fromGenericPointResidueFields X η)).symm.trans
                (Category.assoc _ _ _)

end Scheme

/-! ### Functoriality of the normalization of a scheme along a flat morphism -/

variable {X Y : Scheme.{u}}

/-- The morphism of normalizations induced by a flat morphism of schemes whose quasi-compact
opens have finitely many irreducible components. -/
noncomputable def normalizationSchemeMap (f : X ⟶ Y) [Flat f]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    X.normalizationScheme hX ⟶ Y.normalizationScheme hY :=
  letI := Scheme.quasiCompactFromGenericPointResidueFields X hX
  letI := Scheme.quasiSeparatedFromGenericPointResidueFields X
  letI := Scheme.quasiCompactFromGenericPointResidueFields Y hY
  letI := Scheme.quasiSeparatedFromGenericPointResidueFields Y
  Scheme.Hom.normalizationMap (Scheme.fromGenericPointResidueFields Y)
    (Scheme.fromGenericPointResidueFields X) f.genericPointResidueSpectrumMap f
    f.genericPointResidueSpectrumMap_fromGenericPointResidueFields

/-- The induced morphism of normalizations commutes with the normalization morphisms. -/
theorem normalizationSchemeMap_normalization (f : X ⟶ Y) [Flat f]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    normalizationSchemeMap f hX hY ≫ Y.stacksNormalization hY = X.stacksNormalization hX ≫ f :=
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let := Scheme.quasiCompactFromGenericPointResidueFields Y hY
  let := Scheme.quasiSeparatedFromGenericPointResidueFields Y
  Scheme.Hom.normalizationMap_fromNormalization _ _ _ _ _

/-! ### The comparison for an extension of the ground field -/

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

end AlgebraicGeometry

end
