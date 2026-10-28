import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeEquationComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalPresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRelationsTransport

/-! # Scalar and intrinsic weighted rational quotient comparison -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- Scalar evaluation takes the rational generators to the intrinsic generators. -/
theorem relativeSeriesEvaluation_equation (j : Fin m) :
    Adjoin.relativeSeriesEvaluation K A s
      (appendLeft A.polyradius s K g *
        X (A.polyradius.append s) K (Fin.natAdd A.arity j) -
          appendLeft A.polyradius s K (f j)) =
      constantAlgHom s K A (presentationMap K A g) * X s A j -
        constantAlgHom s K A (presentationMap K A (f j)) := by
  rw [map_sub, map_mul, Adjoin.relativeSeriesEvaluation_appendLeft,
    Adjoin.relativeSeriesEvaluation_X, Adjoin.relativeSeriesTuple_natAdd,
    Adjoin.relativeSeriesEvaluation_appendLeft]

/-- The image of the scalar rational equations is exactly the intrinsic relation set. -/
theorem relativeEquationRelations_eq :
    Adjoin.relativeEquationRelations K A s (equations K A s g f) =
      RelativeRationalPresentation.equations K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) := by
  ext h
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (relativeSeriesEvaluation_equation K A s g f j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, relativeSeriesEvaluation_equation K A s g f j⟩

/-- Identity coefficient transport from the evaluated scalar equations. -/
theorem mapsRelations_to_intrinsic :
    RelativeRelations.MapsRelations K s (BoundedAlgHom.id K A)
      (Adjoin.relativeEquationRelations K A s (equations K A s g f))
      (RelativeRationalPresentation.equations K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j))) := by
  rw [relativeEquationRelations_eq]
  exact RelativeRelations.mapsRelations_id K s _

/-- Identity coefficient transport back to the evaluated scalar equations. -/
theorem mapsRelations_from_intrinsic :
    RelativeRelations.MapsRelations K s (BoundedAlgHom.id K A)
      (RelativeRationalPresentation.equations K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)))
      (Adjoin.relativeEquationRelations K A s (equations K A s g f)) := by
  rw [relativeEquationRelations_eq]
  exact RelativeRelations.mapsRelations_id K s _

/-- Relabel the relative quotient using the proved equality of rational equations. -/
def relativeEquationEquiv :
    BoundedAlgEquiv K
      (Adjoin.relativeEquationAlgebra K A s (equations K A s g f))
      (RelativeRationalPresentation.Algebra K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j))) :=
  RelativeRelations.transportEquiv K s _ _ (BoundedAlgEquiv.refl K A)
    (mapsRelations_to_intrinsic K A s g f) (mapsRelations_from_intrinsic K A s g f)

@[simp] theorem relativeEquationEquiv_quotientMap (h : GeneralizedTateAlgebra s A) :
    relativeEquationEquiv K A s g f
      (RelativeRelations.quotientMap K A s
        (Adjoin.relativeEquationRelations K A s (equations K A s g f)) h) =
      RelativeRationalPresentation.quotientMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) h := by
  change RelativeRelations.transport K s
    (Adjoin.relativeEquationRelations K A s (equations K A s g f))
    (RelativeRationalPresentation.equations K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j))) (BoundedAlgHom.id K A)
    (mapsRelations_to_intrinsic K A s g f)
    (RelativeRelations.quotientMap K A s
      (Adjoin.relativeEquationRelations K A s (equations K A s g f)) h) = _
  rw [RelativeRelations.transport_quotientMap, mapCoefficientsAlgHom_id]
  rfl

@[simp] theorem relativeEquationEquiv_symm_quotientMap (h : GeneralizedTateAlgebra s A) :
    (relativeEquationEquiv K A s g f).symm
      (RelativeRationalPresentation.quotientMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) h) =
      RelativeRelations.quotientMap K A s
        (Adjoin.relativeEquationRelations K A s (equations K A s g f)) h := by
  change RelativeRelations.transport K s
    (RelativeRationalPresentation.equations K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j)))
    (Adjoin.relativeEquationRelations K A s (equations K A s g f))
    (BoundedAlgHom.id K A) (mapsRelations_from_intrinsic K A s g f)
    (RelativeRelations.quotientMap K A s
      (RelativeRationalPresentation.equations K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j))) h) = _
  rw [RelativeRelations.transport_quotientMap, mapCoefficientsAlgHom_id]
  rfl

theorem norm_relativeEquationEquiv
    (a : Adjoin.relativeEquationAlgebra K A s (equations K A s g f)) :
    ‖relativeEquationEquiv K A s g f a‖ = ‖a‖ :=
  RelativeRelations.norm_transportEquiv K s (BoundedAlgEquiv.refl K A)
    (mapsRelations_to_intrinsic K A s g f) (mapsRelations_from_intrinsic K A s g f)
    (fun _ => rfl) a

/-- The actual bounded equivalence from the scalar rational presentation to the
intrinsic rational quotient of relative series over the coefficient algebra. -/
def relativeEquiv :
    BoundedAlgEquiv K (algebra K A s g f)
      (RelativeRationalPresentation.Algebra K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j))) :=
  (BoundedAlgEquiv.ofHomInv
    (Adjoin.relativeEquationMap K A s (equations K A s g f))
    (Adjoin.relativeEquationInverse K A s (equations K A s g f))
    (Adjoin.relativeEquationInverse_map K A s (equations K A s g f))
    (Adjoin.relativeEquationMap_inverse K A s (equations K A s g f))).trans
      (relativeEquationEquiv K A s g f)

/-- On a scalar series representative the comparison is relative evaluation
followed by the intrinsic quotient projection. -/
@[simp] theorem relativeEquiv_presentationMap
    (h : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeEquiv K A s g f (presentationMap K (algebra K A s g f) h) =
      RelativeRationalPresentation.quotientMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) (Adjoin.relativeSeriesEvaluation K A s h) := by
  change relativeEquationEquiv K A s g f
    (RelativeRelations.quotientMap K A s
      (Adjoin.relativeEquationRelations K A s (equations K A s g f))
      (Adjoin.relativeSeriesEvaluation K A s h)) = _
  exact relativeEquationEquiv_quotientMap K A s g f _

/-- The inverse evaluates relative series in the scalar rational quotient. -/
@[simp] theorem relativeEquiv_symm_quotientMap (h : GeneralizedTateAlgebra s A) :
    (relativeEquiv K A s g f).symm
      (RelativeRationalPresentation.quotientMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) h) =
      Adjoin.relativeEquationInverseEvaluation K A s (equations K A s g f) h := by
  change Adjoin.relativeEquationInverse K A s (equations K A s g f)
    ((relativeEquationEquiv K A s g f).symm
      (RelativeRationalPresentation.quotientMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) h)) = _
  rw [relativeEquationEquiv_symm_quotientMap,
    Adjoin.relativeEquationInverse_quotientMap]

/-- The comparison fixes every actual coefficient. -/
@[simp] theorem relativeEquiv_baseMap (a : A) :
    relativeEquiv K A s g f (baseMap K A s g f a) =
      RelativeRationalPresentation.baseMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) a := by
  change relativeEquationEquiv K A s g f
    (Adjoin.relativeEquationMap K A s (equations K A s g f)
      (Adjoin.baseMap K A s (equations K A s g f) a)) = _
  rw [Adjoin.relativeEquationMap_baseMap]
  exact relativeEquationEquiv_quotientMap K A s g f _

/-- The comparison fixes every fraction coordinate label. -/
@[simp] theorem relativeEquiv_fraction (j : Fin m) :
    relativeEquiv K A s g f (fraction K A s g f j) =
      RelativeRationalPresentation.fraction K A s (presentationMap K A g)
        (fun i => presentationMap K A (f i)) j := by
  change relativeEquationEquiv K A s g f
    (Adjoin.relativeEquationMap K A s (equations K A s g f)
      (Adjoin.newCoordinate K A s (equations K A s g f) j)) = _
  rw [Adjoin.relativeEquationMap_newCoordinate]
  exact relativeEquationEquiv_quotientMap K A s g f _

@[simp] theorem relativeEquiv_symm_baseMap (a : A) :
    (relativeEquiv K A s g f).symm
      (RelativeRationalPresentation.baseMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) a) = baseMap K A s g f a := by
  rw [← relativeEquiv_baseMap, BoundedAlgEquiv.symm_apply_apply]

@[simp] theorem relativeEquiv_symm_fraction (j : Fin m) :
    (relativeEquiv K A s g f).symm
      (RelativeRationalPresentation.fraction K A s (presentationMap K A g)
        (fun i => presentationMap K A (f i)) j) = fraction K A s g f j := by
  rw [← relativeEquiv_fraction, BoundedAlgEquiv.symm_apply_apply]

/-- The comparison preserves the two actual quotient norms. -/
theorem norm_relativeEquiv (a : algebra K A s g f) :
    ‖relativeEquiv K A s g f a‖ = ‖a‖ :=
  (norm_relativeEquationEquiv K A s g f _).trans
    (Adjoin.norm_relativeEquationMap K A s (equations K A s g f) a)

theorem norm_relativeEquiv_symm
    (a : RelativeRationalPresentation.Algebra K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j))) :
    ‖(relativeEquiv K A s g f).symm a‖ = ‖a‖ := by
  have h := norm_relativeEquiv K A s g f ((relativeEquiv K A s g f).symm a)
  rw [BoundedAlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem isometry_relativeEquiv : Isometry (relativeEquiv K A s g f) :=
  AddMonoidHomClass.isometry_of_norm (relativeEquiv K A s g f).toAlgEquiv
    (norm_relativeEquiv K A s g f)

/-- Scalar rational maps are determined by coefficients and fraction coordinates. -/
theorem hom_ext (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    (ψ χ : BoundedAlgHom K (algebra K A s g f) B)
    (hbase : ∀ a, ψ (baseMap K A s g f a) = χ (baseMap K A s g f a))
    (hfrac : ∀ j, ψ (fraction K A s g f j) = χ (fraction K A s g f j)) :
    ψ = χ := by
  have h := RelativeRationalPresentation.hom_ext K A s (presentationMap K A g)
    (fun j => presentationMap K A (f j)) B
    (ψ.comp (relativeEquiv K A s g f).symm.toBoundedAlgHom)
    (χ.comp (relativeEquiv K A s g f).symm.toBoundedAlgHom)
    (fun a => by simpa only [BoundedAlgHom.comp_apply,
      BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_symm_baseMap] using hbase a)
    (fun j => by simpa only [BoundedAlgHom.comp_apply,
      BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_symm_fraction] using hfrac j)
  apply BoundedAlgHom.ext
  intro a
  have ha := congrArg (fun φ : BoundedAlgHom K
    (RelativeRationalPresentation.Algebra K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j))) B => φ (relativeEquiv K A s g f a)) h
  simpa only [BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    BoundedAlgEquiv.symm_apply_apply] using ha

omit [CompleteSpace K] in
/-- The scalar and intrinsic rational inequalities are the same subset. -/
theorem locus_eq_relativeLocus :
    locus K A s g f = RelativeRationalPresentation.locus K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j)) := rfl

/-- The actual spectrum homeomorphism induced contravariantly by the comparison. -/
def relativeSpectrumHomeomorph :
    BanachSpectrum (RelativeRationalPresentation.Algebra K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j))) ≃ₜ BanachSpectrum (algebra K A s g f) :=
  (relativeEquiv K A s g f).spectrumHomeomorph

@[simp] theorem relativeSpectrumHomeomorph_apply
    (x : BanachSpectrum (RelativeRationalPresentation.Algebra K A s
      (presentationMap K A g) (fun j => presentationMap K A (f j))))
    (a : algebra K A s g f) :
    relativeSpectrumHomeomorph K A s g f x a = x (relativeEquiv K A s g f a) := rfl

@[simp] theorem relativeSpectrumHomeomorph_symm_apply
    (x : BanachSpectrum (algebra K A s g f))
    (a : RelativeRationalPresentation.Algebra K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j))) :
    (relativeSpectrumHomeomorph K A s g f).symm x a =
      x ((relativeEquiv K A s g f).symm a) := rfl

/-- Comparison commutes with the two structural maps to the coefficient spectrum. -/
theorem relativeSpectrumHomeomorph_naturality :
    (spectrumMap K A s g f).comp
      ⟨relativeSpectrumHomeomorph K A s g f,
        (relativeSpectrumHomeomorph K A s g f).continuous⟩ =
      RelativeRationalPresentation.spectrumMap K A s (presentationMap K A g)
        (fun j => presentationMap K A (f j)) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (relativeEquiv K A s g f (baseMap K A s g f a)) =
    x (RelativeRationalPresentation.baseMap K A s (presentationMap K A g)
      (fun j => presentationMap K A (f j)) a)
  rw [relativeEquiv_baseMap]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
