import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalTransport

/-! # Coefficient equivalences of intrinsic weighted rational quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  {A B C : PresentedAffinoidAlgebra K} {m : ℕ}
  (s : PositivePolyradius (Fin m)) (g : A) (f : Fin m → A)
  (e : BoundedAlgEquiv K A B)

/-- The coefficient equivalence sends the original rational relations into the
closed ideal of the mapped rational relations. -/
theorem coefficientEquiv_mapsRelations :
    RelativeRelations.MapsRelations K s e.toBoundedAlgHom
      (equations K A s g f) (equations K B s (e g) (fun j => e (f j))) :=
  RelativeRelations.mapsRelations_of_mapsTo K s e.toBoundedAlgHom
    (mapCoefficients_equations K s g f e.toBoundedAlgHom)

/-- The inverse coefficient map preserves the rational relations in the reverse
direction, using the proved coefficient inverse identities. -/
theorem coefficientEquiv_symm_mapsRelations :
    RelativeRelations.MapsRelations K s e.symm.toBoundedAlgHom
      (equations K B s (e g) (fun j => e (f j))) (equations K A s g f) := by
  apply RelativeRelations.mapsRelations_of_mapsTo K s e.symm.toBoundedAlgHom
  simpa only [BoundedAlgEquiv.toBoundedAlgHom_apply,
    BoundedAlgEquiv.symm_apply_apply] using
    mapCoefficients_equations K s (e g) (fun j => e (f j)) e.symm.toBoundedAlgHom

/-- The actual bounded rational-quotient equivalence induced by a bounded
coefficient equivalence, with no relation-compatibility input. -/
def coefficientEquiv :
    BoundedAlgEquiv K (Algebra K A s g f)
      (Algebra K B s (e g) (fun j => e (f j))) :=
  RelativeRelations.transportEquiv K s
    (equations K A s g f) (equations K B s (e g) (fun j => e (f j))) e
    (coefficientEquiv_mapsRelations K s g f e)
    (coefficientEquiv_symm_mapsRelations K s g f e)

/-- The forward map is the already constructed coefficient transport. -/
@[simp] theorem coefficientEquiv_toBoundedAlgHom :
    (coefficientEquiv K s g f e).toBoundedAlgHom = transport K s g f e.toBoundedAlgHom :=
  rfl

@[simp] theorem coefficientEquiv_quotientMap (h : GeneralizedTateAlgebra s A) :
    coefficientEquiv K s g f e (quotientMap K A s g f h) =
      quotientMap K B s (e g) (fun j => e (f j))
        (mapCoefficientsAlgHom s e.toBoundedAlgHom h) := rfl

@[simp] theorem coefficientEquiv_symm_quotientMap (h : GeneralizedTateAlgebra s B) :
    (coefficientEquiv K s g f e).symm
      (quotientMap K B s (e g) (fun j => e (f j)) h) =
      quotientMap K A s g f (mapCoefficientsAlgHom s e.symm.toBoundedAlgHom h) := rfl

@[simp] theorem coefficientEquiv_baseMap (a : A) :
    coefficientEquiv K s g f e (baseMap K A s g f a) =
      baseMap K B s (e g) (fun j => e (f j)) (e a) :=
  transport_baseMap K s g f e.toBoundedAlgHom a

@[simp] theorem coefficientEquiv_fraction (j : Fin m) :
    coefficientEquiv K s g f e (fraction K A s g f j) =
      fraction K B s (e g) (fun i => e (f i)) j :=
  transport_fraction K s g f e.toBoundedAlgHom j

@[simp] theorem coefficientEquiv_symm_baseMap (b : B) :
    (coefficientEquiv K s g f e).symm
      (baseMap K B s (e g) (fun j => e (f j)) b) =
      baseMap K A s g f (e.symm b) :=
  RelativeRelations.transport_baseMap K s e.symm.toBoundedAlgHom
    (coefficientEquiv_symm_mapsRelations K s g f e) b

@[simp] theorem coefficientEquiv_symm_fraction (j : Fin m) :
    (coefficientEquiv K s g f e).symm
      (fraction K B s (e g) (fun i => e (f i)) j) = fraction K A s g f j :=
  RelativeRelations.transport_newCoordinate K s e.symm.toBoundedAlgHom
    (coefficientEquiv_symm_mapsRelations K s g f e) j

/-- Every nonnegative forward coefficient bound transfers unchanged. -/
theorem norm_coefficientEquiv_le {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ a, ‖e a‖ ≤ c * ‖a‖) (a : Algebra K A s g f) :
    ‖coefficientEquiv K s g f e a‖ ≤ c * ‖a‖ :=
  RelativeRelations.norm_transportEquiv_le K s e
    (coefficientEquiv_mapsRelations K s g f e)
    (coefficientEquiv_symm_mapsRelations K s g f e) hc he a

/-- The inverse bound transfers independently of the forward bound. -/
theorem norm_coefficientEquiv_symm_le {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ b, ‖e.symm b‖ ≤ c * ‖b‖)
    (b : Algebra K B s (e g) (fun j => e (f j))) :
    ‖(coefficientEquiv K s g f e).symm b‖ ≤ c * ‖b‖ :=
  RelativeRelations.norm_transportEquiv_symm_le K s e
    (coefficientEquiv_mapsRelations K s g f e)
    (coefficientEquiv_symm_mapsRelations K s g f e) hc he b

/-- Norm preservation of the coefficient equivalence gives exact equality of the
actual rational quotient norms. -/
theorem norm_coefficientEquiv (he : ∀ a, ‖e a‖ = ‖a‖) (a : Algebra K A s g f) :
    ‖coefficientEquiv K s g f e a‖ = ‖a‖ :=
  RelativeRelations.norm_transportEquiv K s e
    (coefficientEquiv_mapsRelations K s g f e)
    (coefficientEquiv_symm_mapsRelations K s g f e) he a

theorem norm_coefficientEquiv_symm (he : ∀ a, ‖e a‖ = ‖a‖)
    (b : Algebra K B s (e g) (fun j => e (f j))) :
    ‖(coefficientEquiv K s g f e).symm b‖ = ‖b‖ := by
  have h := norm_coefficientEquiv K s g f e he ((coefficientEquiv K s g f e).symm b)
  rw [BoundedAlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem isometry_coefficientEquiv (he : Isometry e) :
    Isometry (coefficientEquiv K s g f e) :=
  RelativeRelations.isometry_transportEquiv K s e
    (coefficientEquiv_mapsRelations K s g f e)
    (coefficientEquiv_symm_mapsRelations K s g f e) he

/-- The forward coefficient and fraction formulas determine the equivalence's
bounded forward map among all bounded homomorphisms. -/
theorem eq_coefficientEquiv
    (ψ : BoundedAlgHom K (Algebra K A s g f)
      (Algebra K B s (e g) (fun j => e (f j))))
    (hbase : ∀ a, ψ (baseMap K A s g f a) =
      baseMap K B s (e g) (fun j => e (f j)) (e a))
    (hfrac : ∀ j, ψ (fraction K A s g f j) =
      fraction K B s (e g) (fun i => e (f i)) j) :
    ψ = (coefficientEquiv K s g f e).toBoundedAlgHom :=
  eq_transport K s g f e.toBoundedAlgHom ψ hbase hfrac

omit e in
@[simp] theorem coefficientEquiv_refl (a : Algebra K A s g f) :
    coefficientEquiv K s g f (BoundedAlgEquiv.refl K A) a = a := by
  have h := congrArg (fun φ : BoundedAlgHom K (Algebra K A s g f)
    (Algebra K A s g f) => φ a) (transport_id K s g f)
  exact h

/-- Composition of coefficient equivalences agrees on every quotient element. -/
theorem coefficientEquiv_trans (d : BoundedAlgEquiv K B C) (a : Algebra K A s g f) :
    coefficientEquiv K s g f (e.trans d) a =
      coefficientEquiv K s (e g) (fun j => e (f j)) d
        (coefficientEquiv K s g f e a) := by
  have h := congrArg (fun φ : BoundedAlgHom K (Algebra K A s g f)
    (Algebra K C s (d (e g)) (fun j => d (e (f j)))) => φ a)
    (transport_comp K s g f d.toBoundedAlgHom e.toBoundedAlgHom)
  exact h

/-- The actual quotient-spectrum homeomorphism, contravariant in coefficients. -/
def coefficientSpectrumHomeomorph :
    BanachSpectrum (Algebra K B s (e g) (fun j => e (f j))) ≃ₜ
      BanachSpectrum (Algebra K A s g f) :=
  (coefficientEquiv K s g f e).spectrumHomeomorph

@[simp] theorem coefficientSpectrumHomeomorph_apply
    (x : BanachSpectrum (Algebra K B s (e g) (fun j => e (f j))))
    (a : Algebra K A s g f) :
    coefficientSpectrumHomeomorph K s g f e x a =
      x (coefficientEquiv K s g f e a) := rfl

@[simp] theorem coefficientSpectrumHomeomorph_symm_apply
    (x : BanachSpectrum (Algebra K A s g f))
    (b : Algebra K B s (e g) (fun j => e (f j))) :
    (coefficientSpectrumHomeomorph K s g f e).symm x b =
      x ((coefficientEquiv K s g f e).symm b) := rfl

/-- The coefficient spectrum homeomorphism restricts to the actual rational
inequality loci. Its inverse uses the proved coefficient inverse identities. -/
def coefficientLocusHomeomorph :
    locus K B s (e g) (fun j => e (f j)) ≃ₜ locus K A s g f :=
  e.spectrumHomeomorph.subtype (fun _ => Iff.rfl)

@[simp] theorem coefficientLocusHomeomorph_apply
    (x : locus K B s (e g) (fun j => e (f j))) (a : A) :
    (coefficientLocusHomeomorph K s g f e x).val a = x.val (e a) := rfl

@[simp] theorem coefficientLocusHomeomorph_symm_apply
    (x : locus K A s g f) (b : B) :
    ((coefficientLocusHomeomorph K s g f e).symm x).val b = x.val (e.symm b) := rfl

/-- The homeomorphisms commute with the actual forward structural maps, as an
equality of continuous maps into the original inequality locus. -/
theorem coefficientSpectrumHomeomorph_naturality :
    (spectrumToLocus K A s g f).comp
        ⟨coefficientSpectrumHomeomorph K s g f e,
          (coefficientSpectrumHomeomorph K s g f e).continuous⟩ =
      (⟨coefficientLocusHomeomorph K s g f e,
        (coefficientLocusHomeomorph K s g f e).continuous⟩ :
          C(locus K B s (e g) (fun j => e (f j)), locus K A s g f)).comp
        (spectrumToLocus K B s (e g) (fun j => e (f j))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (coefficientEquiv_baseMap K s g f e a)

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation
