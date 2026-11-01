import Langlands.Geometry.Analytic.Spectrum.ResidueField

/-! # Extending point realizations to completed residue fields -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BanachSpectrum

variable {A : Type u} [NormedCommRing A]
  (K : Type v) [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]
  (x : BanachSpectrum A)
  {L : Type w} [NormedField L]
  (f : A →+* L) (hf : ∀ a, ‖f a‖ = x a)

private def realizationQuotient : ResidueDomain x →+* L :=
  Ideal.Quotient.lift x.kernel f fun a ha => norm_eq_zero.mp ((hf a).trans ha)

private theorem realizationQuotient_injective :
    Function.Injective (realizationQuotient x f hf) :=
  RingHom.lift_injective_of_ker_le_ideal x.kernel _ fun a ha => by
    change x a = 0
    rw [← hf a]
    exact norm_eq_zero.mpr ha

private def realizationFraction : ResidueFraction x →+* L :=
  IsFractionRing.lift (realizationQuotient_injective x f hf)

private theorem realizationFraction_map (a : A) :
    realizationFraction x f hf (fractionMap x a) = f a := by
  change IsFractionRing.lift _ (algebraMap (ResidueDomain x) (ResidueFraction x)
    (residueQuotient x a)) = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

private def realizationNormed : NormedResidueField K x →+* L :=
  (realizationFraction x f hf).comp (WithAbs.equiv (fractionAbsoluteValue K x)).toRingHom

private theorem realizationNormed_map (a : A) :
    realizationNormed K x f hf (residueFieldMap K x a) = f a :=
  realizationFraction_map x f hf a

private theorem norm_realizationNormed (a : NormedResidueField K x) :
    ‖realizationNormed K x f hf a‖ = ‖a‖ := by
  obtain ⟨b, c, _hc, ha⟩ := IsFractionRing.div_surjective (ResidueDomain x) a.ofAbs
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := x.kernel) b
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (I := x.kernel) c
  have ha' : a = residueFieldMap K x b / residueFieldMap K x c :=
    (WithAbs.equiv (fractionAbsoluteValue K x)).injective ha.symm
  rw [ha', map_div₀, norm_div, realizationNormed_map, realizationNormed_map,
    norm_div, norm_residueFieldMap, norm_residueFieldMap, hf, hf]

private theorem isometry_realizationNormed : Isometry (realizationNormed K x f hf) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr (norm_realizationNormed K x f hf)

variable [CompleteSpace L]

/-- The canonical extension of a norm-preserving point realization to its
completed residue field. -/
def completedResidueLiftRingHom : CompletedResidueField K x →+* L :=
  UniformSpace.Completion.extensionHom (realizationNormed K x f hf)
    (isometry_realizationNormed K x f hf).continuous

theorem isometry_completedResidueLiftRingHom :
    Isometry (completedResidueLiftRingHom K x f hf) :=
  (isometry_realizationNormed K x f hf).completion_extension

@[simp]
theorem completedResidueLiftRingHom_map (a : A) :
    completedResidueLiftRingHom K x f hf (completedResidueMap K x a) = f a :=
  (UniformSpace.Completion.extensionHom_coe _ _ (residueFieldMap K x a)).trans
    (realizationNormed_map K x f hf a)

variable [Algebra K L]

/-- The extension of a point-realizing algebra map, with its isometric norm
bound and scalar compatibility retained. -/
def completedResidueLift (g : A →ₐ[K] L) (hg : ∀ a, ‖g a‖ = x a) :
    BoundedAlgHom K (CompletedResidueField K x) L where
  toRingHom := completedResidueLiftRingHom K x g.toRingHom hg
  commutes' c := by
    change completedResidueLiftRingHom K x g.toRingHom hg
      (completedResidueMap K x (algebraMap K A c)) = algebraMap K L c
    rw [completedResidueLiftRingHom_map]
    exact g.commutes c
  bounded := ⟨1, zero_lt_one, fun a => by
    rw [one_mul]
    simpa only [map_zero, dist_zero_right] using
      ((isometry_completedResidueLiftRingHom K x g.toRingHom hg).dist_eq a 0).le⟩

theorem isometry_completedResidueLift (g : A →ₐ[K] L) (hg : ∀ a, ‖g a‖ = x a) :
    Isometry (completedResidueLift K x g hg) :=
  isometry_completedResidueLiftRingHom K x g.toRingHom hg

@[simp]
theorem completedResidueLift_map (g : A →ₐ[K] L) (hg : ∀ a, ‖g a‖ = x a) (a : A) :
    completedResidueLift K x g hg (completedResidueMap K x a) = g a :=
  completedResidueLiftRingHom_map K x g.toRingHom hg a

variable {B : Type z} [NormedCommRing B] [NormedAlgebra K B]

/-- A bounded map induces the canonical isometric embedding between the
completed residue fields at a point and its restriction. -/
def completedResidueComap (g : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    BoundedAlgHom K
      (CompletedResidueField K (comap g.toBoundedRingHom y))
      (CompletedResidueField K y) :=
  completedResidueLift K (comap g.toBoundedRingHom y)
    ((completedResidueMap K y).comp g).toAlgHom
    (fun a => norm_completedResidueMap K y (g a))

theorem isometry_completedResidueComap (g : BoundedAlgHom K A B)
    (y : BanachSpectrum B) : Isometry (completedResidueComap K g y) :=
  isometry_completedResidueLift K _ _ _

@[simp]
theorem completedResidueComap_map (g : BoundedAlgHom K A B) (y : BanachSpectrum B) (a : A) :
    completedResidueComap K g y
      (completedResidueMap K (comap g.toBoundedRingHom y) a) =
      completedResidueMap K y (g a) :=
  completedResidueLift_map K _ _ _ a

end Langlands.Analytic.BanachSpectrum
