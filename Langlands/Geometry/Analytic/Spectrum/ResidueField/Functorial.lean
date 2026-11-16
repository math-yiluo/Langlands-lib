import Langlands.Geometry.Analytic.GeneralizedAffinoid.PointAmalgamationReduction

/-! # Uniqueness and functoriality of completed residue-field lifts -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.BanachSpectrum

variable {A : Type u} [NormedCommRing A]
  (K : Type v) [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]
  (x : BanachSpectrum A)
  {L : Type w} [NormedField L]

/-- A continuous map of completed residue fields is determined by its values on
    the original algebra, because fractions of these values are dense. -/
theorem completedResidueRingHom_ext
    {f g : CompletedResidueField K x →+* L}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a, f (completedResidueMap K x a) = g (completedResidueMap K x a)) :
    f = g := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hf hg
  | ih a =>
    obtain ⟨b, c, _hc, ha⟩ := IsFractionRing.div_surjective (ResidueDomain x) a.ofAbs
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := x.kernel) b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (I := x.kernel) c
    have ha' : a = residueFieldMap K x b / residueFieldMap K x c :=
      (WithAbs.equiv (fractionAbsoluteValue K x)).injective ha.symm
    rw [ha']
    rw [show ((residueFieldMap K x b / residueFieldMap K x c :
        NormedResidueField K x) : CompletedResidueField K x) =
        (residueFieldMap K x b : CompletedResidueField K x) /
          (residueFieldMap K x c : CompletedResidueField K x) from
      map_div₀ (UniformSpace.Completion.coeRingHom :
        NormedResidueField K x →+* CompletedResidueField K x) _ _]
    change f (completedResidueMap K x b / completedResidueMap K x c) =
      g (completedResidueMap K x b / completedResidueMap K x c)
    rw [map_div₀, map_div₀, h b, h c]

/-- Bounded algebra maps out of a completed residue field are determined by
    their composites with its canonical algebra map. -/
theorem completedResidueBoundedAlgHom_ext [Algebra K L]
    {f g : BoundedAlgHom K (CompletedResidueField K x) L}
    (h : ∀ a, f (completedResidueMap K x a) = g (completedResidueMap K x a)) :
    f = g := by
  apply BoundedAlgHom.ext
  have hf : Continuous f := AddMonoidHomClass.continuous_of_bound
    f.toAlgHom.toRingHom f.bounded.choose f.bounded.choose_spec.2
  have hg : Continuous g := AddMonoidHomClass.continuous_of_bound
    g.toAlgHom.toRingHom g.bounded.choose g.bounded.choose_spec.2
  exact RingHom.congr_fun (completedResidueRingHom_ext K x hf hg h)

variable {B : Type z} [NormedCommRing B] [NormedAlgebra K B]
  {C : Type t} [NormedCommRing C] [NormedAlgebra K C]

/-- The residue-field map over an identity algebra map is the identity. -/
theorem completedResidueComapOfEq_id
    (h : comap (BoundedAlgHom.id K A).toBoundedRingHom x = x) :
    completedResidueComapOfEq K (BoundedAlgHom.id K A) x x h =
      BoundedAlgHom.id K (CompletedResidueField K x) := by
  apply completedResidueBoundedAlgHom_ext K x
  intro a
  rw [completedResidueComapOfEq_map]
  rfl

/-- Canonical completed residue-field maps respect composition, including
    explicit identifications of the spectrum points. -/
theorem completedResidueComapOfEq_comp
    (i : BoundedAlgHom K A B) (j : BoundedAlgHom K B C)
    (y : BanachSpectrum B) (z : BanachSpectrum C)
    (hi : comap i.toBoundedRingHom y = x)
    (hj : comap j.toBoundedRingHom z = y)
    (hij : comap (j.comp i).toBoundedRingHom z = x) :
    (completedResidueComapOfEq K j y z hj).comp
      (completedResidueComapOfEq K i x y hi) =
      completedResidueComapOfEq K (j.comp i) x z hij := by
  apply completedResidueBoundedAlgHom_ext K x
  intro a
  change completedResidueComapOfEq K j y z hj
      (completedResidueComapOfEq K i x y hi (completedResidueMap K x a)) = _
  rw [completedResidueComapOfEq_map, completedResidueComapOfEq_map,
    completedResidueComapOfEq_map]
  rfl

end Langlands.Analytic.BanachSpectrum
