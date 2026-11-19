import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.UnramifiedRigidity

/-! # Local agreement of maps to an unramified affinoid piece -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

open Set

variable {K : Type u} {R : Type v} {S : Type w} {T : Type z}
  [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [Algebra K R] [Algebra K S] [Algebra K T]

/-- An open neighbourhood on which any affinoid restriction makes two
bounded maps agree as full algebra maps. -/
structure AgreementNeighborhood (g h : BoundedAlgHom K S T) (x : BanachSpectrum T) where
  carrier : Set (BanachSpectrum T)
  isOpen : IsOpen carrier
  mem : x ∈ carrier
  comp_eq : ∀ (C : PresentedAffinoidAlgebra K) (r : BoundedAlgHom K T C),
    (∀ y, BanachSpectrum.comap r.toBoundedRingHom y ∈ carrier) → r.comp g = r.comp h

/-- If two maps over the same base agree in the residue field of `x` and
the first map lands at an unramified point, there is an open neighbourhood
of `x` on which every affinoid restriction makes them agree. -/
def unramifiedAgreementNeighborhood (f : BoundedAlgHom K R S)
    (hf : f.toAlgHom.toRingHom.FiniteType)
    (g h : BoundedAlgHom K S T) (hbase : g.comp f = h.comp f)
    (x : BanachSpectrum T) (heq : ∀ a, x (g a - h a) = 0)
    (hu : f.IsUnramifiedAtPoint (BanachSpectrum.comap g.toBoundedRingHom x)) :
    AgreementNeighborhood g h x :=
  Classical.choice (show Nonempty (AgreementNeighborhood g h x) from by
    classical
    unfold IsUnramifiedAtPoint at hu
    obtain ⟨e, he, hne⟩ := SetLike.not_le_iff_exists.mp hu
    obtain ⟨G, n, M, _, hrigid⟩ :=
      QuasiEtaleRigidity.exists_unramified_rigidity_bound f hf e he
    let V : Set (BanachSpectrum T) :=
      {y | M * ∑ a ∈ G, y (g a - h a) < y (g e) ^ n}
    have hsum : Continuous (fun y : BanachSpectrum T => ∑ a ∈ G, y (g a - h a)) :=
      continuous_finsetSum G fun a _ => (BanachSpectrum.evaluation (g a - h a)).continuous
    have hpos : 0 < x (g e) :=
      lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _) (Ne.symm hne)
    refine ⟨⟨V, isOpen_lt (continuous_const.mul hsum)
      ((BanachSpectrum.evaluation (g e)).continuous.pow n), ?_, ?_⟩⟩
    · change M * ∑ a ∈ G, x (g a - h a) < x (g e) ^ n
      simp only [heq, Finset.sum_const_zero, mul_zero]
      exact pow_pos hpos n
    · intro C r hr
      apply hrigid C (r.comp g) (r.comp h)
      · intro a
        exact congrArg r (congrArg (fun k : BoundedAlgHom K R T => k a) hbase)
      · intro y
        have hy := hr y
        change M * ∑ a ∈ G, y (r (g a - h a)) < y (r (g e)) ^ n at hy
        change M * ∑ a ∈ G, y (r (g a) - r (h a)) < y (r (g e)) ^ n
        simpa only [map_sub] using hy)

end Langlands.Analytic.BoundedAlgHom
