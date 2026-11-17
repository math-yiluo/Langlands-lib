import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Pointwise étaleness and bounded changes of target algebra -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w} {T : Type z}
  [NormedField K] [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [Algebra K R] [Algebra K S] [Algebra K T]

/-- A bounded change of target algebra preserves and reflects pointwise
étaleness at the corresponding actual spectrum point. -/
theorem isEtaleAtPoint_comp_boundedEquiv_iff
    (f : BoundedAlgHom K R S) (e : BoundedAlgEquiv K S T)
    (hf : f.toAlgHom.toRingHom.FiniteType) (y : BanachSpectrum T) :
    (e.toBoundedAlgHom.comp f).IsEtaleAtPoint y ↔
      f.IsEtaleAtPoint (e.spectrumHomeomorph y) := by
  have he : e.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
    AlgebraicallyFiniteEtale.of_bijective _ e.bijective
  have hi : e.symm.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
    AlgebraicallyFiniteEtale.of_bijective _ e.symm.bijective
  have het := (algebraicallyFiniteEtale_iff _).1 he
  have hit := (algebraicallyFiniteEtale_iff _).1 hi
  constructor
  · intro hx
    have hp : BanachSpectrum.comap e.symm.toBoundedAlgHom.toBoundedRingHom
        (e.spectrumHomeomorph y) = y :=
      e.spectrumHomeomorph.symm_apply_apply y
    have hx' : (e.toBoundedAlgHom.comp f).IsEtaleAtPoint
        (BanachSpectrum.comap e.symm.toBoundedAlgHom.toBoundedRingHom
          (e.spectrumHomeomorph y)) := hp.symm ▸ hx
    have hc := (hi.isEtaleAtPoint (e.spectrumHomeomorph y)).comp
      hit.1.finiteType (het.1.finiteType.comp hf) hx'
    have hcancel : e.symm.toBoundedAlgHom.comp (e.toBoundedAlgHom.comp f) = f := by
      apply BoundedAlgHom.ext
      intro r
      exact e.symm_apply_apply (f r)
    rw [hcancel] at hc
    exact hc
  · intro hx
    exact (he.isEtaleAtPoint y).comp het.1.finiteType hf hx

end Langlands.Analytic.BoundedAlgHom
