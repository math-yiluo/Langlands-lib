import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Mathlib.RingTheory.Unramified.Finite

/-! # Pointwise cancellation for bounded algebra maps -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w} {T : Type z}
  [NormedField K] [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [Algebra K R] [Algebra K S] [Algebra K T]

/-- Unramifiedness of a finite-type composite descends to its second map. -/
theorem IsUnramifiedAtPoint.of_comp {f : BoundedAlgHom K R S}
    {g : BoundedAlgHom K S T} (hft : (g.comp f).toAlgHom.toRingHom.FiniteType)
    {z : BanachSpectrum T} (hgf : (g.comp f).IsUnramifiedAtPoint z) :
    g.IsUnramifiedAtPoint z := by
  rw [isUnramifiedAtPoint_iff_isUnramifiedAt _ hft] at hgf
  rw [isUnramifiedAtPoint_iff_isUnramifiedAt _ (RingHom.FiniteType.of_comp_finiteType hft)]
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra S T := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra R T := (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsUnramifiedAt R z.kernel := hgf
  exact Algebra.IsUnramifiedAt.of_restrictScalars R z.kernel

/-- Flatness of a composite descends across a first map that is finite type
and unramified at the image point. -/
theorem IsFlatAtPoint.of_comp {f : BoundedAlgHom K R S}
    {g : BoundedAlgHom K S T} (hft : f.toAlgHom.toRingHom.FiniteType)
    {z : BanachSpectrum T}
    (hf : f.IsUnramifiedAtPoint (BanachSpectrum.comap g.toBoundedRingHom z))
    (hgf : (g.comp f).IsFlatAtPoint z) : g.IsFlatAtPoint z := by
  rw [isUnramifiedAtPoint_iff_isUnramifiedAt _ hft] at hf
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra S T := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra R T := (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let q := (BanachSpectrum.comap g.toBoundedRingHom z).kernel
  let p := (BanachSpectrum.comap f.toBoundedRingHom
    (BanachSpectrum.comap g.toBoundedRingHom z)).kernel
  have : q.LiesOver p := ⟨f.kernel_comap _⟩
  have : z.kernel.LiesOver q := ⟨g.kernel_comap z⟩
  have : z.kernel.LiesOver p := ⟨(g.comp f).kernel_comap z⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := Localization.AtPrime.algebraOfLiesOver q z.kernel
  let := Localization.AtPrime.algebraOfLiesOver p z.kernel
  have : Algebra.FiniteType R S := hft
  have : Algebra.IsUnramifiedAt R q := hf
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R (Localization.AtPrime p) (Localization.AtPrime q)
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime z.kernel) := by
    exact hgf
  have hflat : Module.Flat (Localization.AtPrime q) (Localization.AtPrime z.kernel) :=
    Algebra.FormallyUnramified.flat_of_restrictScalars
      (R := Localization.AtPrime p) (S := Localization.AtPrime q) _
  exact hflat

/-- A finite-type unramified first map can be cancelled from a finite-type
composite that is étale at the point. -/
theorem IsEtaleAtPoint.of_comp {f : BoundedAlgHom K R S}
    {g : BoundedAlgHom K S T} (hft : f.toAlgHom.toRingHom.FiniteType)
    (hgft : (g.comp f).toAlgHom.toRingHom.FiniteType)
    {z : BanachSpectrum T}
    (hf : f.IsUnramifiedAtPoint (BanachSpectrum.comap g.toBoundedRingHom z))
    (hgf : (g.comp f).IsEtaleAtPoint z) : g.IsEtaleAtPoint z :=
  ⟨IsFlatAtPoint.of_comp hft hf hgf.1, IsUnramifiedAtPoint.of_comp hgft hgf.2⟩

/-- Pointwise étale cancellation in an actual bounded-map scalar tower.
The carrier universes are independent. -/
def PointwiseEtaleCancellationStatement (K : Type u) [NormedField K] : Prop :=
  ∀ (R : Type v) (S : Type w) (T : Type z)
    [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
    [Algebra K R] [Algebra K S] [Algebra K T]
    (f : BoundedAlgHom K R S) (g : BoundedAlgHom K S T) (s : BanachSpectrum T),
    f.toAlgHom.toRingHom.FiniteType →
      (g.comp f).toAlgHom.toRingHom.FiniteType →
      f.IsUnramifiedAtPoint (BanachSpectrum.comap g.toBoundedRingHom s) →
      (g.comp f).IsEtaleAtPoint s → g.IsEtaleAtPoint s

/-- The pointwise cancellation statement follows from the two local
restriction-of-scalars arguments above. -/
theorem pointwiseEtaleCancellation (K : Type u) [NormedField K] :
    PointwiseEtaleCancellationStatement.{u, v, w, z} K := by
  intro R S T _ _ _ _ _ _ f g s hft hgft hf hgf
  exact IsEtaleAtPoint.of_comp hft hgft hf hgf

end Langlands.Analytic.BoundedAlgHom
