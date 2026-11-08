import Langlands.Geometry.Analytic.FiniteEtaleAlgebra
import Langlands.Geometry.Analytic.Spectrum.Properties
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Unramified.Locus

/-! # Flatness, unramifiedness and étaleness of bounded affinoid maps at spectrum points -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BanachSpectrum

variable {A : Type v} [NormedCommRing A]

/-- The kernel of a bounded multiplicative seminorm is a prime ideal. -/
instance kernel.isPrime (x : BanachSpectrum A) : x.kernel.IsPrime :=
  kernel_isPrime x

end BanachSpectrum

namespace BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w} {T : Type z}
  [NormedField K] [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [Algebra K R] [Algebra K S] [Algebra K T]

/-- The prime ideal of the image point is the preimage of the prime ideal of
the point. -/
theorem kernel_comap (f : BoundedAlgHom K R S) (y : BanachSpectrum S) :
    (BanachSpectrum.comap f.toBoundedRingHom y).kernel =
      y.kernel.comap f.toAlgHom.toRingHom :=
  Ideal.ext fun _ => Iff.rfl

/-- Flatness at a point, in the form of Berkovich's Proposition 3.2.1: the
localization of the target at the prime of `y` is flat over the localization
of the source at the prime of the image point. -/
def IsFlatAtPoint (f : BoundedAlgHom K R S) (y : BanachSpectrum S) : Prop :=
  (Localization.localRingHom (BanachSpectrum.comap f.toBoundedRingHom y).kernel y.kernel
    f.toAlgHom.toRingHom (f.kernel_comap y)).Flat

/-- Unramifiedness at a point: `y` lies outside the support of the module of
differentials, that is, the annihilator of `Ω[S⁄R]` is not contained in the
prime of `y`. -/
def IsUnramifiedAtPoint (f : BoundedAlgHom K R S) (y : BanachSpectrum S) : Prop :=
  letI : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  ¬ Module.annihilator S Ω[S⁄R] ≤ y.kernel

/-- Flat and unramified at the point. -/
def IsEtaleAtPoint (f : BoundedAlgHom K R S) (y : BanachSpectrum S) : Prop :=
  f.IsFlatAtPoint y ∧ f.IsUnramifiedAtPoint y

/-- For maps of finite type, unramifiedness at a point is Mathlib's
unramifiedness at the prime of the point: the localization is formally
unramified. -/
theorem isUnramifiedAtPoint_iff_isUnramifiedAt (f : BoundedAlgHom K R S)
    (hf : f.toAlgHom.toRingHom.FiniteType) (y : BanachSpectrum S) :
    f.IsUnramifiedAtPoint y ↔
      (letI : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
       Algebra.IsUnramifiedAt R y.kernel) := by
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  have : Algebra.FiniteType R S := hf
  change ¬ Module.annihilator S Ω[S⁄R] ≤ y.kernel ↔
    (⟨y.kernel, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff,
    Module.mem_support_iff_of_finite]

/-- Flat maps are flat at every point (the "in particular" of Proposition
3.2.1, in the easy direction). -/
theorem isFlatAtPoint_of_flat (f : BoundedAlgHom K R S) (hf : f.toAlgHom.toRingHom.Flat)
    (y : BanachSpectrum S) : f.IsFlatAtPoint y :=
  hf.localRingHom y.kernel _ (f.kernel_comap y)

/-- Formally unramified maps are unramified at every point: the module of
differentials vanishes, so its annihilator is the unit ideal. -/
theorem isUnramifiedAtPoint_of_formallyUnramified (f : BoundedAlgHom K R S)
    (hf : f.toAlgHom.toRingHom.FormallyUnramified) (y : BanachSpectrum S) :
    f.IsUnramifiedAtPoint y := by
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  have : Algebra.FormallyUnramified R S := hf
  change ¬ Module.annihilator S Ω[S⁄R] ≤ y.kernel
  rw [Module.annihilator_eq_top_iff.mpr inferInstance, top_le_iff]
  exact (BanachSpectrum.kernel.isPrime y).ne_top

/-- Algebraically finite étale bounded maps are étale at every point. -/
theorem AlgebraicallyFiniteEtale.isEtaleAtPoint {f : BoundedAlgHom K R S}
    (hf : f.AlgebraicallyFiniteEtale) (y : BanachSpectrum S) : f.IsEtaleAtPoint y := by
  obtain ⟨-, hflat, hunr, -⟩ := (algebraicallyFiniteEtale_iff f).1 hf
  exact ⟨f.isFlatAtPoint_of_flat hflat y, f.isUnramifiedAtPoint_of_formallyUnramified hunr y⟩

theorem isEtaleAtPoint_id (y : BanachSpectrum R) : (BoundedAlgHom.id K R).IsEtaleAtPoint y :=
  algebraicallyFiniteEtale_id.isEtaleAtPoint y

theorem isFlatAtPoint_id (y : BanachSpectrum R) : (BoundedAlgHom.id K R).IsFlatAtPoint y :=
  (isEtaleAtPoint_id y).1

theorem isUnramifiedAtPoint_id (y : BanachSpectrum R) :
    (BoundedAlgHom.id K R).IsUnramifiedAtPoint y :=
  (isEtaleAtPoint_id y).2

/-- Flatness at points composes: the local homomorphism of the composite is the
composite of the local homomorphisms. -/
theorem IsFlatAtPoint.comp {g : BoundedAlgHom K S T} {f : BoundedAlgHom K R S}
    {z : BanachSpectrum T} (hg : g.IsFlatAtPoint z)
    (hf : f.IsFlatAtPoint (BanachSpectrum.comap g.toBoundedRingHom z)) :
    (g.comp f).IsFlatAtPoint z := by
  unfold IsFlatAtPoint at hg hf ⊢
  have key : Localization.localRingHom (BanachSpectrum.comap (g.comp f).toBoundedRingHom z).kernel
      z.kernel (g.comp f).toAlgHom.toRingHom ((g.comp f).kernel_comap z) =
      (Localization.localRingHom (BanachSpectrum.comap g.toBoundedRingHom z).kernel z.kernel
        g.toAlgHom.toRingHom (g.kernel_comap z)).comp
        (Localization.localRingHom
          (BanachSpectrum.comap f.toBoundedRingHom
            (BanachSpectrum.comap g.toBoundedRingHom z)).kernel
          (BanachSpectrum.comap g.toBoundedRingHom z).kernel f.toAlgHom.toRingHom
          (f.kernel_comap _)) :=
    Localization.localRingHom_comp _ _ _ _ (f.kernel_comap _) _ (g.kernel_comap z)
  rw [key]
  exact hf.comp hg

/-- Unramifiedness at points composes for maps of finite type, through
Mathlib's composition law for unramifiedness at primes. -/
theorem IsUnramifiedAtPoint.comp {g : BoundedAlgHom K S T} {f : BoundedAlgHom K R S}
    (hgt : g.toAlgHom.toRingHom.FiniteType) (hft : f.toAlgHom.toRingHom.FiniteType)
    {z : BanachSpectrum T} (hg : g.IsUnramifiedAtPoint z)
    (hf : f.IsUnramifiedAtPoint (BanachSpectrum.comap g.toBoundedRingHom z)) :
    (g.comp f).IsUnramifiedAtPoint z := by
  rw [isUnramifiedAtPoint_iff_isUnramifiedAt _ hgt] at hg
  rw [isUnramifiedAtPoint_iff_isUnramifiedAt _ hft] at hf
  rw [isUnramifiedAtPoint_iff_isUnramifiedAt _ (hgt.comp hft)]
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra S T := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra R T := (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : z.kernel.LiesOver (BanachSpectrum.comap g.toBoundedRingHom z).kernel :=
    ⟨g.kernel_comap z⟩
  have : Algebra.IsUnramifiedAt R (BanachSpectrum.comap g.toBoundedRingHom z).kernel := hf
  have : Algebra.IsUnramifiedAt S z.kernel := hg
  exact Algebra.IsUnramifiedAt.comp (R := R)
    (BanachSpectrum.comap g.toBoundedRingHom z).kernel z.kernel

/-- Étaleness at points composes for maps of finite type. -/
theorem IsEtaleAtPoint.comp {g : BoundedAlgHom K S T} {f : BoundedAlgHom K R S}
    (hgt : g.toAlgHom.toRingHom.FiniteType) (hft : f.toAlgHom.toRingHom.FiniteType)
    {z : BanachSpectrum T} (hg : g.IsEtaleAtPoint z)
    (hf : f.IsEtaleAtPoint (BanachSpectrum.comap g.toBoundedRingHom z)) :
    (g.comp f).IsEtaleAtPoint z :=
  ⟨hg.1.comp hf.1, IsUnramifiedAtPoint.comp hgt hft hg.2 hf.2⟩

end BoundedAlgHom

end Langlands.Analytic
