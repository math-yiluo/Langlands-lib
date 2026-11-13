import Langlands.Geometry.FormalGroup.KernelPoints
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Finite locally free kernels and rank-based isogeny heights -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom

/-- The underlying set functor of the actual point kernel. -/
def kernelSetFunctor (f : Hom M N) : CommAlgCat.{v} R ⥤ Type v :=
  f.kernelPointFunctor ⋙ forget (ModuleCat.{v} O)

/-- A finite projective algebra naturally corepresenting the actual kernel.
The natural equivalence is a required part of the representation. -/
structure FiniteKernelModel (f : Hom M N) where
  coordinateAlgebra : CommAlgCat.{v} R
  finite : Module.Finite R coordinateAlgebra
  projective : Module.Projective R coordinateAlgebra
  represents : f.kernelSetFunctor.CorepresentableBy coordinateAlgebra

attribute [instance] FiniteKernelModel.finite FiniteKernelModel.projective

namespace FiniteKernelModel

variable {f : Hom M N}

/-- Uniqueness of the coordinate algebra follows from the actual kernel functor. -/
def coordinateIso (K L : FiniteKernelModel f) :
    K.coordinateAlgebra ≅ L.coordinateAlgebra :=
  K.represents.uniqueUpToIso L.represents

/-- Rank of the kernel's finite projective coordinate module at a base prime. -/
def rank (K : FiniteKernelModel f) : PrimeSpectrum R → ℕ :=
  Module.rankAtStalk (R := R) K.coordinateAlgebra

/-- The rank does not depend on the chosen representation of the kernel. -/
theorem rank_eq (K L : FiniteKernelModel f) : K.rank = L.rank :=
  Module.rankAtStalk_eq_of_equiv
    (CommAlgCat.algEquivOfIso (K.coordinateIso L)).toLinearEquiv

/-- Finite locally free kernel ranks vary locally constantly on the base. -/
theorem isLocallyConstant_rank (K : FiniteKernelModel f) : IsLocallyConstant K.rank := by
  let := Module.finitePresentation_of_projective R K.coordinateAlgebra
  exact Module.isLocallyConstant_rankAtStalk

end FiniteKernelModel

/-- The actual point kernel is represented by a finite locally free affine algebra. -/
def HasFiniteLocallyFreeKernel (f : Hom M N) : Prop :=
  Nonempty (FiniteKernelModel f)

/-- Constant rank of the actual represented kernel; no rank datum is supplied. -/
def HasKernelRank (f : Hom M N) (n : ℕ) : Prop :=
  ∃ K : FiniteKernelModel f, ∀ p : PrimeSpectrum R, K.rank p = n

theorem HasKernelRank.finiteLocallyFree {f : Hom M N} {n : ℕ}
    (h : f.HasKernelRank n) : f.HasFiniteLocallyFreeKernel :=
  ⟨h.choose⟩

/-- A rank condition can be checked on any representation of the actual kernel. -/
theorem hasKernelRank_iff (f : Hom M N) (K : FiniteKernelModel f) (n : ℕ) :
    f.HasKernelRank n ↔ ∀ p : PrimeSpectrum R, K.rank p = n := by
  constructor
  · rintro ⟨L, hL⟩ p
    rw [K.rank_eq L]
    exact hL p
  · exact fun h => ⟨K, h⟩

/-- Constant ranks are unique when the base has a prime. -/
theorem HasKernelRank.unique [Nontrivial R] {f : Hom M N} {m n : ℕ}
    (hm : f.HasKernelRank m) (hn : f.HasKernelRank n) : m = n := by
  obtain ⟨K, hK⟩ := hm
  obtain ⟨L, hL⟩ := hn
  let p : PrimeSpectrum R := Classical.choice inferInstance
  exact (hK p).symm.trans ((congrFun (K.rank_eq L) p).trans (hL p))

/-- Every actual target point lifts after a faithfully flat finitely presented
extension of its test algebra. This is the affine fppf local-lifting condition. -/
def IsFppfLocallySurjective (f : Hom M N) : Prop :=
  ∀ (A : CommAlgCat.{v} R) (y : N.AlgebraPoint A),
    ∃ (B : CommAlgCat.{v} R) (φ : A ⟶ B),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧
        ∃ x : M.AlgebraPoint B, f.onAlgebraPoints x = N.algebraMapPoints φ.hom y

/-- The affine point-functor isogeny condition: fppf local lifting and an actual
finite locally free represented kernel. -/
def IsIsogeny (f : Hom M N) : Prop :=
  f.IsFppfLocallySurjective ∧ f.HasFiniteLocallyFreeKernel

/-- Height h means constant kernel rank q^h, together with the isogeny condition.
For a p-divisible group q is p; the formal O-module normalization uses the residue cardinality. -/
def HasHeight (f : Hom M N) (q h : ℕ) : Prop :=
  f.IsIsogeny ∧ f.HasKernelRank (q ^ h)

theorem HasHeight.unique [Nontrivial R] {f : Hom M N} {q h k : ℕ}
    (hq : 2 ≤ q) (hh : f.HasHeight q h) (hk : f.HasHeight q k) : h = k :=
  Nat.pow_right_injective hq (hh.2.unique hk.2)

end Hom

end Langlands.FormalGroup.ModuleLaw
