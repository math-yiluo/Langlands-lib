import Langlands.CommutativeAlgebra.HomogenizedPolynomialKernels
import Langlands.CommutativeAlgebra.EtaleValuationProjectiveDimension
import Mathlib.RingTheory.FinitePresentation

/-! # Coherence of finitely presented valuation algebras -/

universe u v w

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R]

/-- The actual map from the inverse image of a submodule to that submodule. -/
def submodulePresentationPullbackMap
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (K : Submodule R N) : K.comap f →ₗ[R] K :=
  (f.domRestrict (K.comap f)).codRestrict K fun x => x.property

theorem submodulePresentationPullbackMap_surjective
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (K : Submodule R N) (hf : Function.Surjective f) :
    Function.Surjective (submodulePresentationPullbackMap f K) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨⟨y, by change f y ∈ K; rw [hy]; exact x.property⟩, Subtype.ext hy⟩

/-- Finite submodules of any finitely presented module are finitely presented
over a ring satisfying finite-free-submodule coherence. -/
theorem finitePresentation_fg_submodule_of_finitePresentation
    (hR : FiniteFreeSubmoduleCoherent R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (K : Submodule R M) (hK : K.FG) :
    Module.FinitePresentation R K := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let L := K.comap f
  have hker : (LinearMap.ker f).FG := Module.FinitePresentation.fg_ker f hf
  have hkerL : LinearMap.ker f ≤ L := by
    intro x hx
    change f x ∈ K
    rw [LinearMap.mem_ker.mp hx]
    exact K.zero_mem
  have hL : L.FG := Submodule.fg_of_fg_map_of_fg_inf_ker f
    (by simpa [L, Submodule.map_comap_eq_of_surjective hf] using hK)
    (by simpa [inf_eq_right.mpr hkerL] using hker)
  have : Module.FinitePresentation R L := hR n L hL
  let g : L →ₗ[R] K := submodulePresentationPullbackMap f K
  have hg : Function.Surjective g := submodulePresentationPullbackMap_surjective f K hf
  have hkg : (LinearMap.ker g).FG := by
    apply Submodule.fg_of_fg_map_injective L.subtype L.injective_subtype
    have heq : (LinearMap.ker g).map L.subtype = LinearMap.ker f := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact congr_arg Subtype.val (LinearMap.mem_ker.mp hy)
      · intro hx
        refine ⟨⟨x, hkerL hx⟩, ?_, rfl⟩
        apply LinearMap.mem_ker.mpr
        exact Subtype.ext (LinearMap.mem_ker.mp hx)
    rwa [heq]
  exact Module.finitePresentation_of_surjective g hg hkg

/-- A coefficient-finitely-presented module is finitely presented over a
coefficient-finitely-presented algebra acting compatibly on it. -/
theorem finitePresentation_of_finitePresentation_restrictScalars
    {S : Type v} [CommRing S] [Algebra R S] [Module.FinitePresentation R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.FinitePresentation R M] :
    Module.FinitePresentation S M := by
  have : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  exact Module.finitePresentation_of_free_of_surjective f hf
    (Submodule.FG.of_restrictScalars R
      (Module.FinitePresentation.fg_ker (f.restrictScalars R) hf))

/-- Coherence passes to any algebra finitely presented as a coefficient module. -/
theorem finiteFreeSubmoduleCoherent_of_module_finitePresentation
    (hR : FiniteFreeSubmoduleCoherent R)
    (S : Type v) [CommRing S] [Algebra R S] [Module.FinitePresentation R S] :
    FiniteFreeSubmoduleCoherent S := by
  intro n K hK
  have hKR : (K.restrictScalars R).FG := hK.restrictScalars
  have : Module.FinitePresentation R (K.restrictScalars R) :=
    finitePresentation_fg_submodule_of_finitePresentation hR _ hKR
  have : Module.FinitePresentation R K :=
    Module.FinitePresentation.of_equiv ((K.restrictScalarsEquiv R).restrictScalars R)
  exact finitePresentation_of_finitePresentation_restrictScalars (R := R) K

/-- Every finitely presented algebra over an arbitrary valuation domain is
coherent in the finite-free-submodule sense. -/
theorem finiteFreeSubmoduleCoherent_of_finitePresentation_of_valuationRing
    [IsDomain R] [ValuationRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] :
    FiniteFreeSubmoduleCoherent S := by
  obtain ⟨n, f, hf, hker⟩ :=
    Algebra.FinitePresentation.out (R := R) (A := S)
  let : Algebra (MvPolynomial (Fin n) R) S := f.toRingHom.toAlgebra
  have : Module.FinitePresentation (MvPolynomial (Fin n) R) S :=
    Module.finitePresentation_of_free_of_surjective
      (Algebra.linearMap (MvPolynomial (Fin n) R) S) hf hker
  exact finiteFreeSubmoduleCoherent_of_module_finitePresentation
    (finiteFreeSubmoduleCoherent_mvPolynomial_of_valuationRing (R := R) (σ := Fin n)) S

/-- Etale polynomial charts over arbitrary valuation domains have coherence
and finite projective dimension for all finitely presented modules. -/
theorem finitelyPresentedRegularRing_etale_mvPolynomial_of_valuationRing
    [IsDomain R] [ValuationRing R]
    {σ : Type u} [Finite σ] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra (MvPolynomial σ R) S]
    [IsScalarTower R (MvPolynomial σ R) S]
    [Algebra.Etale (MvPolynomial σ R) S] :
    FinitelyPresentedRegularRing S := by
  have : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.trans R (MvPolynomial σ R) S
  exact ⟨finiteFreeSubmoduleCoherent_of_finitePresentation_of_valuationRing (R := R) S,
    finiteProjectiveDimensionForFinitelyPresentedModules_etale_mvPolynomial_of_valuationRing
      (R := R) (σ := σ)⟩

end Langlands.CommutativeAlgebra
