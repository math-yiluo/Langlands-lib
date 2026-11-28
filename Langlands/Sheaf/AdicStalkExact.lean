import Langlands.MathlibBase
import WeilConjectures.SixFunctors.ProEtale.Adic.SubobjectStalk

/-!
# Exactness of the stalk functor on `ℓ`-adic sheaves

At a geometric point `t : Spec Ω̄ ⟶ Y`, the stalk functor on `ℓ`-adic sheaves preserves finite
limits and epimorphisms (weil-conjectures's instances in
`WeilConjectures.SixFunctors.ProEtale.Adic.SubobjectStalk`), so it preserves homology, and the
stalk maps of a short exact sequence of `ℓ`-adic sheaves form a short exact sequence of
`ℚ̄_ℓ`-vector spaces (`AlgebraicGeometry.ProEtale.adicStalkMap_shortExact`).
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- **The stalk maps of a short exact sequence of `ℓ`-adic sheaves are short exact.** -/
theorem adicStalkMap_shortExact (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    {S : ShortComplex (AdicSheaf l Y)} (hS : S.ShortExact) :
    Function.Injective (adicStalkMap t S.f) ∧ Function.Surjective (adicStalkMap t S.g) ∧
      LinearMap.range (adicStalkMap t S.f) = LinearMap.ker (adicStalkMap t S.g) := by
  have := hS.mono_f
  have := hS.epi_g
  refine ⟨injective_adicStalkMap t S.f, surjective_adicStalkMap t S.g, ?_⟩
  have : (adicStalkFunctor l t).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hex := hS.exact.map (adicStalkFunctor l t)
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  ext x
  have := SetLike.ext_iff.1 hex x
  simp only [LinearMap.mem_range, LinearMap.mem_ker] at this ⊢
  exact this

end AlgebraicGeometry.ProEtale
