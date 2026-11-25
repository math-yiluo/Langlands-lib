import Langlands.ClassFieldTheory.Global.InvariantProof
import Langlands.GaloisCohomology.Global.BrauerSequence.Hasse

/-!
# The global invariant on idèle-class cohomology, and lifting idèle classes to idèles

`ideleClassInvariant` is the Library's global invariant `inv_{E/F} : H²(Gal(E/F), C_E) → ℚ/ℤ`
(`assembledIdeleClassInvariantMaps`, as in the proof of `globalInvariantStatement`), built from the
local invariant family `brauerInvariantFamily`: it is injective with image `(1/[E:F])ℤ/ℤ`, it is
invariant under inflation, and on the image of `H²(Gal(E/F), J_E)` it is the sum of the local
invariants of the idèle class (`ideleClassInvariant_ideleQuotient`).

If some finite place `v` of `F` has local degree in `L` divisible by `[E : F]`, then every class
of `H²(Gal(E/F), C_E)` becomes, after inflation to `L`, the image of a class of
`H²(Gal(L/F), J_L)`, namely of the local section at `v` of the local class with the same invariant
(`relativeIdeleClassInflation_mem_range`). This is the surjectivity of `H²(G_K, I) → H²(G_K, C)` in
the limit (Neukirch–Schmidt–Wingberg (8.1.20)), at the finite levels where it is needed.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic FundamentalClass
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

/-- The relative images of `brauerInvariantFamily`. -/
theorem brauerInvariantFamily_relativeImages (p : ℕ) [Fact p.Prime] :
    (brauerInvariantFamily.{u} p).RelativeImages :=
  (brauerInvariantFamily_spec p).1.2.1

/-- The total idèle invariant (sum of the local invariants) of `brauerInvariantFamily`. -/
abbrev brauerTotalIdeleInvariant : IdeleInvariantMaps.{u} :=
  totalIdeleInvariantMaps brauerInvariantFamily.{u} brauerInvariantFamily_relativeImages

/-- **The global invariant** `H²(Gal(E/F), C_E) → ℚ/ℤ` of the Library's class field theory, relative
to `brauerInvariantFamily`. -/
def ideleClassInvariant : GlobalInvariantMaps.{u} :=
  assembledIdeleClassInvariantMaps brauerTotalIdeleInvariant
    (totalIdeleInvariantMaps_killsQuotientKernel_of_h1 brauerInvariantFamily
      brauerInvariantFamily_relativeImages ideleClassH1Vanishing
      fun p _ => (brauerInvariantFamily_spec p))
    (totalIdeleInvariantMaps_inflation_of_inflationCompatibility brauerInvariantFamily
      (fun p _ => (brauerInvariantFamily_spec p).1.2.2.1) brauerInvariantFamily_relativeImages)
    (totalIdeleInvariantMaps_restriction_of_localLaws brauerInvariantFamily
      (fun p _ => (brauerInvariantFamily_spec p).1.2.2.2)
      (fun p _ => (brauerInvariantFamily_spec p).1.2.2.1) brauerInvariantFamily_relativeImages)
    (totalIdeleInvariantMaps_cyclicRange brauerInvariantFamily
      brauerInvariantFamily_relativeImages Langlands.Global.cyclicPrimePowerLocalDegreeStatement)
    ideleClassGaloisDescent ideleClassH1Vanishing ideleClassH2OrderBound

/-- The global invariant is injective with image `(1/[E:F])ℤ/ℤ`. -/
theorem ideleClassInvariant_images : InvariantImages ideleClassInvariant.{u} :=
  assembledIdeleClassInvariantMaps_images _ _ _ _ _ _ _ _

/-- The global invariant is invariant under inflation. -/
theorem ideleClassInvariant_inflation : InvariantInflationOnClasses ideleClassInvariant.{u} :=
  assembledIdeleClassInvariantMaps_inflation _ _ _ _ _ _ _ _

/-- On the image of idèle cohomology the global invariant is the total local invariant. -/
theorem ideleClassInvariant_ideleQuotient (F E : Type u) [Field F] [Field E] [NumberField F]
    [NumberField E] [Algebra F E] [IsGalois F E] (a : relativeIdeleCohomology F E 2) :
    ideleClassInvariant F E (ideleQuotientCohomologyMap F E 2 a) = brauerTotalIdeleInvariant F E a :=
  assembledIdeleClassInvariantMaps_apply_quotient _ _ _ _ _ _ _ _ F E a

/-- `(1/m)ℤ/ℤ ⊆ (1/n)ℤ/ℤ` when `m ∣ n`. -/
theorem denominatorSubgroup_le_of_dvd {m n : ℕ} (h : m ∣ n) :
    denominatorSubgroup m ≤ denominatorSubgroup n := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  change (m * k) • x = 0
  change m • x = 0 at hx
  rw [mul_nsmul, hx, nsmul_zero]

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

/-- **Lifting idèle classes after inflation.** Let `F ⊆ E ⊆ L` be finite Galois over `F`, and `v`
a finite place of `F` whose local degree at the chosen place of `L` above it is divisible by
`[E : F]`. Then the inflation to `L` of every class of `H²(Gal(E/F), C_E)` is the image of a class
of `H²(Gal(L/F), J_L)`. -/
theorem relativeIdeleClassInflation_mem_range {F E L : Type u} [Field F] [Field E] [Field L]
    [NumberField F] [NumberField E] [NumberField L] [Algebra F E] [Algebra F L] [Algebra E L]
    [IsScalarTower F E L] [IsGalois F E] [IsGalois F L] (v : HeightOneSpectrum (𝓞 F))
    (hv : Module.finrank F E ∣
      Module.finrank (padicField v).Carrier ((placeAbove L v).1.adicCompletion L))
    (c : relativeIdeleClassCohomology F E 2) :
    ∃ a : relativeIdeleCohomology F L 2,
      ideleQuotientCohomologyMap F L 2 a = relativeIdeleClassInflation F E L 2 c := by
  classical
  have := (placeAbove L v).2
  let _ : Fintype ((L ≃ₐ[F] L) ⧸ (decompositionHom v (placeAbove L v).1).range) :=
    Fintype.ofFinite _
  -- the invariant of `c` is a local invariant at `v`
  have hc : ideleClassInvariant F E c ∈ denominatorSubgroup (Module.finrank F E) := by
    rw [← (ideleClassInvariant_images F E).2]
    exact ⟨c, rfl⟩
  have hloc := ((brauerInvariantFamily_relativeImages (residuePrime v)) (padicField v)
    ((placeAbove L v).1.adicCompletion L)).2
  obtain ⟨z, hz⟩ : ideleClassInvariant F E c ∈
      ((brauerInvariantFamily (residuePrime v)).relative (padicField v)
        ((placeAbove L v).1.adicCompletion L)).range := by
    rw [hloc]
    exact denominatorSubgroup_le_of_dvd hv hc
  refine ⟨ideleLocalSection v (placeAbove L v).1 2 z, ?_⟩
  apply (ideleClassInvariant_images F L).1
  rw [ideleClassInvariant_ideleQuotient, ideleClassInvariant_inflation,
    totalIdeleInvariantMaps_ideleLocalSection]
  exact hz

end

end Langlands.GaloisCohomology
