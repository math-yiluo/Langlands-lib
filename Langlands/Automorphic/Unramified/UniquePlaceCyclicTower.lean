import Langlands.LocalFactor.Ramification.InertiaSolvabilityProof
import Langlands.FieldTheory.SolvableGaloisTowerProof
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.ClassField.Global.IdeleSemilocal
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison
import Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower
import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement
import Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCStatement

/-!
# Prime cyclic towers above a place with one place above it

The Galois group of a finite Galois extension of `p`-adic fields is solvable. If a finite
place `v` of a number field `K` has exactly one place `w` of a Galois extension `L` above
it, every element of `Gal(L/K)` fixes `w`, so the decomposition map
`Gal(L_w/K_v) → Gal(L/K)` is onto and `Gal(L/K)` is solvable. A finite Galois extension
with solvable group has a prime cyclic tower. Arthur–Clozel III.4.2(c), general or totally
complex, gives a unitary weak base change along every step of such a tower.
-/

noncomputable section

universe u v uV uW

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Global.AdelicFunctoriality

/-- The ring automorphisms of a finite field of characteristic `p` form a solvable group:
they are the automorphisms over the prime field, an abelian Galois group. -/
theorem isSolvable_ringAut_of_finite (p : ℕ) [Fact p.Prime] (R : Type u)
    [Field R] [Algebra (ZMod p) R] [Finite R] : Group.IsSolvable (RingAut R) := by
  let f : RingAut R →* (R ≃ₐ[ZMod p] R) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) fun x =>
        RingHom.congr_fun (RingHom.ext_zmod
          (σ.toRingHom.comp (algebraMap (ZMod p) R)) (algebraMap (ZMod p) R)) x
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl }
  have hf : Function.Injective f := fun σ τ h => RingEquiv.ext fun x => DFunLike.congr_fun h x
  exact Group.isSolvable_of_isSolvable_injective hf

/-- The automorphisms of a finite extension of `p`-adic fields form a solvable group:
inertia is solvable and the quotient acts faithfully on the finite residue field. -/
theorem isSolvable_localAut {p : ℕ} [Fact p.Prime] {L : PadicField.{u} p}
    (T : L.TopologicalData) (K : Type v) [Field K] [Algebra (Padic p) K]
    [Algebra K L.Carrier] [IsScalarTower (Padic p) K L.Carrier] :
    Group.IsSolvable (L.Carrier ≃ₐ[K] L.Carrier) := by
  let := T.residueAlgebra
  let := T.finite_residueField
  let := isSolvable_ringAut_of_finite p T.ResidueField
  let := Ramification.Padic.isSolvable_inertia T K
  exact Group.isSolvable_of_ker_le_range
    (Ramification.Padic.inertia T K).subtype (Ramification.Padic.residueHom T K)
    (by rw [Subgroup.range_subtype]; exact le_rfl)

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The automorphism group of a completion `L_w` over `K_v` is solvable. -/
theorem isSolvable_completionAut (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    Group.IsSolvable (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
  let := FiniteExtension.towerPadicAlgebra v w
  let := CompletionPadic.padicAlgebra v
  have : IsScalarTower (Padic (CompletionPadic.residuePrime v)) (v.adicCompletion K)
      (w.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact isSolvable_localAut (L := FiniteExtension.towerPadicField v w)
    (FiniteExtension.towerTopologicalData v w) (v.adicCompletion K)

/-- If a finite place `v` of `K` has exactly one place of the Galois extension `L` above it,
then `Gal(L/K)` is solvable. -/
theorem isSolvable_of_hasUniquePlaceAbove [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (h : Harris.HasUniquePlaceAbove L v) : Group.IsSolvable (L ≃ₐ[K] L) := by
  obtain ⟨w, hw⟩ := exists_place_above (L := L) v
  have hsurj : Function.Surjective (ClassField.Global.FundamentalClass.decompositionHom v w) := by
    intro g
    have hg : g ∈ (ClassField.Global.FundamentalClass.decompositionHom v w).range := by
      rw [ClassField.Global.mem_range_decompositionHom_iff]
      have hw' := Harris.finitePlaceEquiv_liesOver (RingEquiv.refl K) g.toRingEquiv g.commutes
        v w
      simp only [finitePlaceEquiv_refl, Equiv.refl_apply] at hw'
      exact h _ w hw' hw
    exact hg
  have := isSolvable_completionAut v w
  exact Group.isSolvable_of_surjective hsurj

end Langlands.Global.AdelicFunctoriality

namespace Langlands.Automorphic.Unramified

open Langlands.Global

namespace PrimeCyclicBaseChangeTower

/-- A finite Galois extension of number fields with solvable Galois group has a prime cyclic
tower. -/
theorem nonempty_of_isSolvable (F : Type u) (K : Type v) [Field F] [Field K]
    [NumberField F] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [Group.IsSolvable (K ≃ₐ[F] K)] : Nonempty (PrimeCyclicBaseChangeTower F K) := by
  obtain ⟨n, T, h0, htop, hsteps⟩ := Langlands.FieldTheory.solvableGaloisPrimeTower F K
  have hle : ∀ i : Fin n, T i.castSucc ≤ T i.succ := fun i => (hsteps i).1
  refine ⟨⟨n, T, Fin.monotone_iff_le_succ.mpr hle, h0, htop, fun i => ?_⟩⟩
  obtain ⟨_, _, hG, hC, hp⟩ := hsteps i
  exact ⟨hG, hC, hp⟩

variable {F K : Type u} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
  (T : PrimeCyclicBaseChangeTower F K) [∀ i, CompactSpace (AdeleQuotient (T.level i))]

/-- Arthur–Clozel III.4.2(c) gives a unitary weak base change along every step of a prime
cyclic tower. -/
theorem exists_weakBaseChange_step
    (hBC : CyclicPrimeIsobaricBaseChangeStatement.{u, u, uV, uW})
    (i : Fin T.length) (DF : IsobaricData (T.level i.castSucc)) (hDF : DF.IsUnitary) :
    ∃ DE : IsobaricData (T.level i.succ), DE.IsUnitary ∧
      letI := T.stepAlgebra i
      IsobaricData.IsWeakBaseChangeOf.{u, u, uV, uW} DE DF := by
  let := T.stepAlgebra i
  obtain ⟨hG, -, hp⟩ := T.primeCyclic_step i
  obtain ⟨DE, h1, h2, -⟩ := hBC (T.level i.castSucc) (T.level i.succ) hp DF hDF
  exact ⟨DE, h1, h2⟩

/-- The totally complex form of `exists_weakBaseChange_step`: over a totally complex base,
the totally complex form of Arthur–Clozel III.4.2(c) suffices, since every level is
totally complex. -/
theorem exists_weakBaseChange_step_of_isTotallyComplex [IsTotallyComplex F]
    (hBC : CyclicPrimeIsobaricBaseChangeTCStatement.{u, u, uV, uW})
    (i : Fin T.length) (DF : IsobaricData (T.level i.castSucc)) (hDF : DF.IsUnitary) :
    ∃ DE : IsobaricData (T.level i.succ), DE.IsUnitary ∧
      letI := T.stepAlgebra i
      IsobaricData.IsWeakBaseChangeOf.{u, u, uV, uW} DE DF := by
  let := T.stepAlgebra i
  have : IsTotallyComplex (T.level i.castSucc) := isTotallyComplex_of_algebra F _
  obtain ⟨hG, -, hp⟩ := T.primeCyclic_step i
  obtain ⟨DE, h1, h2, -⟩ := hBC (T.level i.castSucc) (T.level i.succ) hp DF hDF
  exact ⟨DE, h1, h2⟩

end PrimeCyclicBaseChangeTower

end Langlands.Automorphic.Unramified
