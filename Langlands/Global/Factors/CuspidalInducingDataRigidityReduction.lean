import Langlands.Global.Factors.CuspidalInducingDataRigidityStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Representation.Unramified.ProductInducedSpectrum
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-!
# Rigidity of cuspidal inducing data from Euler constituent recovery

At each finite place where the presentations supply spectra and the hypothesis supplies
a common spherical subquotient, the two block inductions give the same multiset of
eigenvalues. Thus the two sums of spectral systems have the same Euler polynomials.
`CuspidalEulerConstituentRecoveryStatement` then gives the bijection of inducing data.
This implements the proof of Jacquet–Shalika II, Theorem (4.4), p. 809, in Euler-polynomial form.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization PositiveRankCuspidalClass)
open CuspidalPairFunctionalEquation (hasSphericalSpectrum_padicObject)
open CompletionPadic (padicField)
open Unramified (SpectralSystem sphericalSpectrumUniqueness)
open Unramified.ProductInducedSpectrum (exists_hasSphericalSpectrum_of_isSubquotientOf_productInduced)

/-- The canonical matrix topology on `GL_n(F_v)`, as in the statement module. -/
local instance inducingReductionGeneralLinearTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- The passage from the common spherical subquotient to the numerical recovery problem. -/
def CuspidalInducingDataRigidityReductionStatement : Prop :=
  Automorphic.Unramified.CuspidalEulerConstituentRecoveryStatement.{u, uQ} →
    CuspidalInducingDataRigidityStatement.{u, uQ}

/-- Rigidity of cuspidal inducing data from Euler-polynomial recovery of the constituents. -/
theorem cuspidalInducingDataRigidity_of_constituentRecovery :
    CuspidalInducingDataRigidityReductionStatement.{u, uQ} := by
  classical
  intro hrec F _ _ _ r k k' m m' hm hm' T T' P P' h h' S hS
  let c : Fin k → PositiveRankCuspidalClass F := fun i => ⟨m i, (T i).isoClass⟩
  let d : Fin k' → PositiveRankCuspidalClass F := fun j => ⟨m' j, (T' j).isoClass⟩
  let s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank :=
    fun i => (P i).spectralSystem
  let t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank :=
    fun j => (P' j).spectralSystem
  have hc : ∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{u, uQ} (c i) (s i) := fun i =>
    (CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff (T i) _).mpr ⟨P i, rfl⟩
  have hd : ∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{u, uQ} (d j) (t j) := fun j =>
    (CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff (T' j) _).mpr ⟨P' j, rfl⟩
  have hsame : (SpectralSystem.finiteSum s).SameEulerPolynomials (SpectralSystem.finiteSum t) := by
    filter_upwards [S.eventually_cofinite_notMem] with v hvS
    intro hs ht
    have hvi : ∀ i, v ∉ (s i).exceptional := fun i =>
      SpectralSystem.not_mem_exceptional s v hs i
    have hvj : ∀ j, v ∉ (t j).exceptional := fun j =>
      SpectralSystem.not_mem_exceptional t v ht j
    obtain ⟨-, -, A, hAfix, hA, hA'⟩ := hS v hvS
    let inducedSpectrum := exists_hasSphericalSpectrum_of_isSubquotientOf_productInduced (padicField v)
    obtain ⟨u₁, hu₁, hu₁s⟩ := inducedSpectrum r k m hm
      (fun i => ((P i).localComponent v).padicObject (h i v).1 (h i v).2)
      (fun i => (s i).eigenvalues v (hvi i))
      (fun i => hasSphericalSpectrum_padicObject (P i) (h i) v (hvi i)) A hAfix hA
    obtain ⟨u₂, hu₂, hu₂s⟩ := inducedSpectrum r k' m' hm'
      (fun j => ((P' j).localComponent v).padicObject (h' j v).1 (h' j v).2)
      (fun j => (t j).eigenvalues v (hvj j))
      (fun j => hasSphericalSpectrum_padicObject (P' j) (h' j) v (hvj j)) A hAfix hA'
    have hu : u₁ = u₂ := sphericalSpectrumUniqueness _ (padicField v) r A u₁ u₂ hu₁ hu₂
    have hmult : (∑ i, ((s i).eigenvalues v (hvi i) : Multiset ℂˣ)) =
        ∑ j, ((t j).eigenvalues v (hvj j) : Multiset ℂˣ) := by
      calc
        _ = (u₁ : Multiset ℂˣ) := hu₁s.symm
        _ = (u₂ : Multiset ℂˣ) := by rw [hu]
        _ = _ := hu₂s
    exact congrArg (fun z : Multiset ℂˣ =>
      (z.map (fun w : ℂˣ => 1 - Polynomial.C (w : ℂ) * Polynomial.X)).prod) hmult
  exact hrec F k k' c d s t hc hd hsame

end Langlands.Global
