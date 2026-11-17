import Langlands.Automorphic.IsobaricData
import Langlands.Global.CompletionPadicTower
import Langlands.Correspondence.SupercuspidalRelations
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # Actual local components and supercuspidal support of isobaric data

Internal attachment relations on actual global cuspidal realizations, their
spectral presentations, and actual smooth representations over an identified
p-adic completion. No existence, uniqueness, or base change is asserted.
-/

noncomputable section

open scoped BigOperators

universe uF uP uK uR uV

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Repackage a successor rank and its genuine supercuspidal class as local
cuspidal data, retaining exactly the same class. -/
def supercuspidalSupportDatum
    (a : Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    K.canonicalTopologicalData.CuspidalDatum.{uV, uK} where
  rank := a.1 + 1
  rank_pos := Nat.succ_pos _
  cls := a.2

@[simp]
theorem supercuspidalSupportDatum_rank
    (a : Σ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    (supercuspidalSupportDatum K a).rank = a.1 + 1 := rfl

end Langlands.Correspondence

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance localSupportRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localSupportContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localSupportSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localSupportFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance localSupportSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace CuspidalOperatorRealization.IsoClass

variable {r : ℕ}

/-- An actual local component after identifying the supplied p-adic field with
the actual completion. The equivalence compares the original form-space action
with `ρ`, even when their carriers lie in different universes. -/
def HasPadicLocalComponent (c : IsoClass F r) (v : FinitePlace F)
    {p : ℕ} [Fact p.Prime] (hp : CompletionPadic.residuePrime v = p)
    (K : PadicField.{uK} p)
    (α : letI := (CompletionPadic.padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt v hp).Carrier)
    (ρ : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, uK, uR} ℂ (GeneralLinear (r + 1) K.Carrier)) : Prop :=
  letI := (CompletionPadic.padicFieldAt v hp).algebra
  letI := K.canonicalTopologicalData.topology
  letI := (CompletionPadic.padicFieldAt v hp).canonicalTopologicalData.topology
  ∃ (S : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{uF, uP} S),
    S.isoClass = c ∧
      Nonempty (Representation.Equiv ((P.localComponent v).representation.comp
        (GeneralLinear.fieldEquiv (r + 1) α.toRingEquiv
          (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv
            K (CompletionPadic.padicFieldAt v hp) α)
          (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv
            (CompletionPadic.padicFieldAt v hp) K α.symm)).toMonoidHom)
        ρ.representation)

/-- Some actual supercuspidal representative of the specified genuine class
is an actual local component after the field identification. -/
def HasPadicSupercuspidalClass (c : IsoClass F r) (v : FinitePlace F)
    {p : ℕ} [Fact p.Prime] (hp : CompletionPadic.residuePrime v = p)
    (K : PadicField.{uK} p)
    (α : letI := (CompletionPadic.padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt v hp).Carrier)
    (π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K r.succPNat) : Prop :=
  letI := K.canonicalTopologicalData.topology
  ∃ A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := r + 1),
    A.isoClass = π ∧ HasPadicLocalComponent.{uF, uP, uK, uV} c v hp K α A.obj

end CuspidalOperatorRealization.IsoClass

namespace IsobaricData

/-- Enumerate every global constituent with multiplicity, attach an actual
local component to each, and sum their actual supercuspidal supports with
multiplicity. The local supports may have several smaller-rank terms. -/
def HasLocalSupercuspidalSupport (D : IsobaricData F) (v : FinitePlace F)
    {p : ℕ} [Fact p.Prime] (hp : CompletionPadic.residuePrime v = p)
    (K : PadicField.{uK} p)
    (α : letI := (CompletionPadic.padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt v hp).Carrier)
    (s : Multiset (Σ k : ℕ,
      Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat)) : Prop :=
  letI := K.canonicalTopologicalData.topology
  ∃ (b : ℕ) (σ : Fin b → PositiveRankCuspidalClass F)
    (_ : Finset.univ.val.map σ = D)
    (ρ : ∀ j, SmoothRep.{0, uK, max uK uV} ℂ (GeneralLinear (σ j).rank K.Carrier))
    (t : Fin b → Multiset (Σ k : ℕ,
      Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat)),
    (∀ j, CuspidalOperatorRealization.IsoClass.HasPadicLocalComponent.{uF, uP,
      uK, max uK uV} (σ j).2 v hp K α (ρ j)) ∧
    (∀ j, K.canonicalTopologicalData.IsSupercuspidalSupport (ρ j)
      ((t j).map (Correspondence.supercuspidalSupportDatum K))) ∧
    s = ∑ j, t j

/-- The ranks of all local support constituents add up to the global datum's
rank, retaining both global and local multiplicities. -/
theorem HasLocalSupercuspidalSupport.sum_rank
    {D : IsobaricData F} {v : FinitePlace F} {p : ℕ} [Fact p.Prime]
    {hp : CompletionPadic.residuePrime v = p} {K : PadicField.{uK} p}
    {α : letI := (CompletionPadic.padicFieldAt v hp).algebra
      K.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt v hp).Carrier}
    {s : Multiset (Σ k : ℕ,
      Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat)}
    (hs : HasLocalSupercuspidalSupport.{uF, uP, uK, uV} D v hp K α s) :
    (s.map (fun a => a.1 + 1)).sum = D.rank := by
  obtain ⟨b, σ, hσ, ρ, t, _, ht, rfl⟩ := hs
  calc
    ((∑ j, t j).map (fun a => a.1 + 1)).sum =
        ∑ j, ((t j).map (fun a => a.1 + 1)).sum :=
      map_sum (Multiset.sumAddMonoidHom.comp
        (Multiset.mapAddMonoidHom (fun a : (Σ k : ℕ,
          Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) =>
          a.1 + 1))) t Finset.univ
    _ = ∑ j, (σ j).rank := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Multiset.map_map, Function.comp_def,
        Correspondence.supercuspidalSupportDatum_rank] using (ht j).sum_rank
    _ = D.rank := by
      rw [rank, ← hσ, Multiset.map_map]
      rfl

end IsobaricData

end Langlands.Automorphic
