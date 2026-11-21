import Langlands.Global.Factors.ComplexIsobaricPlaceQuotient
import Langlands.Global.Factors.CuspidalInducedTensorDescent
import Langlands.Global.Factors.CuspidalIsobaricAutomorphyAssembly
import Langlands.Global.Factors.CuspidalIsobaricAutomorphyStatement
import Langlands.Global.Factors.CuspidalIsobaricFiniteFamilyStatement
import Langlands.Global.Factors.RealIsobaricQuotientReordering

/-! # Prescribed tensor realization for the isobaric automorphy proof -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Matrix.Norms.Operator

universe u uQ

namespace Langlands.Global

open NumberField Langlands.Archimedean Langlands.Automorphic
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSubquotientOf sphericalSubgroup)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean (RealBlock ComplexCharacterData realRank)

attribute [local instance 100] LieRing.ofAssociativeRing

section PlaceData

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RealStandard(" ds ")" => realStandardKFinite (r + 1) ds
local notation "ComplexStandard(" ds ")" => complexStandardKFinite (r + 1) ds

/-- Data specifying the real quotient to be realized, with its subquotient map
in the original cuspidal block order. -/
structure RealIsobaricPlaceData (T : ∀ i, CuspidalOperatorRealization F (m i)) (v : RP) where
  blocks : Fin k → List RealBlock
  parameters : ∀ i, (T i).realization.HasRealPlaceParameter v (blocks i) ∧
    IsIrreducibleGKModule (realStandardRep (m i + 1) (blocks i))
      (realStandardLie (m i + 1) (blocks i))
  orderedBlocks : List RealBlock
  perm : orderedBlocks.Perm (List.ofFn blocks).flatten
  rank : realRank orderedBlocks = r + 1
  ordered : IsRealLanglandsOrdered orderedBlocks
  kernel : Submodule ℂ RealStandard(orderedBlocks)
  stable : IsGKSubmodule (realStandardRep (r + 1) orderedBlocks)
    (realStandardLie (r + 1) orderedBlocks) kernel
  irreducible : IsIrreducibleGKModule ((realStandardRep (r + 1) orderedBlocks).quotient kernel stable.1)
    (RealLeviDuality.quotLie (realStandardLie (r + 1) orderedBlocks) kernel stable.2)
  isSubquotient :
    let xs := (List.ofFn blocks).flatten
    ∃ (W : Submodule ℂ RealStandard(xs))
      (hW : IsGKSubmodule (realStandardRep (r + 1) xs) (realStandardLie (r + 1) xs) W)
      (q : W →ₗ[ℂ] (RealStandard(orderedBlocks) ⧸ kernel)),
      IsGKSubquotientMap ((realStandardRep (r + 1) orderedBlocks).quotient kernel stable.1)
        (RealLeviDuality.quotLie (realStandardLie (r + 1) orderedBlocks) kernel stable.2) hW q

/-- Data specifying the complex quotient to be realized, with its subquotient
map in the original cuspidal block order. -/
structure ComplexIsobaricPlaceData (T : ∀ i, CuspidalOperatorRealization F (m i)) (v : CP) where
  blocks : Fin k → List ComplexCharacterData
  parameters : ∀ i, (T i).realization.HasComplexPlaceParameter v (blocks i) ∧
    IsIrreducibleGKModule (complexStandardRep (m i + 1) (blocks i))
      (complexStandardLie (m i + 1) (blocks i))
  orderedBlocks : List ComplexCharacterData
  perm : orderedBlocks.Perm (List.ofFn blocks).flatten
  rank : orderedBlocks.length = r + 1
  ordered : IsComplexLanglandsOrdered orderedBlocks
  kernel : Submodule ℂ ComplexStandard(orderedBlocks)
  stable : IsGKSubmodule (complexStandardRep (r + 1) orderedBlocks)
    (complexStandardLie (r + 1) orderedBlocks) kernel
  irreducible : IsIrreducibleGKModule ((complexStandardRep (r + 1) orderedBlocks).quotient kernel stable.1)
    (RealLeviDuality.quotLie (complexStandardLie (r + 1) orderedBlocks) kernel stable.2)
  isSubquotient :
    let xs := (List.ofFn blocks).flatten
    ∃ (W : Submodule ℂ ComplexStandard(xs))
      (hW : IsGKSubmodule (complexStandardRep (r + 1) xs) (complexStandardLie (r + 1) xs) W)
      (q : W →ₗ[ℂ] (ComplexStandard(orderedBlocks) ⧸ kernel)),
      IsGKSubquotientMap ((complexStandardRep (r + 1) orderedBlocks).quotient kernel stable.1)
        (RealLeviDuality.quotLie (complexStandardLie (r + 1) orderedBlocks) kernel stable.2) hW q

private theorem nonempty_realIsobaricPlaceData {T : ∀ i, CuspidalOperatorRealization F (m i)}
    {v : RP} (h : HasRealIsobaricPlaceQuotient (r := r) T v) :
    Nonempty (RealIsobaricPlaceData (r := r) T v) := by
  obtain ⟨ds, es, hds, hperm, hn, ho, R, hR, hJ, hsub⟩ := h
  exact ⟨⟨ds, hds, es, hperm, hn, ho, R, hR, hJ, hsub⟩⟩

private theorem nonempty_complexIsobaricPlaceData {T : ∀ i, CuspidalOperatorRealization F (m i)}
    {v : CP} (h : HasComplexIsobaricPlaceQuotient (r := r) T v) :
    Nonempty (ComplexIsobaricPlaceData (r := r) T v) := by
  obtain ⟨ds, es, hds, hperm, hn, ho, R, hR, hJ, hsub⟩ := h
  exact ⟨⟨ds, hds, es, hperm, hn, ho, R, hR, hJ, hsub⟩⟩

end PlaceData

local instance isobaricTensorMatrixTopology {K : Type u} [Field K] [NumberField K]
    (v : FinitePlace K) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- The all-places realization input for Getz–Hahn Theorem 10.7.5.
For every choice of the local induced constituents of the specified cuspidal
family, realize their exact adelic tensor as a quotient of an invariant space
of genuine automorphic forms. -/
def CuspidalIsobaricTensorRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (E : Finset (FinitePlace F))
    (hsub : ∀ v, IsSubquotientOf (CuspidalInducedFiniteTensor.source hm P h v) (A v).obj.representation)
    (hfixed : ∀ v ∉ E, fixedVectors (A v).obj.representation (sphericalSubgroup (padicField v) r) ≠ ⊥)
    (real : ∀ v : {v : InfinitePlace F // InfinitePlace.IsReal v}, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : {v : InfinitePlace F // InfinitePlace.IsComplex v}, ComplexIsobaricPlaceData (r := r) T v),
    CuspidalInducedFiniteTensor.HasTensorRealization A
      (CuspidalInducedFiniteTensor.assemble hm P h A E hsub hfixed)
      (fun v => (real v).orderedBlocks) (fun v => (complex v).orderedBlocks)
      (fun v => (real v).kernel) (fun v => (complex v).kernel)
      (fun v => (real v).stable) (fun v => (complex v).stable)

set_option maxHeartbeats 3500000 in
/-- Assemble the original all-places target from the local constructions and
realization of their prescribed tensor. -/
theorem cuspidalIsobaricAutomorphy_of_tensorRealization
    (hparam : RealGenericStandardParameterStatement.{u}) (htied : RealTemperedStandardIrreducibleStatement)
    (hfinite : CuspidalIsobaricFiniteFamilyStatement.{u, uQ})
    (hglobal : CuspidalIsobaricTensorRealizationStatement.{u, uQ}) :
    CuspidalIsobaricAutomorphyStatement.{u, uQ} := by
  intro F _ _ _ r k m hm T P h
  obtain ⟨A, E, hIso, hSub, hSph⟩ := hfinite F r k m hm T P h
  let real (v : {v : InfinitePlace F // InfinitePlace.IsReal v}) :=
    Classical.choice (nonempty_realIsobaricPlaceData (realIsobaricPlaceQuotientReduction hparam htied F r k m hm T v))
  let complex (v : {v : InfinitePlace F // InfinitePlace.IsComplex v}) :=
    Classical.choice (nonempty_complexIsobaricPlaceData (hasComplexIsobaricPlaceQuotient hm T v))
  let D := CuspidalInducedFiniteTensor.assemble hm P h A E hSub hSph
  have hrealization := hglobal F r k m hm T P h A E hSub hSph real complex
  obtain ⟨Q, ⟨j, hj⟩, hr, hc⟩ :=
    CuspidalInducedFiniteTensor.exists_placeEmbeddings_of_tensorRealization A D
      (fun v => (real v).orderedBlocks) (fun v => (complex v).orderedBlocks)
      (fun v => (real v).kernel) (fun v => (complex v).kernel)
      (fun v => (real v).stable) (fun v => (complex v).stable)
      (fun v => (real v).irreducible) (fun v => (complex v).irreducible) hrealization
  refine ⟨Q, Q.isCuspidalIsobaricSum_of_constituentEmbeddings P h hIso
    ⟨CuspidalInducedFiniteTensor.localEmbeddings A D j hj, ?_, ?_⟩⟩
  · intro v
    exact ⟨(real v).blocks, (real v).orderedBlocks, fun i => ((real v).parameters i).1,
      (real v).perm, (real v).rank, (real v).ordered, (real v).kernel, (real v).stable,
      (real v).irreducible, hr v⟩
  · intro v
    exact ⟨(complex v).blocks, (complex v).orderedBlocks, fun i => ((complex v).parameters i).1,
      (complex v).perm, (complex v).rank, (complex v).ordered, (complex v).kernel, (complex v).stable,
      (complex v).irreducible, hc v⟩

end Langlands.Global
