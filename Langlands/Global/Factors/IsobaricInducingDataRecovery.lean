import Langlands.Global.Factors.CuspidalInducingDataRigidityStatement
import Langlands.Global.Factors.IsobaricFinitePlaceComparison
import Langlands.Representation.Classification.IsobaricSumSubquotient
import Langlands.Representation.Unramified.SphericalIsobaricSum

/-! # Recovering cuspidal data from common local embeddings -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSubquotientOf sphericalSubgroup)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

private local instance (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

set_option maxHeartbeats 800000 in
/-- Recover the cuspidal classes of two isobaric families from common finite-place
embeddings, using cuspidal inducing-data rigidity and the local spherical occurrence
of an isobaric sum of spherical factors. -/
theorem exists_cuspidalMatching_of_common_finitePlace_embeddings
    (rigidity : CuspidalInducingDataRigidityStatement.{u, uQ})
    {r k k' : ℕ} {m : Fin k → ℕ} {m' : Fin k' → ℕ}
    (hm : ∑ i, (m i + 1) = r + 1) (hm' : ∑ j, (m' j + 1) = r + 1)
    {T : ∀ i, CuspidalOperatorRealization F (m i)}
    {T' : ∀ j, CuspidalOperatorRealization F (m' j)}
    {P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i)}
    {P' : ∀ j, CuspidalSpectralPresentation.{u, uQ} (T' j)}
    {h : ∀ i, HasIrreducibleAdmissibleComponents (P i)}
    {h' : ∀ j, HasIrreducibleAdmissibleComponents (P' j)}
    {Q Q' : IrreducibleOperatorSubquotient F r}
    (hQ : Q.IsCuspidalIsobaricSum T P h) (hQ' : Q'.IsCuspidalIsobaricSum T' P' h')
    (S : Finset (FinitePlace F))
    (common : ∀ v ∉ S, ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
      (∃ f : A.obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective f.toLinearMap) ∧
      ∃ f' : A.obj.representation.IntertwiningMap (Q'.subquotient.localRepresentation v),
        Function.Injective f'.toLinearMap) :
    ∃ e : Fin k ≃ Fin k', ∀ i, (⟨m i, (T i).isoClass⟩ : PositiveRankCuspidalClass F) =
      ⟨m' (e i), (T' (e i)).isoClass⟩ := by
  classical
  let U := S ∪ (Finset.univ.biUnion fun i => (P i).exceptional) ∪
    (Finset.univ.biUnion fun j => (P' j).exceptional)
  apply rigidity F r k k' m m' hm hm' T T' P P' h h' U
  intro v hv
  have hvS : v ∉ S := fun hvS => hv (Finset.mem_union_left _ (Finset.mem_union_left _ hvS))
  have hi (i : Fin k) : v ∉ (P i).exceptional := fun hmem =>
    hv (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)))
  have hj (j : Fin k') : v ∉ (P' j).exceptional := fun hmem =>
    hv (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hmem⟩))
  let B := fun i => ((P i).localComponent v).padicObject (h i v).1 (h i v).2
  let B' := fun j => ((P' j).localComponent v).padicObject (h' j v).1 (h' j v).2
  have hB (i : Fin k) :
      fixedVectors (B i).obj.representation (sphericalSubgroup (padicField v) (m i)) ≠ ⊥ :=
    ((P i).hasSpectrum v (hi i)).1
  have hB' (j : Fin k') :
      fixedVectors (B' j).obj.representation (sphericalSubgroup (padicField v) (m' j)) ≠ ⊥ :=
    ((P' j).hasSpectrum v (hj j)).1
  obtain ⟨C, ⟨g, hg⟩, ⟨g', hg'⟩⟩ := common v hvS
  obtain ⟨A, hA, f, hf⟩ := hQ.1 v
  obtain ⟨A', hA', f', hf'⟩ := hQ'.1 v
  obtain ⟨e⟩ := Q.subquotient.nonempty_local_equiv_of_injective v A.obj.representation
    Q.irreducible C.obj.representation A.property.1 C.property.1 f hf g hg
  obtain ⟨e'⟩ := Q'.subquotient.nonempty_local_equiv_of_injective v C.obj.representation
    Q'.irreducible A'.obj.representation C.property.1 A'.property.1 g' hg' f' hf'
  have hAsph := Unramified.isSpherical_of_isIsobaricSum (padicField v) hm (σ := B) (A := A)
    hA hB
  have hAocc : IsSubquotientOf ((padicField v).canonicalNormalizedProductInduced
      ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ (fun i => (B i).obj.representation))
      A.obj.representation :=
    PadicField.TopologicalData.IsIsobaricSum.isSubquotient_normalizedProduct
      (padicField v).canonicalTopologicalData (Nat.succ_pos _)
      ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ hA
  have hA'occ : IsSubquotientOf ((padicField v).canonicalNormalizedProductInduced
      ⟨k', fun j => m' j + 1, fun _ => Nat.succ_pos _, hm'⟩ (fun j => (B' j).obj.representation))
      A'.obj.representation :=
    PadicField.TopologicalData.IsIsobaricSum.isSubquotient_normalizedProduct
      (padicField v).canonicalTopologicalData (Nat.succ_pos _)
      ⟨k', fun j => m' j + 1, fun _ => Nat.succ_pos _, hm'⟩ hA'
  obtain ⟨W, w, hw⟩ := hA'occ
  let toA := (e.trans e').symm
  exact ⟨fun i => ⟨B i, rfl, hB i⟩, fun j => ⟨B' j, rfl, hB' j⟩, A, hAsph, hAocc,
    W, toA.toIntertwiningMap.comp w, toA.surjective.comp hw⟩

end Langlands.Global
