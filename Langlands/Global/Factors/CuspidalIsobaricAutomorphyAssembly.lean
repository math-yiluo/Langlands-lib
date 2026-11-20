import Langlands.Global.Factors.IsobaricArchimedeanQuotients

/-!
# Assembly from prescribed local constituent embeddings

An embedding of each chosen finite constituent and of each chosen
archimedean quotient into one automorphic subquotient gives the isobaric-sum
predicate. At an archimedean place the map from the ordered standard module
is the quotient projection followed by the prescribed embedding.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix.Norms.Operator

universe u uQ

namespace Langlands.Automorphic.IrreducibleOperatorSubquotient

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Archimedean Langlands.Global
open Langlands.Global.CompletionPadic (padicField)
open Langlands.Correspondence (AutomorphicObject)
open Langlands.Global.CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open Langlands.LocalFactor.Archimedean (RealBlock ComplexCharacterData realRank)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance finiteMatrixTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- The given finite constituents and irreducible quotients of the ordered
archimedean standard modules embed into one automorphic subquotient. -/
def HasIsobaricConstituentEmbeddings (Q : IrreducibleOperatorSubquotient F r)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat) : Prop :=
  (∀ v : FinitePlace F,
    ∃ B : (A v).obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
      Function.Injective B.toLinearMap) ∧
  (∀ v : RP, ∃ (ds : Fin k → List RealBlock) (es : List RealBlock),
    (∀ i, (T i).realization.HasRealPlaceParameter v (ds i)) ∧
    es.Perm (List.ofFn ds).flatten ∧ realRank es = r + 1 ∧ IsRealLanglandsOrdered es ∧
    ∃ (R : Submodule ℂ (realStandardKFinite (r + 1) es))
      (hR : IsGKSubmodule (realStandardRep (r + 1) es) (realStandardLie (r + 1) es) R),
      IsIrreducibleGKModule ((realStandardRep (r + 1) es).quotient R hR.1)
        (RealLeviDuality.quotLie (realStandardLie (r + 1) es) R hR.2) ∧
      ∃ B : (realStandardKFinite (r + 1) es ⧸ R) →ₗ[ℂ] Q.Space,
        Function.Injective B ∧
        B ∈ gkHoms ((realStandardRep (r + 1) es).quotient R hR.1)
          (RealLeviDuality.quotLie (realStandardLie (r + 1) es) R hR.2)
          (Q.subquotient.realPlaceCompactRepresentation v) (Q.subquotient.realPlaceLieAction v)) ∧
  ∀ v : CP, ∃ (ds : Fin k → List ComplexCharacterData) (es : List ComplexCharacterData),
    (∀ i, (T i).realization.HasComplexPlaceParameter v (ds i)) ∧
    es.Perm (List.ofFn ds).flatten ∧ es.length = r + 1 ∧ IsComplexLanglandsOrdered es ∧
    ∃ (R : Submodule ℂ (complexStandardKFinite (r + 1) es))
      (hR : IsGKSubmodule (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es) R),
      IsIrreducibleGKModule ((complexStandardRep (r + 1) es).quotient R hR.1)
        (RealLeviDuality.quotLie (complexStandardLie (r + 1) es) R hR.2) ∧
      ∃ B : (complexStandardKFinite (r + 1) es ⧸ R) →ₗ[ℂ] Q.Space,
        Function.Injective B ∧
        B ∈ gkHoms ((complexStandardRep (r + 1) es).quotient R hR.1)
          (RealLeviDuality.quotLie (complexStandardLie (r + 1) es) R hR.2)
          (Q.subquotient.complexPlaceCompactRepresentation v)
          (Q.subquotient.complexPlaceLieAction v)

private theorem embedding_ne_zero {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V]
    {B : V →ₗ[ℂ] W} (hB : Function.Injective B) : B ≠ 0 := by
  intro hB0
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hB (by simp [hB0]))

/-- Extract the three clauses of the published isobaric-sum predicate from
the embeddings of the chosen constituents. -/
theorem isCuspidalIsobaricSum_of_constituentEmbeddings
    {Q : IrreducibleOperatorSubquotient F r}
    {T : ∀ i, CuspidalOperatorRealization F (m i)}
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    {A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat}
    (hA : ∀ v, (padicField v).canonicalTopologicalData.IsIsobaricSum.{u, u}
      (fun i => (((P i).localComponent v).padicObject (h i v).1 (h i v).2).obj) (A v).obj)
    (hEmb : Q.HasIsobaricConstituentEmbeddings T A) :
    Q.IsCuspidalIsobaricSum T P h := by
  obtain ⟨hfinite, hreal, hcomplex⟩ := hEmb
  refine ⟨fun v => ⟨A v, hA v, hfinite v⟩, ?_, ?_⟩
  · intro v
    obtain ⟨ds, es, hds, hperm, hn, ho, R, hR, hJ, B, hBi, hB⟩ := hreal v
    have := hJ.1
    have ho' := LocalFactor.Archimedean.isRealLanglandsOrdered_iff.mpr ho
    exact ⟨ds, hds, es, hperm,
      OperatorSubquotient.hasRealPlaceLanglandsQuotient_of_quotient hn ho' hJ
        R.mkQ_surjective (quotientProjection_mem_gkHoms hR) (embedding_ne_zero hBi) hB⟩
  · intro v
    obtain ⟨ds, es, hds, hperm, hn, ho, R, hR, hJ, B, hBi, hB⟩ := hcomplex v
    have := hJ.1
    exact ⟨ds, hds, es, hperm,
      OperatorSubquotient.hasComplexPlaceLanglandsQuotient_of_quotient hn ho hJ
        R.mkQ_surjective (quotientProjection_mem_gkHoms hR) (embedding_ne_zero hBi) hB⟩

end Langlands.Automorphic.IrreducibleOperatorSubquotient
