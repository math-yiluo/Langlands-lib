import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.LocalComponentFinitePlace
import Langlands.Global.Factors.CuspidalInducingDataRigidityStatement
import Langlands.Global.Factors.CuspidalSupportStatement
import Langlands.Representation.Unramified.PrincipalSeries

/-!
# Cuspidal support uniqueness from inducing-data rigidity

The embeddings supplied by the finite constituent predicate identify the two
local subquotients. Jacquet–Shalika rigidity then matches the cuspidal data.
-/

noncomputable section

set_option autoImplicit false

universe u uQ uV uW

namespace Langlands.Global

open Automorphic
open CompactSplitting
open CompletionPadic (padicField)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)

attribute [local instance] Automorphic.localComponentRationalGroup
  Automorphic.localComponentContinuousGroup Automorphic.localComponentSmoothGroup
  Automorphic.localComponentFormGroup Automorphic.localComponentStableGroup
  Automorphic.localComponentRealizationGroup Automorphic.localComponentGeneralLinearTopology

/-- The local restriction of an irreducible operator subquotient has a single
irreducible type whenever two irreducible representations embed into it. -/
private theorem nonempty_equiv_of_localEmbeddings
    {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (Q : OperatorSubquotient F n) (hQ : Q.IsIrreducible) (v : FinitePlace F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (FiniteLocalGL F n v) V)
    (τ : Representation ℂ (FiniteLocalGL F n v) W)
    (hρ : ρ.IsIrreducible) (hτ : τ.IsIrreducible)
    (f : ρ.IntertwiningMap (Q.localRepresentation v)) (hf : Function.Injective f.toLinearMap)
    (g : τ.IntertwiningMap (Q.localRepresentation v)) (hg : Function.Injective g.toLinearMap) :
    Nonempty (ρ.Equiv τ) := by
  have : ρ.IsIrreducible := hρ
  have : τ.IsIrreducible := hτ
  let σ := Q.localRepresentation v
  let I := isotypicPart ρ σ
  have hlocal (d : FiniteLocalGL F n v) (x : Q.Space) (hx : x ∈ I) : σ d x ∈ I :=
    apply_mem_isotypicPart ρ σ d hx
  have hcentralizer (c : Module.End ℂ Q.Space) (hc : c ∈ Q.localCentralizerOperators v)
      (x : Q.Space) (hx : x ∈ I) : c x ∈ I :=
    intertwiner_mem_isotypicPart ρ
      (JointIsotypic.commutingHom c (Q.commutesWith_localCentralizerOperators v c hc)) hx
  have hI : I ≠ ⊥ := by
    intro hbot
    have : Nontrivial ρ.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (FiniteLocalGL F n v)) ρ.asModule
    obtain ⟨x, hx⟩ := exists_ne (0 : ρ.asModule)
    have hmem : f (ρ.asModuleEquiv x) ∈ I :=
      range_le_isotypicPart ρ σ f ⟨ρ.asModuleEquiv x, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx (ρ.asModuleEquiv.injective (hf (hmem.trans (map_zero _).symm)))
  have htop : isotypicPart ρ σ = ⊤ :=
    (Q.isJointlyIrreducible_localCentralizerOperators hQ v I hlocal hcentralizer).resolve_left hI
  have hτ := isotypicPart_comap_of_injective ρ τ σ g hg
  rw [htop, Submodule.comap_top] at hτ
  exact nonempty_equiv_of_isotypicPart_eq_top ρ τ hτ.symm

/-- A reference vector outside the exceptional set gives a spherical local class. -/
private theorem localClass_isSpherical
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} {T : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (h : HasIrreducibleAdmissibleComponents P)
    (v : FinitePlace F) (hv : v ∉ P.tensorExceptional) :
    Correspondence.IsSphericalClass (padicField v) (localClass P h v) := by
  refine (LocalRealization.padicClass_isSpherical_iff (P.localComponent v) (h v).1 (h v).2).mpr ?_
  obtain ⟨f, hf, hfix⟩ :=
    P.presentation.localComponent_exists_integral_fixed P.finiteSlice.nonzero v hv
  exact (Submodule.ne_bot_iff _).mpr ⟨f, fun g => hfix g.1 g.2, hf⟩

/-- The implication from inducing-data rigidity to finite-place cuspidal support uniqueness. -/
def CuspidalSupportUniquenessReductionStatement : Prop :=
  CuspidalInducingDataRigidityStatement.{u, uQ} → CuspidalSupportUniquenessStatement.{u, uQ}

/-- Getz–Hahn Corollary 10.7.3 at the finite places follows from Theorem 10.7.2. -/
theorem cuspidalSupportUniqueness_of_rigidity :
    CuspidalSupportUniquenessReductionStatement.{u, uQ} := by
  classical
  intro hrig F _ _ _ r k k' m m' hm hm' T T' P P' h h' Q hQ hQ'
  obtain ⟨A, S, hAsub, hAfix, hAemb⟩ := hQ
  obtain ⟨A', -, hA'sub, -, hA'emb⟩ := hQ'
  let E := Finset.univ.biUnion (fun i => (P i).tensorExceptional)
  let E' := Finset.univ.biUnion (fun j => (P' j).tensorExceptional)
  refine hrig F r k k' m m' hm hm' T T' P P' h h' (S ∪ (E ∪ E')) fun v hv => ?_
  have hvS : v ∉ S := fun hs => hv (Finset.mem_union_left _ hs)
  have hvE : v ∉ E ∪ E' := fun he => hv (Finset.mem_union_right _ he)
  have hvP (i : Fin k) : v ∉ (P i).tensorExceptional := fun hi =>
    hvE (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩))
  have hvP' (j : Fin k') : v ∉ (P' j).tensorExceptional := fun hj =>
    hvE (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩))
  obtain ⟨f, hf⟩ := hAemb v
  obtain ⟨g, hg⟩ := hA'emb v
  obtain ⟨e⟩ := nonempty_equiv_of_localEmbeddings Q.subquotient Q.irreducible v
    (A' v).obj.representation (A v).obj.representation
    (A' v).property.1 (A v).property.1 g hg f hf
  exact ⟨fun i => localClass_isSpherical (P i) (h i) v (hvP i),
    fun j => localClass_isSpherical (P' j) (h' j) v (hvP' j),
    A v, hAfix v hvS, hAsub v, (Unramified.isSubquotientOf_iff_of_equiv e).mp (hA'sub v)⟩

end Langlands.Global
