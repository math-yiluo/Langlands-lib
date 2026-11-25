import Langlands.Theta.Heisenberg.InducedModel
import Langlands.Representation.Smooth.RenardSigmaCompactSchurProof
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# The Stone–von Neumann theorem over a nonarchimedean local field

Let `F` be a nonarchimedean local field with `2 ≠ 0`, `W` a finite-dimensional vector space over
`F` with its natural topology, `B` a non-degenerate alternating form on `W` and `ψ` a continuous
non-trivial additive character of `F`. Then the Heisenberg group `HeisenbergGroup B` has, up to
isomorphism, exactly one smooth irreducible complex representation with central character `ψ`:

* `exists_isIrreducible_isSmooth`: the induced model of a self-dual datum is one;
* `nonempty_equiv`: any two are isomorphic;
* `equiv_eq_smul`: an isomorphism between two of them is unique up to a scalar.

The Heisenberg group of a finite-dimensional space over a local field is a Hausdorff, locally
compact, totally disconnected and σ-compact topological group (instances below); the last
statement is the Library's Schur lemma for such groups.

Mœglin–Vignéras–Waldspurger, *Correspondances de Howe sur un corps p-adique* (Lecture Notes in
Math. 1291, Springer 1987), chapter 2, I.2, Théorème (Stone, von Neumann), p. 28 (existence I.3,
pp. 28–30; uniqueness I.5, pp. 30–31).
-/

noncomputable section

open Topology

namespace Langlands.HeisenbergGroup

universe u v w w'

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A nonarchimedean local field is σ-compact: its topology is that of a proper normed field. -/
private theorem sigmaCompactSpace_field : SigmaCompactSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F) (Γ₀ := ValuativeRel.ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let N : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField (L := F) (Γ₀ := ValuativeRel.ValueGroupWithZero F)
  have hP : @ProperSpace F N.toPseudoMetricSpace :=
    .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have h := @secondCountable_of_proper F N.toPseudoMetricSpace hP
  have : SecondCountableTopology F := h
  infer_instance

variable {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W]
  [IsModuleTopology F W]

/-- `W` is homeomorphic to `F ^ n` through a basis. -/
private def homeomorphPi (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (W : Type v) [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W] :
    W ≃ₜ (Fin (Module.finrank F W) → F) :=
  haveI := IsModuleTopology.isTopologicalAddGroup F W
  { toEquiv := (Module.finBasis F W).equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (Module.finBasis F W).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Module.finBasis F W).equivFun.symm.toLinearMap }

variable [Invertible (2 : F)] {B : LinearMap.BilinForm F W}

/-- The Heisenberg group over a local field is Hausdorff. -/
instance : T2Space (HeisenbergGroup B) :=
  have : T2Space W := (homeomorphPi F W).symm.t2Space
  homeomorphProd.symm.t2Space

/-- The Heisenberg group over a local field is locally compact. -/
instance : LocallyCompactSpace (HeisenbergGroup B) :=
  have : LocallyCompactSpace W := (homeomorphPi F W).isClosedEmbedding.locallyCompactSpace
  homeomorphProd.isClosedEmbedding.locallyCompactSpace

/-- The Heisenberg group over a local field is totally disconnected. -/
instance : TotallyDisconnectedSpace (HeisenbergGroup B) :=
  have : TotallyDisconnectedSpace W := (homeomorphPi F W).symm.totallyDisconnectedSpace
  homeomorphProd.symm.totallyDisconnectedSpace

/-- The Heisenberg group over a local field is σ-compact. -/
instance : SigmaCompactSpace (HeisenbergGroup B) :=
  have := sigmaCompactSpace_field (F := F)
  have : SigmaCompactSpace W := (homeomorphPi F W).isClosedEmbedding.sigmaCompactSpace
  homeomorphProd.isClosedEmbedding.sigmaCompactSpace

variable {ψ : AddChar F ℂ}

/-- **Stone–von Neumann, existence.** The Heisenberg group of a non-degenerate alternating form
has a smooth irreducible representation with central character `ψ` (the induced model of a
self-dual subgroup). -/
theorem exists_isIrreducible_isSmooth (hB : B.IsAlt) (hn : B.Nondegenerate) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) :
    ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module ℂ S)
      (ρ : Representation ℂ (HeisenbergGroup B) S),
      IsSmooth ρ ∧ ρ.IsIrreducible ∧ HasCentralCharacter ρ ψ := by
  obtain ⟨D⟩ := nonempty_selfDualDatum hB hn hψ hψ1
  exact ⟨_, _, _, (inducedModel D).toRepresentation, isSmooth_inducedModel hB D hψ,
    isIrreducible_inducedModel hB D hψ, hasCentralCharacter_inducedModel D⟩

/-- **Stone–von Neumann, uniqueness.** Two smooth irreducible representations of the Heisenberg
group of a non-degenerate alternating form with the same central character `ψ` are
isomorphic. -/
theorem nonempty_equiv (hB : B.IsAlt) (hn : B.Nondegenerate) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {S : Type w} {S' : Type w'} [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S']
    {ρ : Representation ℂ (HeisenbergGroup B) S} {ρ' : Representation ℂ (HeisenbergGroup B) S'}
    (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible) (hc : HasCentralCharacter ρ ψ)
    (hρ' : IsSmooth ρ') (hi' : ρ'.IsIrreducible) (hc' : HasCentralCharacter ρ' ψ) :
    Nonempty (ρ.Equiv ρ') := by
  obtain ⟨D⟩ := nonempty_selfDualDatum hB hn hψ hψ1
  obtain ⟨e, -, he0, he⟩ := D.exists_eigenvector_mem hB hc hρ ⊤ top_ne_bot
  obtain ⟨e', -, he0', he'⟩ := D.exists_eigenvector_mem hB hc' hρ' ⊤ top_ne_bot
  have hcp : HasCentralCharacter (ρ.prod ρ') ψ := fun t v => Prod.ext (hc t v.1) (hc' t v.2)
  let P := translatesSpan hcp (e, e')
  have heP : (e, e') ∈ P.toSubmodule := mem_translatesSpan hcp (e, e')
  have i3 : P.toRepresentation.IsIrreducible :=
    D.isIrreducible_translatesSpan hB hψ hcp (fun h => he0 (congrArg Prod.fst h))
      (fun a ha => Prod.ext (he a ha) (he' a ha))
  let f : P.toRepresentation.IntertwiningMap ρ :=
    ⟨(LinearMap.fst ℂ S S').comp P.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
  let f' : P.toRepresentation.IntertwiningMap ρ' :=
    ⟨(LinearMap.snd ℂ S S').comp P.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
  have hf := (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right fun h =>
    he0 (congrArg (fun k : P.toRepresentation.IntertwiningMap ρ => k ⟨_, heP⟩) h)
  have hf' := (Representation.IsIrreducible.bijective_or_eq_zero f').resolve_right fun h =>
    he0' (congrArg (fun k : P.toRepresentation.IntertwiningMap ρ' => k ⟨_, heP⟩) h)
  exact ⟨(f.ofBijective hf).symm.trans (f'.ofBijective hf')⟩

/-- An isomorphism from a smooth irreducible representation of the Heisenberg group is unique
up to a scalar (Schur's lemma). -/
theorem equiv_eq_smul {S : Type w} {S' : Type w'} [AddCommGroup S] [Module ℂ S] [AddCommGroup S']
    [Module ℂ S'] {ρ : Representation ℂ (HeisenbergGroup B) S}
    {ρ' : Representation ℂ (HeisenbergGroup B) S'} (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (e e' : ρ.Equiv ρ') : ∃ c : ℂ, ∀ v, e' v = c • e v := by
  obtain ⟨c, hc⟩ := (Renard.Smooth.sigmaCompactSchur.{max u v, w, w} (HeisenbergGroup B) S ρ hρ hi).1
    (e'.trans e.symm).toIntertwiningMap
  refine ⟨c, fun v => ?_⟩
  have h : e.symm (e' v) = c • v := congrArg (fun k : ρ.IntertwiningMap ρ => k v) hc
  calc e' v = e (e.symm (e' v)) := (e.apply_symm_apply _).symm
    _ = e (c • v) := by rw [h]
    _ = c • e v := map_smul e c v

end Langlands.HeisenbergGroup
