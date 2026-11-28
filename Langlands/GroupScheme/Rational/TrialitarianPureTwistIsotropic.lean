import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Reductive.InnerFormStarForward
import Langlands.GroupScheme.Rational.SimplyConnectedQuasiSplitPureTwist
import Langlands.GroupScheme.Rational.TitsIndexQuasiSplitMarking
import Langlands.GroupScheme.Rational.TrialitarianCentrallyMarkedCohomology
import Langlands.GroupScheme.SimplyConnected.TypeD4CentralMarking

/-! # Cohomology of an isotropic pure inner twist in trialitarian type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.CentralSimple

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1350000

section InnerIndex

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [Algebra.IsSeparable F L]
  {G H A : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {e : LocalGroupIso G H (GaloisCocycle.cover F L)}

/-- An inner discrepancy preserves the Cartan pairing and all star permutations
on the actual simple vertices. -/
theorem LocalGroupIso.HasInnerDiscrepancy.exists_cartan_starEquiv
    {q : G ⟶ A} (hq : IsAdjointQuotient q) (he : e.HasInnerDiscrepancy hq.innerAction)
    (d : TitsIndexData G) (d' : TitsIndexData H) :
    ∃ v : d.Vertex ≃ d'.Vertex, (∀ a b, d'.cartan (v a) (v b) = d.cartan a b) ∧
      ∀ σ a, v (d.star σ a) = d'.star σ (v a) := by
  obtain ⟨f, hb, hs⟩ := InnerFormStarForward.of_localIso hq d.pinning d'.pinning e he
  refine ⟨f.indexEquiv.subtypeEquiv hb, (fun _ _ => f.toHom.pairing), ?_⟩
  intro σ a
  apply Subtype.ext
  exact congrArg (fun z : RootPairing.Equiv d.pinning.rootDatum d'.pinning.rootDatum =>
    z.indexEquiv a.val) (hs σ)

/-- Conjugation by a pure cocycle acts trivially on the based diagram even
when the original and twisted groups have different distinguished sets. -/
theorem LocalGroupIso.HasDiscrepancy.exists_cartan_starEquiv
    {ξ : Cocycle G (GaloisCocycle.cover F L)}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (d : TitsIndexData G) (d' : TitsIndexData H) :
    ∃ v : d.Vertex ≃ d'.Vertex, (∀ a b, d'.cartan (v a) (v b) = d.cartan a b) ∧
      ∀ σ a, v (d.star σ a) = d'.star σ (v a) := by
  obtain ⟨A, q, hq⟩ := adjointQuotientExistence F G d.isSemisimple.isConnectedReductive
  have hinner : e.HasInnerDiscrepancy hq.innerAction := by
    intro T a b
    refine ⟨ξ.toFun a b ≫ q.hom.hom, ?_⟩
    intro W r g
    rw [← Category.assoc, hq.innerAction_act_lift, ← ξ.naturality]
    simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id] using
      hξ (r ≫ a) (r ≫ b) g
  exact LocalGroupIso.HasInnerDiscrepancy.exists_cartan_starEquiv hq hinner d d'

/-- A pure inner twist retains the numbering and moving leaves of a trialitarian diagram. -/
theorem LocalGroupIso.HasDiscrepancy.exists_trialitarian_numbering
    {ξ : Cocycle G (GaloisCocycle.cover F L)}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (d : TitsIndexData G) (d' : TitsIndexData H) (q : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b))
    (hno : ∀ a : d.Vertex, q a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) :
    ∃ q' : d'.Vertex ≃ Fin 4,
      (∀ a b, d'.cartan a b = CartanMatrix.D 4 (q' a) (q' b)) ∧
      ∀ a : d'.Vertex, q' a ≠ 1 →
        ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d'.star σ a ≠ a := by
  obtain ⟨v, hv, hs⟩ := hξ.exists_cartan_starEquiv d d'
  let q' := v.symm.trans q
  refine ⟨q', ?_, ?_⟩
  · intro a b
    simpa only [q', Equiv.trans_apply, Equiv.apply_symm_apply] using
      (hv (v.symm a) (v.symm b)).trans (hD (v.symm a) (v.symm b))
  · intro a ha
    obtain ⟨σ, hmove⟩ := hno (v.symm a) ha
    refine ⟨σ, fun h => hmove (v.injective ?_)⟩
    rw [hs, v.apply_symm_apply, h]

end InnerIndex

namespace TitsIndexData

variable {F : Type u} [Field F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] (d : TitsIndexData H)

/-- A trialitarian index that is isotropic and has an unmarked vertex has
exactly one distinguished orbit, so its split rank is one. -/
theorem splitRank_eq_one_of_trialitarian_unmarked (q : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b))
    (hno : ¬ ∃ a : d.Vertex, q a ≠ 1 ∧
      ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a = a)
    (hiso : ¬ IsAnisotropic H) (a : d.Vertex) (ha : a ∉ d.distinguishedVertices) :
    splitRank H = 1 := by
  classical
  have hs : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) x,
      d.star σ x ∈ d.distinguishedVertices ↔ x ∈ d.distinguishedVertices :=
    fun σ x => not_congr (titsIndexStarInvariant F H d σ x)
  let hleaf := d.star_transitive_on_D4_leaves_of_no_fixed_leaf q hD hno
  have hsub : Subsingleton d.DistinguishedOrbit := by
    constructor
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro x y
    apply Quotient.sound
    change ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ x.val = y.val
    by_cases hac : q a = 1
    · have hx : q x.val ≠ 1 := fun h => ha (q.injective (hac.trans h.symm) ▸ x.property)
      have hy : q y.val ≠ 1 := fun h => ha (q.injective (hac.trans h.symm) ▸ y.property)
      exact hleaf x.val y.val hx hy
    · have hc (z : d.distinguishedVertices) : q z.val = 1 := by
        by_contra h
        obtain ⟨σ, hσ⟩ := hleaf z.val a h hac
        exact ha (hσ ▸ (hs σ z.val).mpr z.property)
      exact ⟨1, (d.star_one x.val).trans (q.injective ((hc x).trans (hc y).symm))⟩
  have hle : Nat.card d.DistinguishedOrbit ≤ 1 := by
    simpa using Nat.card_le_card_of_injective
      (fun _ : d.DistinguishedOrbit => (PUnit.unit : PUnit.{1}))
      (fun x y _ => hsub.elim x y)
  have hr := (titsIndexSplitRank F H d).1
  have hne : Nat.card d.DistinguishedOrbit ≠ 0 := by
    intro h
    apply hiso
    change splitRank H = 0
    simpa only [h, Nat.cast_zero] using hr.symm
  have hone : Nat.card d.DistinguishedOrbit = 1 := by omega
  simpa only [hone, Nat.cast_one] using hr.symm

end TitsIndexData

/-- An isotropic pure inner twist of a quasi-split simply connected
trialitarian group over a totally imaginary number field trivializes the cocycle. -/
theorem LocalGroupIso.HasDiscrepancy.isTrivial_of_trialitarian_isotropic
    {F L : Type u} [Field F] [NumberField F] [IsTotallyComplex F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    {ξ : Cocycle G (GaloisCocycle.cover F L)} {e : LocalGroupIso G H (GaloisCocycle.cover F L)}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    (hsc : IsSimplyConnected G) (hG : IsQuasiSplit G) (hH : IsSimplyConnected H)
    (d : TitsIndexData G) (q : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b))
    (hno : ∀ a : d.Vertex, q a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a)
    (hiso : ¬ IsAnisotropic H) : ξ.IsTrivial := by
  classical
  obtain ⟨d'⟩ := titsIndexExistence F H hH.isSemisimple
  obtain ⟨q', hD', hmove⟩ := hξ.exists_trialitarian_numbering d d' q hD hno
  have hno' : ¬ ∃ a : d'.Vertex, q' a ≠ 1 ∧
      ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d'.star σ a = a := by
    rintro ⟨a, ha, hf⟩
    obtain ⟨σ, hσ⟩ := hmove a ha
    exact hσ (hf σ)
  by_cases hmark : ∀ a : d'.Vertex, a ∈ d'.distinguishedVertices
  · exact hξ.isTrivial_of_quasiSplit hsc hG (d'.isQuasiSplit_of_all_vertices_distinguished hmark)
  · obtain ⟨a, ha⟩ := not_forall.mp hmark
    have hrank := d'.splitRank_eq_one_of_trialitarian_unmarked q' hD' hno' hiso a ha
    have hnum := d'.D4_central_marking_of_no_fixed_leaf q' hD' hrank hno'
    exact hξ.isTrivial_of_D4_centralMarking hn hsc hG hH d' q' hnum hno'

end Langlands.GroupScheme
