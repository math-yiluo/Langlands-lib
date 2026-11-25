import Langlands.ClassFieldTheory.Global.FundamentalClassProof
import Langlands.ClassFieldTheory.Global.LocalRelativeWeilMapExistenceProof
import Langlands.ClassFieldTheory.Global.LocalRelativeWeilTransferProof
import Langlands.ClassFieldTheory.Global.RelativeWeilCharacterFactorization
import Langlands.ClassFieldTheory.Global.RelativeWeilUnramifiedTransfer
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof
import Langlands.Correspondence.AssemblyLTwistedSupercuspidal
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters

/-! # Global norm reciprocity and its finite components -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.BaseChange

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ClassFieldTheory.Global ClassFieldTheory.Global.FundamentalClass ClassFieldTheory.Local
open Global Global.AdelicFunctoriality Global.CompletionPadic LocalClassField
open scoped NumberField FiniteExtension

attribute [local instance] relativeGaloisTopology

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

namespace GlobalNormReciprocity

open RelativeWeilGroup

private theorem exists_compatible_classFamily :
    ∃ (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p),
      (∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) ∧
      ∃ c : ClassFamily.{u}, Generates c ∧ Restriction c ∧ Inflation c ∧ LocalCompatibility I c := by
  let I (p : ℕ) [Fact p.Prime] := Classical.choose (localRelativeClassFormation.{u} p)
  have hI (p : ℕ) [Fact p.Prime] :
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization := by
    have h := Classical.choose_spec (localRelativeClassFormation.{u} p)
    exact ⟨h.2.1, h.1⟩
  exact ⟨I, hI, fundamentalClass_exists I hI⟩

/-- The finite component obtained by including one completion's units into the idele classes. -/
def finiteComponent (rec : IdeleClassGroup (𝓞 F) F →ₜ* (E ≃ₐ[F] E))
    (v : Global.FinitePlace F) : (v.adicCompletion F)ˣ →* (E ≃ₐ[F] E) :=
  rec.toMonoidHom.comp (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v)

private theorem exists_quotient_of_transfer [IsCyclic (E ≃ₐ[F] E)] (c : ClassFamily.{u})
    (hτ : Function.Surjective (transfer c F E))
    (hτker : (transfer c F E).ker = commutator (RelativeWeilGroup c F E)) :
    ∃ rec : IdeleClassGroup (𝓞 F) F →ₜ* (E ≃ₐ[F] E),
      ∀ g, rec (transfer c F E g) = projection c F E g := by
  let : CommGroup (E ≃ₐ[F] E) := IsCyclic.commGroup
  have hle : (transfer c F E).ker ≤ (projection c F E).ker := by
    rw [hτker]
    exact Abelianization.commutator_subset_ker _
  let f := (transfer c F E).liftOfSurjective hτ ⟨projection c F E, hle⟩
  have hf (g : RelativeWeilGroup c F E) : f (transfer c F E g) = projection c F E g :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  refine ⟨⟨f, ?_⟩, hf⟩
  rw [(isQuotientMap_transfer c F E hτ).continuous_iff]
  have hcomp : (f : IdeleClassGroup (𝓞 F) F → E ≃ₐ[F] E) ∘ (transfer c F E) =
      continuousProjection c F E := funext hf
  change Continuous ((f : IdeleClassGroup (𝓞 F) F → E ≃ₐ[F] E) ∘ transfer c F E)
  rw [hcomp]
  exact (continuousProjection c F E).continuous

private theorem quotient_surjective_and_ker (c : ClassFamily.{u})
    (hτ : Function.Surjective (transfer c F E))
    (rec : IdeleClassGroup (𝓞 F) F →ₜ* (E ≃ₐ[F] E))
    (hrec : ∀ g, rec (transfer c F E g) = projection c F E g) :
    Function.Surjective rec ∧ rec.toMonoidHom.ker =
      (ideleClassNorm (K := F) (L := E)).toMonoidHom.range := by
  refine ⟨fun σ => ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := projection_surjective c F E σ
    exact ⟨_, hrec g⟩
  ext a
  obtain ⟨g, rfl⟩ := hτ a
  change rec (transfer c F E g) = 1 ↔ ∃ b, ideleClassNorm b = transfer c F E g
  rw [hrec g]
  constructor
  · intro hg
    obtain ⟨b, rfl⟩ : g ∈ (inclusion c F E).range :=
      (RelativeWeilGroup.exact c F E).symm ▸ hg
    exact ⟨b, (transfer_inclusion c F E b).symm⟩
  · rintro ⟨b, hb⟩
    rw [← transfer_inclusion c F E b] at hb
    rw [← hrec g, ← hb, hrec]
    change inclusion c F E b ∈ (projection c F E).ker
    rw [← RelativeWeilGroup.exact c F E]
    exact ⟨b, rfl⟩

private theorem finiteComponent_ker_and_range (c : ClassFamily.{u})
    (rec : IdeleClassGroup (𝓞 F) F →ₜ* (E ≃ₐ[F] E))
    (hrec : ∀ g, rec (transfer c F E g) = projection c F E g)
    (hker : rec.toMonoidHom.ker = (ideleClassNorm (K := F) (L := E)).toMonoidHom.range)
    (v : Global.FinitePlace F) (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : letI := krullTopology F E
      Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : IsLocalRelativeWeilMap v w.1 e ι) :
    (finiteComponent rec v).ker = normSubgroup (v.adicCompletion F) (w.1.adicCompletion E) ∧
    (finiteComponent rec v).range = (decompositionHom v w.1).range ∧
    ∀ ev : LocalFactor.RankOne.ReciprocityCandidate (padicField v),
      GeometricWeilReciprocityRelation (padicField v) (padicField v).canonicalTopologicalData ev →
      ∀ g : Weil.Local.localWeilGroup (padicField v),
        finiteComponent rec v ((LocalFactor.RankOne.reciprocityUnits (padicField v) ev g)⁻¹) =
          decompositionHom v w.1 (localRestriction v w.1 g) := by
  obtain ⟨ev, hev, -⟩ := geometricWeilReciprocityExistenceUniqueness
    (residuePrime v) (padicField v) (padicField v).canonicalTopologicalData
  let ι₀ : Weil.Local.localWeilGroup (padicField v) →* RelativeWeilGroup c F E :=
    letI := krullTopology F E
    ι.toMonoidHom
  let av := LocalFactor.RankOne.reciprocityUnits (padicField v) ev
  let aw := LocalFactor.RankOne.reciprocityUnits (towerPadicField v w.1) e
  let j := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
  have hlocal := localTransferReciprocity c F E v w.1 e ι hι ev hev
  have hloc (g : Weil.Local.localWeilGroup (padicField v)) :
      finiteComponent rec v ((av g)⁻¹) = projection c F E (ι g) := by
    change rec (j ((av g)⁻¹)) = _
    rw [map_inv, ← hlocal g, hrec]
  have hav (x : (v.adicCompletion F)ˣ) :
      ∃ g : Weil.Local.localWeilGroup (padicField v), x = (av g)⁻¹ := by
    obtain ⟨g, hg⟩ := Correspondence.reciprocityUnits_surjective (padicField v) ev x⁻¹
    exact ⟨g, by rw [show av g = x⁻¹ from hg, inv_inv]⟩
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨g, hxg⟩ := hav x
      have hgker : g ∈ ((projection c F E).comp ι₀).ker := by
        change projection c F E (ι g) = 1
        rw [← hloc g, ← hxg]
        exact hx
      have hιker : ((projection c F E).comp ι₀).ker = _ := ker_projection_comp_eq hι
      rw [hιker] at hgker
      obtain ⟨y, rfl⟩ := hgker
      have hnorm := hlocal (completionWeilMap v w.1 y)
      rw [hι.2.2 y, map_inv, transfer_inclusion, ideleClassNorm_ofAdicCompletion] at hnorm
      have heq : FiniteExtension.localUnitNorm v w.1 (aw y) = av (completionWeilMap v w.1 y) :=
        ofAdicCompletion_injective v (inv_injective hnorm)
      exact ⟨(aw y)⁻¹, by
        change FiniteExtension.localUnitNorm v w.1 ((aw y)⁻¹) = x
        rw [map_inv, heq]
        exact hxg.symm⟩
    · rintro _ ⟨y, rfl⟩
      change rec (j (FiniteExtension.localUnitNorm v w.1 y)) = 1
      change j (FiniteExtension.localUnitNorm v w.1 y) ∈ rec.toMonoidHom.ker
      rw [hker]
      exact ⟨IdeleClassGroup.ofAdicCompletion (𝓞 E) E w.1 y, ideleClassNorm_ofAdicCompletion v w y⟩
  · rw [← range_projection_comp_eq hι]
    ext σ
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨g, hxg⟩ := hav x
      exact ⟨g, by rw [MonoidHom.comp_apply, hxg, hloc]; rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(av g)⁻¹, hloc g⟩
  · intro a ha g
    have hτ := localTransferReciprocity c F E v w.1 e ι hι a ha g
    change rec (j ((LocalFactor.RankOne.reciprocityUnits (padicField v) a g)⁻¹)) = _
    rw [map_inv, ← hτ, hrec]
    exact projection_eq_decompositionHom hι g

end GlobalNormReciprocity

/-- Global reciprocity for a cyclic extension, with the actual local norm kernels and the
images of the finite components. -/
def GlobalNormReciprocityStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    ∃ rec : IdeleClassGroup (𝓞 F) F →ₜ* (E ≃ₐ[F] E),
      Function.Surjective rec ∧
      rec.toMonoidHom.ker = (ideleClassNorm (K := F) (L := E)).toMonoidHom.range ∧
      ∀ (v : Global.FinitePlace F) (w : FinitePlacesAbove E v),
        (GlobalNormReciprocity.finiteComponent rec v).ker =
          normSubgroup (v.adicCompletion F) (w.1.adicCompletion E) ∧
        (GlobalNormReciprocity.finiteComponent rec v).range = (decompositionHom v w.1).range ∧
        ∀ ev : LocalFactor.RankOne.ReciprocityCandidate (padicField v),
          GeometricWeilReciprocityRelation (padicField v) (padicField v).canonicalTopologicalData ev →
          ∀ g : Weil.Local.localWeilGroup (padicField v),
            GlobalNormReciprocity.finiteComponent rec v
                ((LocalFactor.RankOne.reciprocityUnits (padicField v) ev g)⁻¹) =
              decompositionHom v w.1 (RelativeWeilGroup.localRestriction v w.1 g)

set_option maxHeartbeats 1000000 in
/-- Descend the relative Weil projection along transfer, then apply the two local transfer
identities at each finite place. -/
theorem globalNormReciprocity : GlobalNormReciprocityStatement.{u} := by
  intro F E _ _ _ _ _ _ _
  obtain ⟨I, hI, c, hc⟩ := GlobalNormReciprocity.exists_compatible_classFamily.{u}
  obtain ⟨hτ, hτker⟩ := RelativeWeilGroup.relativeWeilTransferReciprocity I hI c hc F E
  obtain ⟨rec, hrec⟩ := GlobalNormReciprocity.exists_quotient_of_transfer c hτ hτker
  obtain ⟨hs, hk⟩ := GlobalNormReciprocity.quotient_surjective_and_ker c hτ rec hrec
  refine ⟨rec, hs, hk, fun v w => ?_⟩
  obtain ⟨e, he, -⟩ := geometricWeilReciprocityExistenceUniqueness
    (residuePrime v) (towerPadicField v w.1) (towerPadicField v w.1).canonicalTopologicalData
  obtain ⟨ι, hι⟩ := localRelativeWeilMapExistence I hI c hc F E v w.1 e he
  exact GlobalNormReciprocity.finiteComponent_ker_and_range c rec hrec hk v w e ι hι

end Langlands.BaseChange
