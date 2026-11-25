import Langlands.Cohomology.AnalyticEtaleGaloisFixedSections

/-! # Fixed subrepresentations for finite families of Galois sections -/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z w a

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {L : Type uL} [NormedField L] [NormedAlgebra K L]
variable {G : Type z} [Group G] [TopologicalSpace G]
variable {ρ : G →* Aut X}
variable {R : Type w} [CommRing R] {S : EtaleGSheaf ρ (ModuleCat.{w} R)}
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The inclusion of the fixed sections into all sections intertwines the
inverse-deck actions. -/
def galoisFixedSectionInclusion {V : TwistedOver (etale (K := K)) ρ}
    (l : ActionLift ρ V.hom) (B : OpenSubgroup G) (hB : (B : Subgroup G) ≤ l.subgroup)
    {Γ : Type} [Group Γ] (deck : Γ →* Aut V.obj.left)
    (hdeck : ∀ γ, (deck γ).asIso.hom ≫ V.hom = V.hom)
    (hcomm : ∀ (γ : Γ) (k : l.subgroup),
      (l.action k).asIso.hom ≫ (deck γ).asIso.hom = (deck γ).asIso.hom ≫ (l.action k).asIso.hom)
    (σ : Representation R (ULift.{w} Γ) (S.obj.obj.obj (op V)))
    (hσ : ∀ (γ : ULift.{w} Γ) (t : S.obj.obj.obj (op V)),
      σ γ t = S.obj.obj.map (deckEndomorphism V (deck γ.down⁻¹).asIso (hdeck γ.down⁻¹)).op t) :
    galoisFixedSectionRep (S := S) l B hB deck hdeck hcomm ⟶ Rep.of σ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ σ
    (liftFixedSubmodule S V l B hB).subtype (by
      intro γ t
      change (galoisFixedSectionRepresentation S l B hB deck hdeck hcomm γ.down t).1 = σ γ t.1
      rw [coe_galoisFixedSectionRepresentation_apply, hσ])

/-- On a distinguished object with a supplied lift, a finite family whose
sections are discrete for the lift belongs to an acyclic deck subrepresentation
when the fixed sections are coinduced. -/
theorem exists_galoisFixedSubrepresentation_of_discreteSections
    (hS : HasCoinducedGaloisFixedSections L S)
    {V : TwistedOver (etale (K := K)) ρ} (hV : IsDistinguishedEtale V.hom)
    (l : ActionLift ρ V.hom) {Γ : Type} [Group Γ] [Finite Γ]
    (deck : Γ →* Aut V.obj.left) (hdeck : ∀ γ, (deck γ).asIso.hom ≫ V.hom = V.hom)
    (hfree : ∀ (γ : Γ) (p : (localizedFieldPointFunctor L).obj V.obj.left),
      (localizedFieldPointFunctor L).map (deck γ).asIso.hom p = p → γ = 1)
    (σ : Representation R (ULift.{w} Γ) (S.obj.obj.obj (op V)))
    (hσ : ∀ (γ : ULift.{w} Γ) (t : S.obj.obj.obj (op V)),
      σ γ t = S.obj.obj.map (deckEndomorphism V (deck γ.down⁻¹).asIso (hdeck γ.down⁻¹)).op t)
    {D : Type a} [Finite D] (s : D → S.obj.obj.obj (op V))
    (hdisc : ∀ i, IsDiscreteSection S.obj.obj (liftAction l) (s i))
    (n : ℕ) :
    ∃ (A : Rep.{w} R (ULift.{w} Γ)) (a : A ⟶ Rep.of σ),
      Function.Injective a ∧ IsZero (groupCohomology A (n + 1)) ∧
        ∀ i, ∃ t : A, a t = s i := by
  classical
  obtain ⟨M, hM, hcomm⟩ := exists_openSubgroup_commuting_with_deck hV l deck hdeck
  let l' := l.restrict M M.isOpen hM
  have hcomm' (γ : Γ) (k : l'.subgroup) :
      (l'.action k).asIso.hom ≫ (deck γ).asIso.hom = (deck γ).asIso.hom ≫ (l'.action k).asIso.hom :=
    hcomm γ k k.property
  have hs (i : D) : IsDiscreteSection S.obj.obj (liftAction l') (s i) := by
    exact IsDiscreteSection.of_agree (N := M) (a := liftAction l) (a' := liftAction l')
      hM le_rfl (fun _ _ => rfl) (hdisc i)
  choose N hNl hN using hs
  let B := liftOpenSubgroup l' ⊓ OpenSubgroup.iInfOfFinite N
  have hB : (B : Subgroup G) ≤ l'.subgroup := inf_le_left
  have hmem (i : D) : s i ∈ liftFixedSubmodule S V l' B hB := by
    apply (mem_liftFixedSubmodule_iff S l' B hB (s i)).2
    intro g hg
    exact hN i ⟨g, hB hg⟩ ((OpenSubgroup.iInfOfFinite_le N i) (OpenSubgroup.mem_inf.mp hg).2)
  exact ⟨_, galoisFixedSectionInclusion l' B hB deck hdeck hcomm' σ hσ, Subtype.val_injective,
    isZero_groupCohomology_succ_galoisFixedSectionRep l' B hB deck hdeck hcomm' hS hV hfree
      B.isOpen n, fun i => ⟨⟨s i, hmem i⟩, rfl⟩⟩

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
