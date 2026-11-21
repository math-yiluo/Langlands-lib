import Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclic
import Langlands.Cohomology.CoinducedFilteredAcyclic

/-! # The deck action on fixed sections of an étale G-sheaf -/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z w a

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable {U V : TwistedOver (etale (K := K)) ρ}

section Compatibility

variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- An arrow with trivial twist intertwines two supplied distinguished étale lifts
on an open subgroup. Its trivial twist identifies the two group elements in the
restriction equivariance condition. -/
theorem exists_openSubgroup_intertwining_distinguishedLifts
    (hU : IsDistinguishedEtale U.hom) (hV : IsDistinguishedEtale V.hom)
    (lU : ActionLift ρ U.hom) (lV : ActionLift ρ V.hom) (f : U ⟶ V)
    (hf : Hom.twist f = 1) :
    ∃ (M : OpenSubgroup G) (hMU : (M : Subgroup G) ≤ lU.subgroup)
      (hMV : (M : Subgroup G) ≤ lV.subgroup), ∀ (g : G) (hg : g ∈ M),
        (lU.action ⟨g, hMU hg⟩).hom ≫ Hom.left f =
          Hom.left f ≫ (lV.action ⟨g, hMV hg⟩).hom := by
  have haU : (distinguishedLiftSystem ρ).IsAdmissible U (liftOpenSubgroup lU) (liftAction lU) :=
    ⟨hU, lU, le_rfl, MonoidHom.ext fun _ => rfl⟩
  have haV : (distinguishedLiftSystem ρ).IsAdmissible V (liftOpenSubgroup lV) (liftAction lV) :=
    ⟨hV, lV, le_rfl, MonoidHom.ext fun _ => rfl⟩
  have he := LocalActionSystem.HasAdmissibleRefinements.isRestrictionEquivariant
    (J := twistedEtaleTopology ρ) haV haU f
  obtain ⟨N, hNU, hN⟩ := he (liftOpenSubgroup lV) le_rfl
  let M := N ⊓ liftOpenSubgroup lV
  have hMU : M ≤ liftOpenSubgroup lU := inf_le_left.trans hNU
  have hMV : M ≤ liftOpenSubgroup lV := inf_le_right
  refine ⟨M, hMU, hMV, fun g hg => ?_⟩
  have hginv : g⁻¹ ∈ M := inv_mem hg
  let h : lU.subgroup := ⟨g⁻¹, hMU hginv⟩
  have hh : (h : G) ∈ N := (OpenSubgroup.mem_inf.mp hginv).1
  obtain ⟨k, -, hk⟩ := hN h hh
  have hkh : (h : G)⁻¹ = (k : G)⁻¹ := by
    have ht := congrArg Hom.twist hk
    change Hom.twist f * (h : G)⁻¹ = (k : G)⁻¹ * Hom.twist f at ht
    simpa only [hf, one_mul, mul_one] using ht
  have hk' : k = (⟨g⁻¹, hMV hginv⟩ : lV.subgroup) :=
    Subtype.ext (inv_inj.mp hkh).symm
  subst k
  have hl := congrArg Hom.left hk
  change (lU.action h⁻¹).hom ≫ Hom.left f =
    Hom.left f ≫ (lV.action (⟨g⁻¹, hMV hginv⟩ : lV.subgroup)⁻¹).hom at hl
  simpa only [show h⁻¹ = ⟨g, hMU hg⟩ by
      apply Subtype.ext
      exact inv_inv g,
    show (⟨g⁻¹, hMV hginv⟩ : lV.subgroup)⁻¹ = ⟨g, hMV hg⟩ by
      apply Subtype.ext
      exact inv_inv g] using hl

/-- One open subgroup of a supplied lift commutes with every automorphism in a
finite family over the base. -/
theorem exists_openSubgroup_commuting_with_deck (hV : IsDistinguishedEtale V.hom)
    (l : ActionLift ρ V.hom) {Γ : Type a} [Finite Γ] (deck : Γ → Aut V.obj.left)
    (hdeck : ∀ γ, (deck γ).hom ≫ V.hom = V.hom) :
    ∃ (M : OpenSubgroup G) (hM : (M : Subgroup G) ≤ l.subgroup),
      ∀ (γ : Γ) (g : G) (hg : g ∈ M),
        (l.action ⟨g, hM hg⟩).hom ≫ (deck γ).hom =
          (deck γ).hom ≫ (l.action ⟨g, hM hg⟩).hom := by
  classical
  choose N hNl _ hN using fun γ =>
    exists_openSubgroup_intertwining_distinguishedLifts hV hV l l
      (deckEndomorphism V (deck γ) (hdeck γ)) rfl
  let M := liftOpenSubgroup l ⊓ OpenSubgroup.iInfOfFinite N
  have hM : M ≤ liftOpenSubgroup l := inf_le_left
  refine ⟨M, hM, fun γ g hg => ?_⟩
  exact hN γ g ((OpenSubgroup.iInfOfFinite_le N γ) ((OpenSubgroup.mem_inf.mp hg).2))

end Compatibility

section Representation

variable {R : Type w} [CommRing R] (S : EtaleGSheaf ρ (ModuleCat.{w} R))
variable (l : ActionLift ρ V.hom) (N : Subgroup G) (hN : N ≤ l.subgroup)
variable {Γ : Type a} [Group Γ] (deck : Γ →* Aut V.obj.left)
variable (hdeck : ∀ γ, (deck γ).hom ≫ V.hom = V.hom)
variable (hcomm : ∀ (γ : Γ) (k : l.subgroup),
  (l.action k).hom ≫ (deck γ).hom = (deck γ).hom ≫ (l.action k).hom)

/-- Membership in the fixed submodule is precisely the pointwise fixed section condition. -/
theorem mem_liftFixedSubmodule_iff (s : S.obj.obj.obj (op V)) :
    s ∈ liftFixedSubmodule S V l N hN ↔ ∀ (g : G) (hg : g ∈ N),
      S.obj.obj.map (liftAction l ⟨g, hN hg⟩).unop.op s = s := by
  simp [liftFixedSubmodule, LinearMap.sub_apply, sub_eq_zero]

omit [TopologicalSpace G] in
private theorem deckEndomorphism_one :
    deckEndomorphism V (deck 1) (hdeck 1) = 𝟙 V :=
  hom_ext rfl (by change (deck 1).hom = 𝟙 _; rw [map_one]; rfl)

omit [TopologicalSpace G] in
private theorem deckEndomorphism_mul (γ δ : Γ) :
    deckEndomorphism V (deck (γ * δ)) (hdeck (γ * δ)) =
      deckEndomorphism V (deck δ) (hdeck δ) ≫ deckEndomorphism V (deck γ) (hdeck γ) :=
  hom_ext (one_mul 1).symm (rho_mul_hom (ρ := deck) γ δ)

include hcomm in
private theorem liftAction_comm_deckEndomorphism (γ : Γ) (k : l.subgroup) :
    (liftAction l k).unop ≫ deckEndomorphism V (deck γ) (hdeck γ) =
      deckEndomorphism V (deck γ) (hdeck γ) ≫ (liftAction l k).unop := by
  refine hom_ext ?_ (hcomm γ k⁻¹)
  simp [deckEndomorphism]

include hcomm in
/-- The action of the finite-cover deck group on the fixed submodule. The left
representation acts by restriction along the inverse deck transformation. -/
def galoisFixedSectionRepresentation : Representation R Γ (liftFixedSubmodule S V l N hN) where
  toFun γ := (S.obj.obj.map (deckEndomorphism V (deck γ⁻¹) (hdeck γ⁻¹)).op).hom.restrict (by
    intro s hs
    rw [mem_liftFixedSubmodule_iff] at hs ⊢
    intro g hg
    let k : (liftOpenSubgroup l : Subgroup G) := ⟨g, hN hg⟩
    change S.obj.obj.map (liftAction l k).unop.op
        (S.obj.obj.map (deckEndomorphism V (deck γ⁻¹) (hdeck γ⁻¹)).op s) = _
    rw [← map_op_comp_apply, liftAction_comm_deckEndomorphism l deck hdeck hcomm γ⁻¹ k,
      map_op_comp_apply, hs g hg])
  map_one' := by
    ext s
    change S.obj.obj.map (deckEndomorphism V (deck (1 : Γ)⁻¹) _).op s.1 = s.1
    rw [inv_one, deckEndomorphism_one, op_id, S.obj.obj.map_id]
    rfl
  map_mul' γ δ := by
    ext s
    change S.obj.obj.map (deckEndomorphism V (deck (γ * δ)⁻¹) _).op s.1 =
      S.obj.obj.map (deckEndomorphism V (deck γ⁻¹) _).op
        (S.obj.obj.map (deckEndomorphism V (deck δ⁻¹) _).op s.1)
    rw [mul_inv_rev, deckEndomorphism_mul, map_op_comp_apply]

@[simp]
theorem coe_galoisFixedSectionRepresentation_apply (γ : Γ)
    (s : liftFixedSubmodule S V l N hN) :
    (galoisFixedSectionRepresentation S l N hN deck hdeck hcomm γ s).1 =
      S.obj.obj.map (deckEndomorphism V (deck γ⁻¹) (hdeck γ⁻¹)).op s.1 := rfl

end Representation

section Coinduction

variable {R : Type w} [CommRing R] {S : EtaleGSheaf ρ (ModuleCat.{w} R)}
variable {Γ : Type} [Group Γ]
variable (l : ActionLift ρ V.hom) (N : Subgroup G) (hN : N ≤ l.subgroup)
variable (deck : Γ →* Aut V.obj.left) (hdeck : ∀ γ, (deck γ).hom ≫ V.hom = V.hom)
variable (hcomm : ∀ (γ : Γ) (k : l.subgroup),
  (l.action k).hom ≫ (deck γ).hom = (deck γ).hom ≫ (l.action k).hom)

/-- The fixed-section representation with the deck group lifted to the coefficient
universe, as required by the group cohomology functor. -/
abbrev galoisFixedSectionRep : Rep.{w} R (ULift.{w} Γ) :=
  Rep.of ((galoisFixedSectionRepresentation S l N hN deck hdeck hcomm).comp
    MulEquiv.ulift.toMonoidHom)

variable {L : Type uL} [NormedField L] [NormedAlgebra K L] [Finite Γ]

/-- The fixed-section hypothesis gives coinduction coordinates for the deck
representation. The inverse in the coordinates cancels the inverse deck action
in the left representation. -/
theorem galoisFixedSectionRep_exists_bijective_inv (hS : HasCoinducedGaloisFixedSections L S)
    (hV : IsDistinguishedEtale V.hom)
    (hfree : ∀ (γ : Γ) (p : (localizedFieldPointFunctor L).obj V.obj.left),
      (localizedFieldPointFunctor L).map (deck γ).hom p = p → γ = 1)
    (hopen : IsOpen (N : Set G)) :
    ∃ (A : ModuleCat.{w} R)
      (π : galoisFixedSectionRep (S := S) l N hN deck hdeck hcomm →ₗ[R] A),
      Function.Bijective fun s γ =>
        π ((galoisFixedSectionRep (S := S) l N hN deck hdeck hcomm).ρ γ⁻¹ s) := by
  obtain ⟨A, π, hπ⟩ := hS V hV Γ deck hdeck hfree l hcomm N hopen hN
  refine ⟨A, π.comp (liftFixedSubmodule S V l N hN).subtype, ?_⟩
  have hreindex : Function.Bijective (fun f : Γ → A => fun γ : ULift.{w} Γ => f γ.down) := by
    refine ⟨fun f g h => funext fun γ => congrFun h (ULift.up γ), ?_⟩
    intro f
    exact ⟨fun γ => f (ULift.up γ), funext fun ⟨_⟩ => rfl⟩
  change Function.Bijective fun s : liftFixedSubmodule S V l N hN => fun γ : ULift.{w} Γ =>
    π ((galoisFixedSectionRepresentation S l N hN deck hdeck hcomm γ.down⁻¹ s).1)
  have hcoord := hreindex.comp hπ
  change Function.Bijective (fun s : liftFixedSubmodule S V l N hN => fun γ : ULift.{w} Γ =>
    π (S.obj.obj.map (deckEndomorphism V (deck γ.down) (hdeck γ.down)).op s.1)) at hcoord
  simpa only [coe_galoisFixedSectionRepresentation_apply, inv_inv] using hcoord

/-- The fixed sections of a distinguished, equivariant finite Galois datum have
vanishing group cohomology in positive degrees. -/
theorem isZero_groupCohomology_succ_galoisFixedSectionRep
    (hS : HasCoinducedGaloisFixedSections L S) (hV : IsDistinguishedEtale V.hom)
    (hfree : ∀ (γ : Γ) (p : (localizedFieldPointFunctor L).obj V.obj.left),
      (localizedFieldPointFunctor L).map (deck γ).hom p = p → γ = 1)
    (hopen : IsOpen (N : Set G)) (n : ℕ) :
    IsZero (groupCohomology (galoisFixedSectionRep (S := S) l N hN deck hdeck hcomm) (n + 1)) := by
  obtain ⟨A, π, hπ⟩ :=
    galoisFixedSectionRep_exists_bijective_inv l N hN deck hdeck hcomm hS hV hfree hopen
  exact CoinducedFilteredAcyclic.isZero_groupCohomology_succ_of_bijective_inv _ π hπ n

end Coinduction

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
