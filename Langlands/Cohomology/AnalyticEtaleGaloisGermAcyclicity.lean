import Langlands.Cohomology.AnalyticEtaleGaloisGermSections
import Langlands.Cohomology.AnalyticEtaleGaloisOpenShrinking
import Langlands.Cohomology.FilteredGaloisAcyclicity
import Langlands.Geometry.Analytic.DistinguishedEtaleActionLift

/-! # Vanishing group cohomology on a finite Galois germ -/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable {I : Type w} [SmallCategory I] {Γ : Type} [Group Γ]
variable {R : Type w} [CommRing R] (S : EtaleGSheaf ρ (ModuleCat.{w} R))
variable (V : I ⥤ EtaleSite X) (deck : Γ →* Aut V)

/-- Evaluate the natural deck automorphisms on the underlying analytic
space at one stage. -/
def galoisStageDeck (i : I) : Γ →* Aut (V.obj i).left :=
  (Functor.mapAut (V.obj i) (MorphismProperty.Over.forget etale ⊤ X ⋙ Over.forget X)).comp
    ((Functor.mapAut V ((evaluation I (EtaleSite X)).obj i)).comp deck)

theorem galoisStageDeck_over (i : I) (γ : Γ) :
    (galoisStageDeck V deck i γ).asIso.hom ≫ (V.obj i).hom = (V.obj i).hom :=
  MorphismProperty.Over.w ((deck γ).asIso.hom.app i)

private abbrev ordinaryPresheaf : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{w} R :=
  (ι etale ρ).op ⋙ S.obj.obj

/-- The deck representation on all sections at one stage. -/
def galoisStageRepresentation (i : I) :
    Representation R (ULift.{w} Γ) ((ordinaryPresheaf S).obj (op (V.obj i))) where
  toFun γ := ((ordinaryPresheaf S).map ((deck γ.down⁻¹).asIso.hom.app i).op).hom
  map_one' := by
    change ((ordinaryPresheaf S).map ((deck (1 : Γ)⁻¹).asIso.hom.app i).op).hom = 1
    rw [inv_one, map_one]
    change ((ordinaryPresheaf S).map (𝟙 (op (V.obj i)))).hom = 1
    rw [(ordinaryPresheaf S).map_id]
    rfl
  map_mul' γ δ := by
    have he : (deck (γ * δ).down⁻¹).asIso.hom.app i =
        (deck γ.down⁻¹).asIso.hom.app i ≫ (deck δ.down⁻¹).asIso.hom.app i := by
      change (deck (γ.down * δ.down)⁻¹).asIso.hom.app i = _
      rw [mul_inv_rev, map_mul]
      rfl
    change ((ordinaryPresheaf S).map ((deck (γ * δ).down⁻¹).asIso.hom.app i).op).hom = _
    rw [he, op_comp, (ordinaryPresheaf S).map_comp]
    rfl

theorem galoisStageRepresentation_apply (i : I) (γ : ULift.{w} Γ)
    (s : (ordinaryPresheaf S).obj (op (V.obj i))) :
    galoisStageRepresentation S V deck i γ s =
      S.obj.obj.map (deckEndomorphism ((ι etale ρ).obj (V.obj i))
        (galoisStageDeck V deck i γ.down⁻¹).asIso (galoisStageDeck_over V deck i γ.down⁻¹)).op s := rfl

/-- Restriction maps between stages of the Galois germ commute with the
inverse deck action. -/
def galoisStageSections : Iᵒᵖ ⥤ Rep.{w} R (ULift.{w} Γ) where
  obj i := Rep.of (galoisStageRepresentation S V deck i.unop)
  map {i j} f := Rep.ofHom <|
    LinearMap.intertwiningMap_of_isIntertwiningMap
      (galoisStageRepresentation S V deck i.unop) (galoisStageRepresentation S V deck j.unop)
      ((ordinaryPresheaf S).map (V.map f.unop).op).hom (by
        intro γ s
        let a := (deck γ.down⁻¹).asIso.hom.app i.unop
        let b := (deck γ.down⁻¹).asIso.hom.app j.unop
        let p := V.map f.unop
        have hp : p ≫ a = b ≫ p := (deck γ.down⁻¹).asIso.hom.naturality f.unop
        exact (map_op_comp_apply (ordinaryPresheaf S) p a s).symm.trans
          ((congrArg (fun h => (ordinaryPresheaf S).map h.op s) hp).trans
            (map_op_comp_apply (ordinaryPresheaf S) b p s)))
  map_id i := by
    apply Rep.hom_ext
    ext s
    change (ordinaryPresheaf S).map (V.map (𝟙 i.unop)).op s = s
    rw [V.map_id, op_id, (ordinaryPresheaf S).map_id]
    rfl
  map_comp f g := by
    apply Rep.hom_ext
    ext s
    change (ordinaryPresheaf S).map (V.map (g.unop ≫ f.unop)).op s =
      (ordinaryPresheaf S).map (V.map g.unop).op ((ordinaryPresheaf S).map (V.map f.unop).op s)
    rw [V.map_comp, map_op_comp_apply]

theorem galoisStageSections_forget₂ :
    galoisStageSections S V deck ⋙ forget₂ (Rep.{w} R (ULift.{w} Γ)) (ModuleCat.{w} R) =
      V.op ⋙ ((ι etale ρ).op ⋙ S.obj.obj) := rfl

variable [IsTopologicalGroup G] [IsCofiltered I] [Finite Γ]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable {L : Type uL} [NormedField L] [NormedAlgebra K L]

/-- Along a diagram of distinguished Galois stages with cofinal open
restriction, the colimit of sections has vanishing positive deck cohomology. -/
theorem isZero_groupCohomology_succ_galoisStageGerm
    (hS : HasCoinducedGaloisFixedSections L S)
    (hpoints : EtaleCoveringPointsStatement.{u, v} K)
    (hLift : ∀ (U : LocalizedCategory.{u, v, v} (K := K)) (p : U ⟶ X),
      quasiEtale p → IsCompactSpace U → Nonempty (ActionLift ρ p))
    (hdist : ∀ i, IsDistinguishedEtale (V.obj i).hom)
    (htrans : ∀ i, ∀ x y : localizedSpaceFunctor.obj (V.obj i).left,
      localizedSpaceFunctor.map (V.obj i).hom x = localizedSpaceFunctor.map (V.obj i).hom y →
        ∃ γ, localizedSpaceFunctor.map (galoisStageDeck V deck i γ).asIso.hom x = y)
    (hfree : ∀ (i : I) (γ : Γ) (p : (localizedFieldPointFunctor L).obj (V.obj i).left),
      (localizedFieldPointFunctor L).map (galoisStageDeck V deck i γ).asIso.hom p = p → γ = 1)
    (y : localizedSpaceFunctor.obj X)
    (hy : ∀ i, ∃ x : localizedSpaceFunctor.obj (V.obj i).left,
      localizedSpaceFunctor.map (V.obj i).hom x = y)
    (hshrink : ∀ (i : I) (O : Opens (localizedSpaceFunctor.obj X)), y ∈ O →
      ∃ (j : I) (p : j ⟶ i) (T : Opens (localizedSpaceFunctor.obj X)), T ≤ O ∧
        ∃ e : V.obj j ≅ ((etaleOpenRestrictionFunctor X).obj T).obj (V.obj i),
          e.hom ≫ (etaleOpenRestrictionInclusion X T).app (V.obj i) = V.map p)
    {c : Cocone (galoisStageSections S V deck)} (hc : IsColimit c) (n : ℕ) :
    IsZero (groupCohomology c.pt (n + 1)) := by
  classical
  apply CoinducedFilteredAcyclic.isZero_groupCohomology_of_eventually_acyclic_subrepresentation hc
  intro i s
  obtain ⟨x, hx⟩ := hy i.unop
  have htrans' (b d : localizedSpaceFunctor.obj (V.obj i.unop).left)
      (h : localizedSpaceFunctor.map (V.obj i.unop).hom b =
        localizedSpaceFunctor.map (V.obj i.unop).hom d) :
      ∃ γ : ULift.{w} Γ,
        localizedSpaceFunctor.map (galoisStageDeck V deck i.unop γ.down).asIso.hom b = d := by
    obtain ⟨γ, hγ⟩ := htrans i.unop b d h
    exact ⟨ULift.up γ, hγ⟩
  obtain ⟨O, hO, m, W, f, hf, hcov⟩ :=
    exists_open_finite_discreteSieve_family S hpoints
      (fun γ : ULift.{w} Γ => galoisStageDeck V deck i.unop γ.down)
      (fun γ => galoisStageDeck_over V deck i.unop γ.down) htrans' s x
  obtain ⟨j, p, T, hTO, e, he⟩ := hshrink i.unop O (hx ▸ hO)
  let A := (ι etale ρ).obj (V.obj i.unop)
  let B := (ι etale ρ).obj (V.obj j)
  let r : B ⟶ A := (ι etale ρ).map (V.map p)
  let J := twistedEtaleTopology ρ
  have hcov' : (Sieve.ofArrows W f).pullback r ∈ J B := by
    have hp := J.pullback_stable ((ι etale ρ).map e.hom) (hcov T hTO)
    rw [← Sieve.pullback_comp, ← (ι etale ρ).map_comp, he] at hp
    exact hp
  obtain ⟨lA⟩ := nonempty_actionLift_of_isDistinguishedEtale hLift (hdist i.unop)
  obtain ⟨lB⟩ := nonempty_actionLift_of_isDistinguishedEtale hLift (hdist j)
  have ha : (distinguishedLiftSystem ρ).IsAdmissible A (liftOpenSubgroup lA) (liftAction lA) :=
    ⟨hdist i.unop, lA, le_rfl, MonoidHom.ext fun _ => rfl⟩
  have hb : (distinguishedLiftSystem ρ).IsAdmissible B (liftOpenSubgroup lB) (liftAction lB) :=
    ⟨hdist j, lB, le_rfl, MonoidHom.ext fun _ => rfl⟩
  let t := fun d => S.obj.obj.map r.op (s d)
  have ht d : IsDiscreteSection S.obj.obj (liftAction (U := B) lB) (t d) :=
    isDiscreteSection_restriction_of_finite_discreteSieve_cover
      (isLiftSystem_liftSystem (ρ := ρ) fun Z => IsDistinguishedEtale Z.hom)
      S.obj.property ha hb r (s d) ⟨m, W, f, hf d, hcov'⟩
  obtain ⟨P, a, ha, hz, hs⟩ :=
    exists_galoisFixedSubrepresentation_of_discreteSections hS
      (hdist j) lB (galoisStageDeck V deck j) (galoisStageDeck_over V deck j) (hfree j)
      (galoisStageRepresentation S V deck j) (galoisStageRepresentation_apply S V deck j) t ht n
  exact ⟨op j, p.op, P, a, ha, hz, hs⟩

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
