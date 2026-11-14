import Langlands.Sheaf.Equivariant.AnalyticSubgroupRestriction

noncomputable section

namespace Langlands.Sheaf.Equivariant.LocalActionSystem

open CategoryTheory

variable {C : Type*} [Category C] {G : Type*} [Group G] [TopologicalSpace G]

/-- A finite covering refinement with its admissible local actions and local
equivariance witnesses. -/
structure FiniteEquivariantRefinement (L : LocalActionSystem C G)
    (J : GrothendieckTopology C) {U : C} {Q : OpenSubgroup G}
    (a : (Q : Subgroup G) →* (End U)ᵐᵒᵖ) (S : Sieve U) where
  size : ℕ
  obj : Fin size → C
  subgroup : Fin size → OpenSubgroup G
  action : ∀ i, (subgroup i : Subgroup G) →* (End (obj i))ᵐᵒᵖ
  arrow : ∀ i, obj i ⟶ U
  admissible : ∀ i, L.IsAdmissible (obj i) (subgroup i) (action i)
  mem : ∀ i, S (arrow i)
  equivariant : ∀ i, IsLocallyEquivariant a (action i) (arrow i)
  covering : Sieve.ofArrows obj arrow ∈ J U

end Langlands.Sheaf.Equivariant.LocalActionSystem

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G]
variable {ρ : G →* Aut X} {H : Subgroup G}
variable {P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))} [P.RespectsIso]

/-- Untwisting an arrow in the extension of a plain sieve returns an arrow of
that plain sieve. -/
theorem untwist_mem_of_functorPushforward {U V : P.Over ⊤ X} {S : Sieve U}
    (f : (ι P ρ).obj V ⟶ (ι P ρ).obj U)
    (hf : (S.functorPushforward (ι P ρ)) f) :
    S (untwist (Hom.twist f) f rfl) := by
  obtain ⟨W, g, k, hg, hfg⟩ := hf
  have hk : Hom.twist k = Hom.twist f := by
    have e := congrArg Hom.twist hfg
    simpa only [comp_twist, ι_map_twist, homMk_twist, one_mul] using e.symm
  have he : untwist (Hom.twist f) f rfl = untwist (Hom.twist f) k hk ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    change Hom.left f = Hom.left k ≫ g.left
    exact congrArg Hom.left hfg
  rw [he]
  exact S.downward_closed hg _

/-- Untwisting every member of a covering family preserves the covering property. -/
theorem covering_untwist_family (J : GrothendieckTopology (P.Over ⊤ X))
    [IsTranslationInvariant (ρ := ρ) J] {U : TwistedOver P ρ} {I : Type*}
    (V : I → TwistedOver P ρ) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ twistedTopology ρ J U) :
    Sieve.ofArrows (fun i => (translate P ρ (Hom.twist (f i))).obj (V i).obj)
      (fun i => untwist (Hom.twist (f i)) (f i) rfl) ∈ J U.obj := by
  refine J.superset_covering ?_ hf
  rintro W g ⟨Y, k, _, ⟨i⟩, hkg⟩
  have hk : Hom.twist (k ≫ relabel ρ (Hom.twist (f i)) (V i).obj) = 1 := by
    have e := congrArg Hom.twist hkg
    simpa only [comp_twist, relabel_twist, ι_map_twist, homMk_twist] using e
  obtain ⟨k₀, hk₀⟩ := exists_ι_map_of_twist_eq_one
    (k ≫ relabel ρ (Hom.twist (f i)) (V i).obj) hk
  refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨i, k₀, ?_⟩
  apply (ι P ρ).map_injective
  rw [Functor.map_comp, hk₀, Category.assoc, relabel_comp_ι_map_untwist]
  exact hkg.symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Local equivariance of a twisted arrow becomes ordinary local intertwining
after translating its source and restricting the translated lift to an open
subgroup. -/
theorem isLocallyEquivariant_untwist_subgroup (hH : IsOpen (H : Set G))
    {U V : P.Over ⊤ X} (l : ActionLift (ρ.comp H.subtype) U.hom)
    (S : OpenSubgroup H) (hS : (S : Subgroup H) ≤ l.subgroup)
    (m : ActionLift ρ V.hom) (T : OpenSubgroup G) (hT : (T : Subgroup G) ≤ m.subgroup)
    (f : (ι P ρ).obj V ⟶ (ι P ρ).obj U)
    (hf : IsLocallyEquivariant
      (H := ⟨(S : Subgroup H).map H.subtype, isOpen_map_subtype hH S.isOpen⟩)
      (H' := T)
      ((liftAction (U := (ι P ρ).obj U) (liftOfSubgroup hH l)).comp
        (Subgroup.inclusion (Subgroup.map_mono (f := H.subtype) hS)))
      ((liftAction (U := (ι P ρ).obj V) m).comp (Subgroup.inclusion hT)) f) :
    IsLocallyEquivariant
      ((liftAction (U := (ι P (ρ.comp H.subtype)).obj U) l).comp
        (Subgroup.inclusion hS))
      (liftAction (U := (ι P (ρ.comp H.subtype)).obj
          ((translate P ρ (Hom.twist f)).obj V))
        (liftToSubgroup H (m.translate (Hom.twist f))))
      ((ι P (ρ.comp H.subtype)).map (untwist (Hom.twist f) f rfl)) := by
  classical
  obtain ⟨M, hMS, hM⟩ := hf T le_rfl
  let N : OpenSubgroup H := S ⊓ M.comap H.subtype continuous_subtype_val
  have hk (g : H) (hg : g ∈ N) :
      ∃ k : (T : Subgroup G), (k : G) = (Hom.twist f)⁻¹ * (g : G) * Hom.twist f ∧
        (liftAction m (Subgroup.inclusion hT k)).unop ≫ f =
          f ≫ (liftAction (liftOfSubgroup hH l)
            ⟨(g : G), Subgroup.map_mono (f := H.subtype) hS (hMS hg.2)⟩).unop := by
    obtain ⟨k, -, he⟩ := hM ⟨(g : G), hMS hg.2⟩ hg.2
    refine ⟨k, ?_, he⟩
    have et := congrArg Hom.twist he
    change Hom.twist f * (k : G)⁻¹ = (g : G)⁻¹ * Hom.twist f at et
    have ei : (k : G)⁻¹ = (Hom.twist f)⁻¹ * (g : G)⁻¹ * Hom.twist f := by
      calc
        (k : G)⁻¹ = (Hom.twist f)⁻¹ * (Hom.twist f * (k : G)⁻¹) :=
          (inv_mul_cancel_left _ _).symm
        _ = (Hom.twist f)⁻¹ * ((g : G)⁻¹ * Hom.twist f) := congrArg _ et
        _ = _ := (mul_assoc _ _ _).symm
    simpa only [inv_inv, mul_inv_rev, mul_assoc] using congrArg Inv.inv ei
  have hNm : (N : Subgroup H) ≤
      (liftToSubgroup H (m.translate (Hom.twist f))).subgroup := by
    intro g hg
    obtain ⟨k, he, -⟩ := hk g hg
    apply (m.mem_translateSubgroup (Hom.twist f) (g : G)).2
    rw [← he]
    exact hT k.2
  refine isLocallyEquivariant_of_intertwines N inf_le_left hNm fun g hg => ?_
  obtain ⟨k, he, heq⟩ := hk g hg
  have hmem : (g : G) ∈ (m.translate (Hom.twist f)).subgroup := hNm hg
  apply hom_ext
  · change 1 * g⁻¹ = g⁻¹ * 1
    simp only [one_mul, mul_one]
  · have e := congrArg Hom.left heq
    have eh :
        m.translateHom (Hom.twist f)
          ⟨(g : G)⁻¹, inv_mem hmem⟩ =
        (Subgroup.inclusion hT k)⁻¹ := by
      apply Subtype.ext
      rw [ActionLift.coe_translateHom]
      change (Hom.twist f)⁻¹ * (g : G)⁻¹ * Hom.twist f = (k : G)⁻¹
      rw [he]
      group
    change (m.action (m.translateHom (Hom.twist f)
        ⟨(g : G)⁻¹, inv_mem hmem⟩)).hom ≫ Hom.left f =
      Hom.left f ≫ (l.action (Subgroup.inclusion hS ⟨g, hg.1⟩)⁻¹).hom
    rw [eh]
    exact e

/-- Finite equivariant refinements for the full group give actual finite
refinement data on the site of an open subgroup. -/
theorem nonempty_subgroupFiniteEquivariantRefinement (hH : IsOpen (H : Set G))
    (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    [(liftSystem P ρ Adm).HasFiniteEquivariantRefinements (twistedTopology ρ J)]
    {U : TwistedOver P (ρ.comp H.subtype)} {Q : OpenSubgroup H}
    {a : (Q : Subgroup H) →* (End U)ᵐᵒᵖ}
    (ha : (liftSystem P (ρ.comp H.subtype) Adm).IsAdmissible U Q a)
    {S : Sieve U} (hS : S ∈ twistedTopology (ρ.comp H.subtype) J U) :
    Nonempty ((liftSystem P (ρ.comp H.subtype) Adm).FiniteEquivariantRefinement
      (twistedTopology (ρ.comp H.subtype) J) a S) := by
  classical
  obtain ⟨hU, l, hQ, rfl⟩ := ha
  let QG : OpenSubgroup G :=
    ⟨(Q : Subgroup H).map H.subtype, isOpen_map_subtype hH Q.isOpen⟩
  let lG : ActionLift ρ U.obj.hom := liftOfSubgroup hH l
  have hQG : (QG : Subgroup G) ≤ lG.subgroup := Subgroup.map_mono hQ
  let aG := (liftAction (U := (ι P ρ).obj U.obj) lG).comp (Subgroup.inclusion hQG)
  let S₀ : Sieve U.obj := S.functorPullback (ι P (ρ.comp H.subtype))
  let SG : Sieve ((ι P ρ).obj U.obj) := S₀.functorPushforward (ι P ρ)
  have hSG : SG ∈ twistedTopology ρ J ((ι P ρ).obj U.obj) :=
    J.superset_covering (Sieve.le_functorPushforward_pullback _ _) hS
  obtain ⟨n, V, T, b, f, hV, hfS, hlocal, hcov⟩ :=
    LocalActionSystem.HasFiniteEquivariantRefinements.exists_refinement
      (L := liftSystem P ρ Adm) (J := twistedTopology ρ J)
      (a := aG) ⟨hU, lG, hQG, rfl⟩ hSG
  choose hVAdm m hT hb using hV
  let mH (i : Fin n) := liftToSubgroup H ((m i).translate (Hom.twist (f i)))
  let VH (i : Fin n) : TwistedOver P (ρ.comp H.subtype) :=
    (ι P (ρ.comp H.subtype)).obj ((translate P ρ (Hom.twist (f i))).obj (V i).obj)
  let fH (i : Fin n) : VH i ⟶ U :=
    (ι P (ρ.comp H.subtype)).map (untwist (Hom.twist (f i)) (f i) rfl)
  refine ⟨{
    size := n
    obj := VH
    subgroup := fun i => liftOpenSubgroup (U := VH i) (mH i)
    action := fun i => liftAction (U := VH i) (mH i)
    arrow := fH
    admissible := fun i => ⟨hAdm _ _ (hVAdm i), mH i, le_rfl, ?_⟩
    mem := fun i => untwist_mem_of_functorPushforward (f i) (hfS i)
    equivariant := ?_
    covering := ?_
  }⟩
  · exact MonoidHom.ext fun _ => rfl
  · intro i
    have hi := hlocal i
    rw [hb i] at hi
    exact isLocallyEquivariant_untwist_subgroup hH l Q hQ (m i) (T i) (hT i) (f i) hi
  · change Sieve.functorPullback (ι P (ρ.comp H.subtype)) _ ∈ J U.obj
    refine J.superset_covering ?_ (covering_untwist_family J V f hcov)
    rintro W g ⟨Y, k, _, ⟨i⟩, rfl⟩
    exact ⟨_, (ι P (ρ.comp H.subtype)).map k,
      (ι P (ρ.comp H.subtype)).map (untwist (Hom.twist (f i)) (f i) rfl), ⟨i⟩,
      ((ι P (ρ.comp H.subtype)).map_comp k _).symm⟩

/-- A chosen finite equivariant refinement on the site of an open subgroup,
constructed by translating a full-group refinement and restricting its lifts. -/
def subgroupFiniteEquivariantRefinement (hH : IsOpen (H : Set G))
    (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    [(liftSystem P ρ Adm).HasFiniteEquivariantRefinements (twistedTopology ρ J)]
    {U : TwistedOver P (ρ.comp H.subtype)} {Q : OpenSubgroup H}
    {a : (Q : Subgroup H) →* (End U)ᵐᵒᵖ}
    (ha : (liftSystem P (ρ.comp H.subtype) Adm).IsAdmissible U Q a)
    {S : Sieve U} (hS : S ∈ twistedTopology (ρ.comp H.subtype) J U) :
    (liftSystem P (ρ.comp H.subtype) Adm).FiniteEquivariantRefinement
      (twistedTopology (ρ.comp H.subtype) J) a S :=
  Classical.choice (nonempty_subgroupFiniteEquivariantRefinement hH Adm hAdm J ha hS)

/-- Finite equivariant refinements descend to an open subgroup for any
translation-invariant admissibility condition on analytic objects. -/
theorem hasFiniteEquivariantRefinements_subgroup (hH : IsOpen (H : Set G))
    (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    [(liftSystem P ρ Adm).HasFiniteEquivariantRefinements (twistedTopology ρ J)] :
    (liftSystem P (ρ.comp H.subtype) Adm).HasFiniteEquivariantRefinements
      (twistedTopology (ρ.comp H.subtype) J) := by
  constructor
  intro U Q a ha S hS
  let D := subgroupFiniteEquivariantRefinement hH Adm hAdm J ha hS
  exact ⟨D.size, D.obj, D.subgroup, D.action, D.arrow,
    D.admissible, D.mem, D.equivariant, D.covering⟩

/-- The finite equivariant refinement hypothesis for compact quasi-étale
objects passes from the full group to every open subgroup. -/
theorem hasFiniteEquivariantRefinements_compactLiftSystem_subgroup
    (hH : IsOpen (H : Set G))
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)] :
    (compactLiftSystem (ρ.comp H.subtype)).HasFiniteEquivariantRefinements
      (twistedQuasiEtaleTopology (ρ.comp H.subtype)) :=
  hasFiniteEquivariantRefinements_subgroup hH (fun V => IsCompactSpace V.left)
    (fun _ _ hV => hV) (quasiEtaleTopology X)

end Langlands.Sheaf.Equivariant.Analytic
