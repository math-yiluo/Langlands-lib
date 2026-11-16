import Langlands.Sheaf.Equivariant.AnalyticSubgroupRefinements

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory

universe u v z

variable {C : Type u} [Category.{v} C]
variable {G : Type z} [Group G] [TopologicalSpace G]
variable {X : C} {P : MorphismProperty C} {ρ : G →* Aut X}

/-- Local equivariance of lifts along a plain arrow gives intertwining by the
same group element on a common open subgroup. -/
theorem exists_openSubgroup_intertwines_of_isLocallyEquivariant
    {U V : TwistedOver P ρ} {H H' : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ}
    {b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ}
    (ha : IsLift a) (hb : IsLift b) {f : V ⟶ U} (ht : Hom.twist f = 1)
    (hf : IsLocallyEquivariant a b f) :
    ∃ (N : OpenSubgroup G) (hNH : N ≤ H) (hNH' : N ≤ H'),
      ∀ (g : G) (hg : g ∈ N),
        (b ⟨g, hNH' hg⟩).unop ≫ f = f ≫ (a ⟨g, hNH hg⟩).unop := by
  obtain ⟨M, hMH, hM⟩ := hf H' le_rfl
  refine ⟨M ⊓ H', inf_le_left.trans hMH, inf_le_right, fun g hg => ?_⟩
  obtain ⟨k, -, hk⟩ := hM ⟨g, hMH hg.1⟩ hg.1
  have hkg : (k : G) = g := by
    have e := congrArg Hom.twist hk
    dsimp only [IsLift] at ha hb
    simpa only [comp_twist, ht, ha, hb, one_mul, mul_one, inv_inj] using e
  have he : k = (⟨g, hg.2⟩ : (H' : Subgroup G)) := Subtype.ext hkg
  simpa only [he] using hk

end Langlands.Sheaf.Equivariant.TwistedOver

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {ρ : G →* Aut X}
variable {P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))} [P.RespectsIso]

/-- Untwisting a locally equivariant arrow and translating its source lift
makes it intertwine the same group elements on an open subgroup. -/
theorem exists_openSubgroup_intertwines_untwist
    {U V : P.Over ⊤ X} {Q : OpenSubgroup G}
    {a : (Q : Subgroup G) →* (End ((ι P ρ).obj U))ᵐᵒᵖ} (ha : IsLift a)
    (m : ActionLift ρ V.hom) (T : OpenSubgroup G) (hT : (T : Subgroup G) ≤ m.subgroup)
    (f : (ι P ρ).obj V ⟶ (ι P ρ).obj U)
    (hf : IsLocallyEquivariant a
      ((liftAction (U := (ι P ρ).obj V) m).comp (Subgroup.inclusion hT)) f) :
    ∃ (N : OpenSubgroup G) (hNQ : N ≤ Q)
      (hNm : (N : Subgroup G) ≤ (m.translate (Hom.twist f)).subgroup),
      ∀ (g : G) (hg : g ∈ N),
        (liftAction (U := (ι P ρ).obj ((translate P ρ (Hom.twist f)).obj V))
          (m.translate (Hom.twist f)) ⟨g, hNm hg⟩).unop ≫
            (ι P ρ).map (untwist (Hom.twist f) f rfl) =
        (ι P ρ).map (untwist (Hom.twist f) f rfl) ≫ (a ⟨g, hNQ hg⟩).unop := by
  obtain ⟨M, hMQ, hM⟩ := hf T le_rfl
  have hk (g : G) (hg : g ∈ M) :
      ∃ k : (T : Subgroup G), (k : G) = (Hom.twist f)⁻¹ * g * Hom.twist f ∧
        (liftAction m (Subgroup.inclusion hT k)).unop ≫ f =
          f ≫ (a ⟨g, hMQ hg⟩).unop := by
    obtain ⟨k, -, he⟩ := hM ⟨g, hMQ hg⟩ hg
    refine ⟨k, ?_, he⟩
    have et := congrArg Hom.twist he
    change Hom.twist f * (k : G)⁻¹ = Hom.twist (a ⟨g, hMQ hg⟩).unop * Hom.twist f at et
    rw [ha] at et
    have ei : (k : G)⁻¹ = (Hom.twist f)⁻¹ * g⁻¹ * Hom.twist f := by
      calc
        (k : G)⁻¹ = (Hom.twist f)⁻¹ * (Hom.twist f * (k : G)⁻¹) :=
          (inv_mul_cancel_left _ _).symm
        _ = (Hom.twist f)⁻¹ * (g⁻¹ * Hom.twist f) := congrArg _ et
        _ = _ := (mul_assoc _ _ _).symm
    simpa only [inv_inv, mul_inv_rev, mul_assoc] using congrArg Inv.inv ei
  have hMm : (M : Subgroup G) ≤ (m.translate (Hom.twist f)).subgroup := by
    intro g hg
    obtain ⟨k, he, -⟩ := hk g hg
    apply (m.mem_translateSubgroup (Hom.twist f) g).2
    rw [← he]
    exact hT k.2
  refine ⟨M, hMQ, hMm, fun g hg => ?_⟩
  obtain ⟨k, he, heq⟩ := hk g hg
  apply hom_ext
  · change 1 * g⁻¹ = Hom.twist (a ⟨g, hMQ hg⟩).unop * 1
    rw [ha]
    simp only [one_mul, mul_one]
  · have e := congrArg Hom.left heq
    have eh :
        m.translateHom (Hom.twist f) ⟨g⁻¹, inv_mem (hMm hg)⟩ =
          (Subgroup.inclusion hT k)⁻¹ := by
      apply Subtype.ext
      rw [ActionLift.coe_translateHom]
      change (Hom.twist f)⁻¹ * g⁻¹ * Hom.twist f = (k : G)⁻¹
      rw [he]
      group
    change (m.action (m.translateHom (Hom.twist f) ⟨g⁻¹, inv_mem (hMm hg)⟩)).hom ≫
        Hom.left f = Hom.left f ≫ Hom.left (a ⟨g, hMQ hg⟩).unop
    rw [eh]
    exact e

/-- A finite plain covering refinement equipped with actual source lifts and
one open subgroup on which all arrows intertwine the target action. -/
structure CommonSubgroupRefinement
    (Adm : P.Over ⊤ X → Prop) (J : GrothendieckTopology (P.Over ⊤ X))
    {U : P.Over ⊤ X} {Q : OpenSubgroup G}
    (a : (Q : Subgroup G) →* (End ((ι P ρ).obj U))ᵐᵒᵖ) (S : Sieve U) where
  size : ℕ
  obj : Fin size → P.Over ⊤ X
  arrow : ∀ i, obj i ⟶ U
  subgroup : OpenSubgroup G
  le_target : subgroup ≤ Q
  lift : ∀ i, ActionLift ρ (obj i).hom
  le_lift : ∀ i, (subgroup : Subgroup G) ≤ (lift i).subgroup
  admissible : ∀ i, Adm (obj i)
  mem : ∀ i, S (arrow i)
  covering : Sieve.ofArrows obj arrow ∈ J U
  equivariant : ∀ i (g : G) (hg : g ∈ subgroup),
    (liftAction (U := (ι P ρ).obj (obj i)) (lift i) ⟨g, le_lift i hg⟩).unop ≫
        (ι P ρ).map (arrow i) =
      (ι P ρ).map (arrow i) ≫ (a ⟨g, le_target hg⟩).unop

/-- Finite local equivariant refinements yield plain refinement data on one
common open subgroup, by translating sources and intersecting finitely many
intertwining subgroups. -/
theorem nonempty_commonSubgroupRefinement
    (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    [(liftSystem P ρ Adm).HasFiniteEquivariantRefinements (twistedTopology ρ J)]
    {U : P.Over ⊤ X} {Q : OpenSubgroup G}
    {a : (Q : Subgroup G) →* (End ((ι P ρ).obj U))ᵐᵒᵖ}
    (ha : (liftSystem P ρ Adm).IsAdmissible ((ι P ρ).obj U) Q a)
    {S : Sieve U} (hS : S ∈ J U) :
    Nonempty (CommonSubgroupRefinement Adm J a S) := by
  classical
  let SG : Sieve ((ι P ρ).obj U) := S.functorPushforward (ι P ρ)
  have hSG : SG ∈ twistedTopology ρ J ((ι P ρ).obj U) :=
    J.superset_covering (Sieve.le_functorPushforward_pullback _ _) hS
  obtain ⟨n, V, T, b, f, hV, hfS, hlocal, hcov⟩ :=
    LocalActionSystem.HasFiniteEquivariantRefinements.exists_refinement
      (L := liftSystem P ρ Adm) (J := twistedTopology ρ J) ha hSG
  choose hVAdm m hT hb using hV
  have hlocal' (i : Fin n) : IsLocallyEquivariant a
      ((liftAction (U := (ι P ρ).obj (V i).obj) (m i)).comp
        (Subgroup.inclusion (hT i))) (f i) := by
    rw [← hb i]
    exact hlocal i
  choose M hMQ hMm heq using fun i =>
    exists_openSubgroup_intertwines_untwist
      (isLiftSystem_liftSystem Adm _ _ _ ha) (m i) (T i) (hT i) (f i) (hlocal' i)
  let N : OpenSubgroup G := Q ⊓ Finset.univ.inf M
  have hNM (i : Fin n) : N ≤ M i :=
    inf_le_right.trans (Finset.inf_le (f := M) (Finset.mem_univ i))
  refine ⟨{
    size := n
    obj := fun i => (translate P ρ (Hom.twist (f i))).obj (V i).obj
    arrow := fun i => untwist (Hom.twist (f i)) (f i) rfl
    subgroup := N
    le_target := inf_le_left
    lift := fun i => (m i).translate (Hom.twist (f i))
    le_lift := fun i _ hg => hMm i (hNM i hg)
    admissible := fun i => hAdm _ _ (hVAdm i)
    mem := fun i => untwist_mem_of_functorPushforward (f i) (hfS i)
    covering := covering_untwist_family J V f hcov
    equivariant := fun i g hg => heq i g (hNM i hg)
  }⟩

/-- A chosen finite covering refinement with a common open acting subgroup. -/
def commonSubgroupRefinement
    (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    [(liftSystem P ρ Adm).HasFiniteEquivariantRefinements (twistedTopology ρ J)]
    {U : P.Over ⊤ X} {Q : OpenSubgroup G}
    {a : (Q : Subgroup G) →* (End ((ι P ρ).obj U))ᵐᵒᵖ}
    (ha : (liftSystem P ρ Adm).IsAdmissible ((ι P ρ).obj U) Q a)
    {S : Sieve U} (hS : S ∈ J U) :
    CommonSubgroupRefinement Adm J a S :=
  Classical.choice (nonempty_commonSubgroupRefinement Adm hAdm J ha hS)

end Langlands.Sheaf.Equivariant.Analytic
