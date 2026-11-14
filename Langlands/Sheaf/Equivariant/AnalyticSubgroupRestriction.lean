import Langlands.Sheaf.Equivariant.TwistedSubgroupRestriction
import Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements
import Langlands.Sheaf.Equivariant.AnalyticEtaleRepCohomology
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleRepCohomology

/-!
# Restriction of étale and quasi-étale `G`-sheaves to a subgroup

Let `G` act on an analytic space `X` and let `H` be a subgroup of `G`, with the subspace
topology. Restriction of sheaves on the twisted site of `G` to the twisted site of `H`
(`TwistedSubgroupRestriction`) sends étale `G`-sheaves to étale `H`-sheaves when `G` is a
topological group, and quasi-étale `G`-sheaves to quasi-étale `H`-sheaves when `H` is open.
The proofs compare the lifts of the two actions: a lift for `G` restricts to a lift for `H`,
a lift for an open `H` is a lift for `G`, and the translate of a lift by `t ∈ G`
(`ActionLift.translate`) is a lift to the translate of the object by `t`. Restriction forgets nothing over `X`, so it commutes
with `b^*`, and the representations of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)` restrict to
the representations of `H` for the restricted sheaf.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Groups

variable {G : Type z} [Group G] (H : Subgroup G)

theorem continuous_subtype_subgroupComap [TopologicalSpace G] (S : Subgroup G) :
    Continuous (H.subtype.subgroupComap S) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable {H} in
theorem mem_of_mem_map_subtype {S : Subgroup H} {g : G} (hg : g ∈ S.map H.subtype) : g ∈ H := by
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hg
  exact y.2

variable {H} in
theorem mk_mem_of_mem_map_subtype {S : Subgroup H} {g : G} (hg : g ∈ S.map H.subtype) :
    (⟨g, mem_of_mem_map_subtype hg⟩ : H) ∈ S := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
  exact hy

/-- The image in `G` of a subgroup `S` of `H` maps back to `S`. -/
def mapSubtypeHom (S : Subgroup H) : S.map H.subtype →* S where
  toFun x := ⟨⟨x.1, mem_of_mem_map_subtype x.2⟩, mk_mem_of_mem_map_subtype x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_mapSubtypeHom [TopologicalSpace G] (S : Subgroup H) :
    Continuous (mapSubtypeHom H S) :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

variable {H} in
/-- The image in `G` of an open subgroup of an open subgroup `H` is open. -/
theorem isOpen_map_subtype [TopologicalSpace G] (hH : IsOpen (H : Set G)) {S : Subgroup H}
    (hS : IsOpen (S : Set H)) : IsOpen ((S.map H.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map, Subgroup.coe_subtype]
  exact hH.isOpenMap_subtype_val _ hS

end Groups

section Lifts

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] [TopologicalSpace G]
variable {ρ : G →* Aut X} {U : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}

variable (H : Subgroup G) in
/-- The restriction of a lift of `ρ` to the subgroup `H`: the open subgroup `S ∩ H` of `H` acts
through `S`. -/
def liftToSubgroup (l : ActionLift ρ f) : ActionLift (ρ.comp H.subtype) f where
  subgroup := l.subgroup.comap H.subtype
  isOpen_subgroup := l.isOpen_subgroup.preimage continuous_subtype_val
  action := l.action.comp (H.subtype.subgroupComap l.subgroup)
  isContinuousAction := l.isContinuousAction.comp
    ⟨H.subtype.subgroupComap l.subgroup, continuous_subtype_subgroupComap H l.subgroup⟩
  equivariant _ := l.equivariant _

/-- A lift of the action of an open subgroup `H` is a lift of the action of `G`: an open
subgroup of `H` is open in `G`. -/
def liftOfSubgroup {H : Subgroup G} (hH : IsOpen (H : Set G))
    (l : ActionLift (ρ.comp H.subtype) f) : ActionLift ρ f where
  subgroup := l.subgroup.map H.subtype
  isOpen_subgroup := isOpen_map_subtype hH l.isOpen_subgroup
  action := l.action.comp (mapSubtypeHom H l.subgroup)
  isContinuousAction := l.isContinuousAction.comp
    ⟨mapSubtypeHom H l.subgroup, continuous_mapSubtypeHom H l.subgroup⟩
  equivariant _ := l.equivariant _

variable [IsTopologicalGroup G]

variable (H : Subgroup G) in
theorem conj_mem_of_mem_liftToSubgroup_translate (l : ActionLift ρ f) (t : G) {h : H}
    (hh : h ∈ (liftToSubgroup H (l.translate t)).subgroup) : t⁻¹ * (h : G) * t ∈ l.subgroup :=
  (l.mem_translateSubgroup t (h : G)).1 hh

end Lifts

section LiftSystems

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] [TopologicalSpace G]
variable {ρ : G →* Aut X} (H : Subgroup G)
variable {P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))}
variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

variable {H} in
/-- For an open subgroup `H`, the local action of a lift for `H`, mapped to the twisted
category of `G`, is the local action of the corresponding lift for `G`. -/
theorem subgroupInclusion_map_liftAction (hH : IsOpen (H : Set G))
    {U : TwistedOver P (ρ.comp H.subtype)} (l : ActionLift (ρ.comp H.subtype) (TwistedOver.hom U))
    (h : ((liftOpenSubgroup l : OpenSubgroup H) : Subgroup H)) :
    (subgroupInclusion ρ H).map (liftAction l h).unop =
      (liftAction (U := (subgroupInclusion ρ H).obj U) (liftOfSubgroup hH l)
        ⟨((h : H) : G), Subgroup.mem_map_of_mem H.subtype h.2⟩).unop :=
  hom_ext rfl rfl

/-- For an open subgroup `H`, the restriction to `H` of a presheaf whose sections are discrete
for the lifts of the action of `G` on the objects satisfying `Adm` has sections discrete for
the lifts of the action of `H` on these objects. -/
theorem isDiscrete_subgroupRestriction {H : Subgroup G} (hH : IsOpen (H : Set G))
    (Adm : P.Over ⊤ X → Prop) {F : (TwistedOver P ρ)ᵒᵖ ⥤ A}
    (hF : (liftSystem P ρ Adm).IsDiscrete F) :
    (liftSystem P (ρ.comp H.subtype) Adm).IsDiscrete ((subgroupInclusion ρ H).op ⋙ F) := by
  rintro U S a ⟨hU, l, hS, rfl⟩ s
  let S' : OpenSubgroup G := ⟨(S : Subgroup H).map H.subtype, isOpen_map_subtype hH S.isOpen⟩
  have hS' : (S' : Subgroup G) ≤ (liftOfSubgroup hH l).subgroup := Subgroup.map_mono hS
  obtain ⟨N, hNS, hN⟩ := hF ((subgroupInclusion ρ H).obj U) S'
    ((liftAction (U := (subgroupInclusion ρ H).obj U) (liftOfSubgroup hH l)).comp
      (Subgroup.inclusion hS')) ⟨hU, liftOfSubgroup hH l, hS', rfl⟩ s
  refine ⟨N.comap H.subtype continuous_subtype_val, fun h hh => ?_, fun h hh => ?_⟩
  · exact (Subgroup.mem_map_iff_mem H.subtype_injective).1 (hNS hh)
  · have hx := hN ⟨((h : H) : G), Subgroup.mem_map_of_mem H.subtype h.2⟩ hh
    exact (congrArg (fun φ => F.map φ.op s)
      (subgroupInclusion_map_liftAction hH l (Subgroup.inclusion hS h))).trans hx

variable [P.RespectsIso] [IsTopologicalGroup G]

/-- The local action of the restriction to `H` of the translate by `t` of a lift on `V`, on
the translate `tV`, is the local action of the lift at `t⁻¹ h t` conjugated by the relabelling
isomorphism `V ≅ tV`. -/
theorem subgroupInclusion_map_liftAction_translate (t : G) {V : P.Over ⊤ X}
    (l : ActionLift ρ (TwistedOver.hom ((ι P ρ).obj V)))
    (h : ((liftOpenSubgroup (U := (ι P (ρ.comp H.subtype)).obj ((translate P ρ t).obj V))
      (liftToSubgroup H (l.translate t)) : OpenSubgroup H) : Subgroup H)) :
    (subgroupInclusion ρ H).map (liftAction (U := (ι P (ρ.comp H.subtype)).obj
        ((translate P ρ t).obj V)) (liftToSubgroup H (l.translate t)) h).unop =
      relabelInv ρ t V ≫ (liftAction l ⟨t⁻¹ * ((h : H) : G) * t,
        conj_mem_of_mem_liftToSubgroup_translate H l t h.2⟩).unop ≫ relabel ρ t V := by
  refine hom_ext ?_ ?_
  · change ((h : H) : G)⁻¹ = (t * (t⁻¹ * ((h : H) : G) * t)⁻¹) * t⁻¹
    group
  · have hmem : (h : H)⁻¹ ∈ (liftToSubgroup H (l.translate t)).subgroup := inv_mem h.2
    have e : l.translateHom t ⟨((h : H) : G)⁻¹, hmem⟩ =
        (⟨t⁻¹ * ((h : H) : G) * t, conj_mem_of_mem_liftToSubgroup_translate H l t h.2⟩ :
          l.subgroup)⁻¹ := by
      apply Subtype.ext
      rw [ActionLift.coe_translateHom]
      change t⁻¹ * ((h : H) : G)⁻¹ * t = (t⁻¹ * ((h : H) : G) * t)⁻¹
      group
    change (l.action (l.translateHom t ⟨((h : H) : G)⁻¹, hmem⟩)).hom =
      𝟙 _ ≫ (l.action (⟨t⁻¹ * ((h : H) : G) * t,
        conj_mem_of_mem_liftToSubgroup_translate H l t h.2⟩ : l.subgroup)⁻¹).hom ≫ 𝟙 _
    rw [e, Category.id_comp, Category.comp_id]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem relabelInv_comp_relabel (t : G) (V : P.Over ⊤ X) :
    relabelInv ρ t V ≫ relabel ρ t V = 𝟙 _ :=
  hom_ext (mul_inv_cancel t) (Category.id_comp _)

theorem map_comp_op_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ A) {W Y Z : C}
    (a : W ⟶ Y) (b : Y ⟶ Z) (y : ToType (F.obj (op Z))) :
    F.map (a ≫ b).op y = F.map a.op (F.map b.op y) := by
  rw [op_comp, F.map_comp, CategoryTheory.comp_apply]

theorem map_comp_comp_op_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ A) {W Y Z V : C}
    (a : W ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ V) (y : ToType (F.obj (op V))) :
    F.map (a ≫ b ≫ c).op y = F.map a.op (F.map b.op (F.map c.op y)) := by
  rw [op_comp, op_comp, F.map_comp, F.map_comp, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply]

/-- The restriction to any subgroup `H` of a sheaf whose sections are locally discrete for the
lifts of the action of `G` on objects satisfying a translation-invariant `Adm` has sections
locally discrete for the lifts of the action of `H`. A discrete section over `V` covering an
arrow over `X` is moved to the translate of `V` by the twist of its arrow, where the
translated lift restricts to a lift for `H`. -/
theorem isLocallyDiscrete_subgroupRestriction (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    {F : (TwistedOver P ρ)ᵒᵖ ⥤ A}
    (hF : (liftSystem P ρ Adm).IsLocallyDiscrete (twistedTopology ρ J) F) :
    (liftSystem P (ρ.comp H.subtype) Adm).IsLocallyDiscrete
      (twistedTopology (ρ.comp H.subtype) J) ((subgroupInclusion ρ H).op ⋙ F) := by
  intro U s
  show Sieve.functorPullback (ι P (ρ.comp H.subtype)) (X := U.obj) _ ∈ J U.obj
  refine J.superset_covering ?_ (hF ((subgroupInclusion ρ H).obj U) s)
  rintro W φ ⟨V, k, f, S, a, ⟨hV, l, hS, rfl⟩, hs, hkf⟩
  obtain ⟨t, ht⟩ : ∃ t, Hom.twist f = t := ⟨_, rfl⟩
  obtain ⟨f₀, hf⟩ : ∃ f₀ : (translate P ρ t).obj V.obj ⟶ U.obj,
      relabel ρ t V.obj ≫ (ι P ρ).map f₀ = f :=
    ⟨untwist t f ht, relabel_comp_ι_map_untwist t f ht⟩
  have hk : Hom.twist (k ≫ relabel ρ t V.obj) = 1 := by
    have : Hom.twist f * Hom.twist k = 1 := congrArg Hom.twist hkf
    rw [comp_twist, relabel_twist, ← ht]
    exact this
  obtain ⟨k₀, hk₀⟩ := exists_ι_map_of_twist_eq_one (k ≫ relabel ρ t V.obj) hk
  have hφ : k₀ ≫ f₀ = φ := (ι P ρ).map_injective (by
    rw [Functor.map_comp, hk₀, Category.assoc, hf]
    exact hkf)
  subst hf hφ
  refine ⟨(ι P (ρ.comp H.subtype)).obj ((translate P ρ t).obj V.obj),
    (ι P (ρ.comp H.subtype)).map k₀, (ι P (ρ.comp H.subtype)).map f₀,
    liftOpenSubgroup (U := (ι P (ρ.comp H.subtype)).obj ((translate P ρ t).obj V.obj))
      (liftToSubgroup H (l.translate t)),
    (liftAction (U := (ι P (ρ.comp H.subtype)).obj ((translate P ρ t).obj V.obj))
      (liftToSubgroup H (l.translate t))).comp (Subgroup.inclusion le_rfl),
    ⟨hAdm t V.obj hV, liftToSubgroup H (l.translate t), le_rfl, rfl⟩, ?_,
    ((ι P (ρ.comp H.subtype)).map_comp k₀ f₀).symm⟩
  obtain ⟨N, hNS, hN⟩ := hs
  have e2 : ∀ y, F.map (relabelInv ρ t V.obj).op (F.map (relabel ρ t V.obj).op y) = y :=
    fun y => by
      have h1 : F.map (relabelInv ρ t V.obj ≫ relabel ρ t V.obj).op y = y := by
        rw [relabelInv_comp_relabel, op_id, F.map_id, CategoryTheory.id_apply]
      rwa [op_comp, F.map_comp, CategoryTheory.comp_apply] at h1
  refine ⟨(N.comap (MulAut.conj t⁻¹).toMonoidHom
      ((continuous_const.mul continuous_id).mul continuous_const)).comap H.subtype
      continuous_subtype_val, fun h hh => hS (hNS hh), fun h hh => ?_⟩
  have hh' : t⁻¹ * ((h : H) : G) * t ∈ N := by
    have : (MulAut.conj t⁻¹) ((h : H) : G) ∈ N := hh
    rwa [MulAut.conj_apply, inv_inv] at this
  have hx : F.map (liftAction l ⟨t⁻¹ * ((h : H) : G) * t,
        conj_mem_of_mem_liftToSubgroup_translate H l t h.2⟩).unop.op
      (F.map (relabel ρ t V.obj ≫ (ι P ρ).map f₀).op s) =
        F.map (relabel ρ t V.obj ≫ (ι P ρ).map f₀).op s :=
    hN ⟨t⁻¹ * ((h : H) : G) * t, hNS hh'⟩ hh'
  change F.map ((subgroupInclusion ρ H).map (liftAction (U := (ι P (ρ.comp H.subtype)).obj
      ((translate P ρ t).obj V.obj)) (liftToSubgroup H (l.translate t)) h).unop).op
      (F.map ((ι P ρ).map f₀).op s) = F.map ((ι P ρ).map f₀).op s
  refine (congrArg (fun φ => F.map φ.op (F.map ((ι P ρ).map f₀).op s))
    (subgroupInclusion_map_liftAction_translate H t l h)).trans ?_
  refine (map_comp_comp_op_apply F _ _ _ _).trans ?_
  have e1 : F.map (relabel ρ t V.obj).op (F.map ((ι P ρ).map f₀).op s) =
      F.map (relabel ρ t V.obj ≫ (ι P ρ).map f₀).op s :=
    (map_comp_op_apply F _ _ s).symm
  refine (congrArg (fun y => F.map (relabelInv ρ t V.obj).op
    (F.map (liftAction l ⟨t⁻¹ * ((h : H) : G) * t,
      conj_mem_of_mem_liftToSubgroup_translate H l t h.2⟩).unop.op y)) e1).trans ?_
  refine (congrArg (fun y => F.map (relabelInv ρ t V.obj).op y) hx).trans ?_
  exact (congrArg (fun y => F.map (relabelInv ρ t V.obj).op y) e1.symm).trans (e2 _)

end LiftSystems

section GSheaves

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] [TopologicalSpace G]
variable (ρ : G →* Aut X) (H : Subgroup G)
variable (A : Type*) [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Restriction of étale `G`-sheaves to étale `H`-sheaves, for any subgroup `H` of a
topological group: restriction of sheaves on the twisted étale site. -/
def etaleGSheafSubgroupRestriction [IsTopologicalGroup G] :
    EtaleGSheaf ρ A ⥤ EtaleGSheaf (ρ.comp H.subtype) A :=
  ((distinguishedLiftSystem (ρ.comp H.subtype)).smoothSheafProperty A
      (twistedEtaleTopology (ρ.comp H.subtype))).lift
    ((distinguishedLiftSystem ρ).smoothSheafInclusion A (twistedEtaleTopology ρ) ⋙
      subgroupRestriction ρ H (etaleTopology X) A)
    fun F => isLocallyDiscrete_subgroupRestriction H _
      (fun t _ hV => hV.comp_iso (ρ t)) (etaleTopology X) F.property

/-- Restriction of étale `G`-sheaves to `H` followed by the inclusion into sheaves is the
inclusion followed by restriction of sheaves to `H`. -/
def etaleGSheafSubgroupRestrictionCompInclusionIso [IsTopologicalGroup G] :
    etaleGSheafSubgroupRestriction ρ H A ⋙
        (distinguishedLiftSystem (ρ.comp H.subtype)).smoothSheafInclusion A
          (twistedEtaleTopology (ρ.comp H.subtype)) ≅
      (distinguishedLiftSystem ρ).smoothSheafInclusion A (twistedEtaleTopology ρ) ⋙
        subgroupRestriction ρ H (etaleTopology X) A :=
  Iso.refl _

variable {H} in
/-- Restriction of quasi-étale `G`-sheaves to quasi-étale `H`-sheaves, for an open subgroup
`H`: restriction of sheaves on the twisted quasi-étale site. -/
def quasiEtaleGSheafSubgroupRestriction (hH : IsOpen (H : Set G)) :
    QuasiEtaleGSheaf ρ A ⥤ QuasiEtaleGSheaf (ρ.comp H.subtype) A :=
  ((compactLiftSystem (ρ.comp H.subtype)).discreteSheafProperty A
      (twistedQuasiEtaleTopology (ρ.comp H.subtype))).lift
    ((compactLiftSystem ρ).discreteSheafInclusion A (twistedQuasiEtaleTopology ρ) ⋙
      subgroupRestriction ρ H (quasiEtaleTopology X) A)
    fun F => isDiscrete_subgroupRestriction hH _ F.property

variable {H} in
/-- Restriction of quasi-étale `G`-sheaves to `H` followed by the inclusion into sheaves is the
inclusion followed by restriction of sheaves to `H`. -/
def quasiEtaleGSheafSubgroupRestrictionCompInclusionIso (hH : IsOpen (H : Set G)) :
    quasiEtaleGSheafSubgroupRestriction ρ A hH ⋙
        (compactLiftSystem (ρ.comp H.subtype)).discreteSheafInclusion A
          (twistedQuasiEtaleTopology (ρ.comp H.subtype)) ≅
      (compactLiftSystem ρ).discreteSheafInclusion A (twistedQuasiEtaleTopology ρ) ⋙
        subgroupRestriction ρ H (quasiEtaleTopology X) A :=
  Iso.refl _

variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Restriction to `H` commutes with `b^*` on étale `G`-sheaves: both forget the action. -/
def etaleGSheafSubgroupRestrictionCompRestrictionIso [IsTopologicalGroup G] :
    etaleGSheafSubgroupRestriction ρ H (ModuleCat.{max u (v + 1) uL} R) ⋙
        etaleGSheafRestriction.{u, v, uL} (ρ.comp H.subtype) R ≅
      etaleGSheafRestriction.{u, v, uL} ρ R :=
  Iso.refl _

variable {H} in
/-- Restriction to an open `H` commutes with `b^*` on quasi-étale `G`-sheaves: both forget the
action. -/
def quasiEtaleGSheafSubgroupRestrictionCompRestrictionIso (hH : IsOpen (H : Set G)) :
    quasiEtaleGSheafSubgroupRestriction ρ (ModuleCat.{max u (v + 1) uL} R) hH ⋙
        quasiEtaleGSheafRestriction.{u, v, uL} (ρ.comp H.subtype) R ≅
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R :=
  Iso.refl _

end GSheaves

section KanExtensions

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable (ρ : G →* Aut X) (H : Subgroup G)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- If `G` is small, module presheaves on the twisted étale site of `H` have pointwise right
Kan extensions along the subgroup inclusion. -/
theorem etale_subgroupInclusion_hasPointwiseRightKanExtension [Small.{max u (v + 1) uL} G]
    (F : (TwistedOver (etale (K := K)) (ρ.comp H.subtype))ᵒᵖ ⥤
      ModuleCat.{max u (v + 1) uL} R) :
    (subgroupInclusion ρ H).op.HasPointwiseRightKanExtension F := fun Y =>
  haveI := twistedEtale_essentiallySmall_points.{u, v, uL} X (ρ.comp H.subtype)
  haveI := twistedEtale_locallySmall_points.{u, v, uL} X ρ
  haveI := hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL}
    (StructuredArrow Y (subgroupInclusion (P := etale (K := K)) ρ H).op)
    (ModuleCat.{max u (v + 1) uL} R)
  inferInstance

/-- If `G` is small, module presheaves on the twisted quasi-étale site of `H` have pointwise
right Kan extensions along the subgroup inclusion. -/
theorem quasiEtale_subgroupInclusion_hasPointwiseRightKanExtension
    [Small.{max u (v + 1) uL} G]
    (F : (TwistedOver (quasiEtale (K := K)) (ρ.comp H.subtype))ᵒᵖ ⥤
      ModuleCat.{max u (v + 1) uL} R) :
    (subgroupInclusion ρ H).op.HasPointwiseRightKanExtension F := fun Y =>
  haveI := twistedQuasiEtale_essentiallySmall_points.{u, v, uL} X (ρ.comp H.subtype)
  haveI := twistedQuasiEtale_locallySmall_points.{u, v, uL} X ρ
  haveI := hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL}
    (StructuredArrow Y (subgroupInclusion (P := quasiEtale (K := K)) ρ H).op)
    (ModuleCat.{max u (v + 1) uL} R)
  inferInstance

end KanExtensions

section EtaleCohomology

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (H : Subgroup G)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]

/-- The restriction to `H` of the representation of `G` on `H^q(X, b^*F)` is the
representation of `H` on `H^q(X, b^*F|_H)`, naturally in the étale `G`-sheaf `F`. -/
def etaleSubgroupRestrictionCohomologyIso (q : ℕ) :
    etaleRestrictionCohomologyRep.{u, v, uL} ρ R q ⋙ Rep.resFunctor H.subtype ≅
      etaleGSheafSubgroupRestriction ρ H (ModuleCat.{max u (v + 1) uL} R) ⋙
        etaleRestrictionCohomologyRep.{u, v, uL} (ρ.comp H.subtype) R q :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := etale_subgroupInclusion_hasPointwiseRightKanExtension.{u, v, uL} ρ H R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  Functor.isoWhiskerLeft ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (subgroupRestrictionGlobalCohomologyIso ρ H (etaleTopology X) R q)

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)

/-- The restriction to `H` of the representation of `G` on `H^q_c(X, b^*F)` is the
representation of `H` on `H^q_c(X, b^*F|_H)`, naturally in the étale `G`-sheaf `F`. -/
def etaleSubgroupRestrictionCompactCohomologyIso (q : ℕ) :
    etaleRestrictionCompactCohomologyRep L ρ h R q ⋙ Rep.resFunctor H.subtype ≅
      etaleGSheafSubgroupRestriction ρ H (ModuleCat.{max u (v + 1) uL} R) ⋙
        etaleRestrictionCompactCohomologyRep L (ρ.comp H.subtype) h R q :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := etale_subgroupInclusion_hasPointwiseRightKanExtension.{u, v, uL} ρ H R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  Functor.isoWhiskerLeft ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (subgroupRestrictionCompactCohomologyIso ρ H (etaleTopology X) R
      (EtaleSite.pointEquivariance L ρ h) q)

end EtaleCohomology

section QuasiEtaleCohomology

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] [TopologicalSpace G]
variable (ρ : G →* Aut X) {H : Subgroup G} (hH : IsOpen (H : Set G))
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [Small.{max u (v + 1) uL} G]

/-- For an open subgroup `H`, the restriction to `H` of the representation of `G` on
`H^q(X, b^*F)` is the representation of `H` on `H^q(X, b^*F|_H)`, naturally in the
quasi-étale `G`-sheaf `F`. -/
def quasiEtaleSubgroupRestrictionCohomologyIso (q : ℕ) :
    quasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q ⋙ Rep.resFunctor H.subtype ≅
      quasiEtaleGSheafSubgroupRestriction ρ (ModuleCat.{max u (v + 1) uL} R) hH ⋙
        quasiEtaleRestrictionCohomologyRep.{u, v, uL} (ρ.comp H.subtype) R q :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := quasiEtale_subgroupInclusion_hasPointwiseRightKanExtension.{u, v, uL} ρ H R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  Functor.isoWhiskerLeft ((compactLiftSystem ρ).discreteSheafInclusion _ _)
    (subgroupRestrictionGlobalCohomologyIso ρ H (quasiEtaleTopology X) R q)

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)

/-- For an open subgroup `H`, the restriction to `H` of the representation of `G` on
`H^q_c(X, b^*F)` is the representation of `H` on `H^q_c(X, b^*F|_H)`, naturally in the
quasi-étale `G`-sheaf `F`. -/
def quasiEtaleSubgroupRestrictionCompactCohomologyIso (q : ℕ) :
    quasiEtaleRestrictionCompactCohomologyRep L ρ h R q ⋙ Rep.resFunctor H.subtype ≅
      quasiEtaleGSheafSubgroupRestriction ρ (ModuleCat.{max u (v + 1) uL} R) hH ⋙
        quasiEtaleRestrictionCompactCohomologyRep L (ρ.comp H.subtype) h R q :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X (ρ.comp H.subtype) R
  haveI := quasiEtale_subgroupInclusion_hasPointwiseRightKanExtension.{u, v, uL} ρ H R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  Functor.isoWhiskerLeft ((compactLiftSystem ρ).discreteSheafInclusion _ _)
    (subgroupRestrictionCompactCohomologyIso ρ H (quasiEtaleTopology X) R
      (QuasiEtaleSite.pointEquivariance L ρ h) q)

end QuasiEtaleCohomology

end Langlands.Sheaf.Equivariant.Analytic
