import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr
import Langlands.AlgebraicGeometry.Modules.OpenCoverIsoGluing
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentEffectiveProof
import Langlands.AlgebraicGeometry.Picard.LineBundleFiniteMonoDetector
import Mathlib.AlgebraicGeometry.Limits

/-! # Effective flat descent of line bundles over an affine base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.LineBundleFlatDescent

section Trivialize

/-- Morphisms of modules on an empty scheme are equal. -/
lemma hom_ext_of_isEmpty {W : Scheme.{u}} [IsEmpty W] {A B : W.Modules} (φ ψ : A ⟶ B) :
    φ = ψ := by
  ext U a
  have : Subsingleton Γ(B, U) := Module.subsingleton Γ(W, U) _
  exact Subsingleton.elim _ _

/-- Over a pair of equal maps, a square comparison commutes with pullbacks of any
isomorphism. -/
lemma square_comm_of_eq {W C D : Scheme.{u}} (a b : W ⟶ C) (hab : a = b) (c : C ⟶ D)
    (h : a ≫ c = b ≫ c) {M N : D.Modules}
    (e : (Scheme.Modules.pullback c).obj M ≅ (Scheme.Modules.pullback c).obj N) :
    (Scheme.Modules.pullback a).map e.hom ≫ (squarePullbackIso c a b c h N).hom =
      (squarePullbackIso c a b c h M).hom ≫ (Scheme.Modules.pullback b).map e.hom := by
  subst hab
  simp [squarePullbackIso, Scheme.Modules.pullbackCongr]

/-- A line bundle on a quasi-compact scheme becomes trivial on a flat surjective cover by
an affine scheme (a finite disjoint union of affine trivializing opens). -/
theorem exists_trivializing_cover {W : Scheme.{u}} [CompactSpace W] {G : W.Modules}
    (hG : IsLocallyFreeRankOne G) :
    ∃ (V : Scheme.{u}) (v : V ⟶ W), IsAffine V ∧ Flat v ∧ Surjective v ∧
      Nonempty ((Scheme.Modules.pullback v).obj G ≅ SheafOfModules.unit V.ringCatSheaf) := by
  classical
  choose U hU hx he using hG.exists_affine_trivialization
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : W ↦ (U x : Set W))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let g : s → Scheme.{u} := fun x ↦ (U x.1).toScheme
  have : ∀ x, IsAffine (g x) := fun x ↦ hU x.1
  let v : ∐ g ⟶ W := Sigma.desc (fun x ↦ (U x.1).ι)
  have hv : ∀ x, Sigma.ι g x ≫ v = (U x.1).ι := fun x ↦ Sigma.ι_comp_desc _ _
  refine ⟨∐ g, v, inferInstance, inferInstance, ?_, ?_⟩
  · refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
    refine Set.eq_univ_of_univ_subset (fun y _ ↦ ?_)
    obtain ⟨x, hxs, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
    exact Set.mem_iUnion.mpr ⟨⟨x, hxs⟩, by rwa [Scheme.Opens.range_ι]⟩
  · let e : ∀ x, (Scheme.Modules.pullback ((sigmaOpenCover g).f x)).obj
        ((Scheme.Modules.pullback v).obj G) ≅
        (Scheme.Modules.pullback ((sigmaOpenCover g).f x)).obj
          (SheafOfModules.unit (∐ g).ringCatSheaf) := fun x ↦
      compIso (Sigma.ι g x) v (U x.1).ι (hv x) G ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback (U x.1).ι).app G).symm ≪≫
          (he x.1).some ≪≫ (pullbackUnitIso (Sigma.ι g x)).symm
    obtain ⟨E, -, -⟩ := openCoverIsoGluing_of_homGluing OpenCoverHomGluing.openCoverHomGluing (∐ g)
      (sigmaOpenCover g) _ _ e (fun x y ↦ by
        by_cases hxy : x = y
        · subst hxy
          exact square_comm_of_eq _ _ (fst_eq_snd_of_mono_eq _) _ _ (e x)
        · have : IsEmpty ↑(Limits.pullback ((sigmaOpenCover g).f x) ((sigmaOpenCover g).f y)) :=
            isEmpty_pullback_sigmaι_of_ne g hxy
          exact hom_ext_of_isEmpty _ _)
    exact ⟨E⟩

end Trivialize

section UnitAut

variable {W U V : Scheme.{u}} (a b : U ⟶ V)

/-- The automorphism of the structure module of `U` obtained by transporting an isomorphism
`a^* G ≅ b^* G` through a trivialization `β` of `G`. -/
def unitAut {G : V.Modules} (β : G ≅ SheafOfModules.unit V.ringCatSheaf)
    (E : (Scheme.Modules.pullback a).obj G ≅ (Scheme.Modules.pullback b).obj G) :
    SheafOfModules.unit U.ringCatSheaf ≅ SheafOfModules.unit U.ringCatSheaf :=
  (pullbackUnitIso a).symm ≪≫ ((Scheme.Modules.pullback a).mapIso β).symm ≪≫ E ≪≫
    (Scheme.Modules.pullback b).mapIso β ≪≫ pullbackUnitIso b

/-- Transported automorphisms compose. -/
lemma unitAut_trans (c : U ⟶ V) {G : V.Modules} (β : G ≅ SheafOfModules.unit V.ringCatSheaf)
    (E : (Scheme.Modules.pullback a).obj G ≅ (Scheme.Modules.pullback b).obj G)
    (E' : (Scheme.Modules.pullback b).obj G ≅ (Scheme.Modules.pullback c).obj G) :
    unitAut a b β E ≪≫ unitAut b c β E' = unitAut a c β (E ≪≫ E') := by
  ext1
  simp [unitAut]

/-- Equal transported automorphisms come from isomorphisms intertwined by the comparison of
the two trivializations. -/
lemma unitAut_eq {G₁ G₂ : V.Modules} (β₁ : G₁ ≅ SheafOfModules.unit V.ringCatSheaf)
    (β₂ : G₂ ≅ SheafOfModules.unit V.ringCatSheaf)
    (E₁ : (Scheme.Modules.pullback a).obj G₁ ≅ (Scheme.Modules.pullback b).obj G₁)
    (E₂ : (Scheme.Modules.pullback a).obj G₂ ≅ (Scheme.Modules.pullback b).obj G₂)
    (h : unitAut a b β₁ E₁ = unitAut a b β₂ E₂) :
    E₁.hom ≫ (Scheme.Modules.pullback b).map (β₁ ≪≫ β₂.symm).hom =
      (Scheme.Modules.pullback a).map (β₁ ≪≫ β₂.symm).hom ≫ E₂.hom := by
  have h' := congrArg (fun φ ↦ (Scheme.Modules.pullback a).map β₁.hom ≫
    (pullbackUnitIso a).hom ≫ φ ≫ (pullbackUnitIso b).inv ≫
      (Scheme.Modules.pullback b).map β₂.inv) (congrArg Iso.hom h)
  simp only [unitAut, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc] at h'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [h']
  simp

/-- Transported automorphisms are compatible with precomposition. -/
lemma unitAut_precomp (k : W ⟶ U) {G : V.Modules} (β : G ≅ SheafOfModules.unit V.ringCatSheaf)
    (E : (Scheme.Modules.pullback a).obj G ≅ (Scheme.Modules.pullback b).obj G) :
    unitAut (k ≫ a) (k ≫ b) β (((Scheme.Modules.pullbackComp k a).app G).symm ≪≫
        (Scheme.Modules.pullback k).mapIso E ≪≫ (Scheme.Modules.pullbackComp k b).app G) =
      structureAutPullback k (unitAut a b β E) := by
  ext1
  have ha : (pullbackUnitIso (k ≫ a)).inv ≫
      (Scheme.Modules.pullbackComp k a).inv.app (SheafOfModules.unit V.ringCatSheaf) =
        (pullbackUnitIso k).inv ≫ (Scheme.Modules.pullback k).map (pullbackUnitIso a).inv := by
    rw [← pullbackUnitIso_inv_comp k a]
    simp
  have hb := pullbackUnitComposition W U V k b
  have na := (Scheme.Modules.pullbackComp k a).inv.naturality β.inv
  have nb := (Scheme.Modules.pullbackComp k b).hom.naturality β.hom
  simp only [Functor.comp_map] at na nb
  simp only [unitAut, structureAutPullback_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% na, reassoc_of% ha, ← reassoc_of% nb, hb]

end UnitAut

section Pullbackθ

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} (D : Datum p F)

/-- The descent isomorphisms pulled back along `w : V ⟶ X`, as isomorphisms between
pullbacks of `w^* F`. -/
def Datum.pullbackθ {V U : Scheme.{u}} (w : V ⟶ X) (a b : U ⟶ V)
    (h : (a ≫ w) ≫ p = (b ≫ w) ≫ p) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback w).obj F) ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback w).obj F) :=
  compIso a w (a ≫ w) rfl F ≪≫ D.θ U (a ≫ w) (b ≫ w) h ≪≫ (compIso b w (b ≫ w) rfl F).symm

lemma Datum.pullbackθ_trans {V U : Scheme.{u}} (w : V ⟶ X) (a b c : U ⟶ V)
    (h : (a ≫ w) ≫ p = (b ≫ w) ≫ p) (h' : (b ≫ w) ≫ p = (c ≫ w) ≫ p)
    (h'' : (a ≫ w) ≫ p = (c ≫ w) ≫ p) :
    D.pullbackθ w a b h ≪≫ D.pullbackθ w b c h' = D.pullbackθ w a c h'' := by
  ext1
  simp only [Datum.pullbackθ, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [reassoc_of% (D.coc _ _ _ _ h h' h'')]

lemma Datum.pullbackθ_precomp {V U U' : Scheme.{u}} (w : V ⟶ X) (k : U' ⟶ U) (a b : U ⟶ V)
    (h : (a ≫ w) ≫ p = (b ≫ w) ≫ p) (h' : ((k ≫ a) ≫ w) ≫ p = ((k ≫ b) ≫ w) ≫ p) :
    D.pullbackθ w (k ≫ a) (k ≫ b) h' =
      ((Scheme.Modules.pullbackComp k a).app _).symm ≪≫
        (Scheme.Modules.pullback k).mapIso (D.pullbackθ w a b h) ≪≫
          (Scheme.Modules.pullbackComp k b).app _ := by
  ext1
  have e : (D.pullbackθ w (k ≫ a) (k ≫ b) h').hom =
      tr k rfl rfl (D.pullbackθ w a b h).hom := by
    have ha : k ≫ (a ≫ w) = (k ≫ a) ≫ w := (Category.assoc _ _ _).symm
    have hb : k ≫ (b ≫ w) = (k ≫ b) ≫ w := (Category.assoc _ _ _).symm
    simp only [Datum.pullbackθ, Iso.trans_hom, Iso.symm_hom]
    rw [tr_comp k rfl ha rfl, tr_comp k ha hb rfl,
      tr_compIso k a w (a ≫ w) rfl (k ≫ a) ((k ≫ a) ≫ w) rfl ha rfl,
      ← D.θ_tr k ha hb h h',
      ← inv_eq_tr k rfl hb (compIso b w (b ≫ w) rfl F) (compIso (k ≫ b) w ((k ≫ b) ≫ w) rfl F)
        (tr_compIso k b w (b ≫ w) rfl (k ≫ b) ((k ≫ b) ≫ w) rfl hb rfl F).symm]
  rw [e]
  unfold tr
  rw [compIso_rfl, compIso_rfl]
  simp

end Pullbackθ

section Unit

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} (D : Datum p F)

/-- If `w^* F` is trivial and `q` is affine faithfully flat with `q ≫ t = w ≫ p`, the
descent data descend `w^* F` along `q` to a line bundle `L`, with an isomorphism
`Ξ : q^* L ≅ w^* F` intertwining the canonical comparisons and the descent data. -/
theorem exists_descent_of_trivial {T V : Scheme.{u}} (t : T ⟶ Y) (q : V ⟶ T) (w : V ⟶ X)
    (hqw : q ≫ t = w ≫ p) [IsAffineHom q] [Flat q] [Surjective q]
    (τ : (Scheme.Modules.pullback w).obj F ≅ SheafOfModules.unit V.ringCatSheaf) :
    ∃ (L : T.Modules) (_ : IsLocallyFreeRankOne L)
      (Ξ : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback w).obj F),
      ∀ (U : Scheme.{u}) (a b : U ⟶ V) (h : a ≫ q = b ≫ q)
        (hθ : (a ≫ w) ≫ p = (b ≫ w) ≫ p),
        tr a rfl rfl Ξ.hom ≫ (D.θ U (a ≫ w) (b ≫ w) hθ).hom = tr b h.symm rfl Ξ.hom := by
  have hθ : ∀ {U : Scheme.{u}} {a b : U ⟶ V}, a ≫ q = b ≫ q →
      (a ≫ w) ≫ p = (b ≫ w) ≫ p := by
    intro U a b h
    rw [Category.assoc, Category.assoc, ← hqw, ← Category.assoc, h, Category.assoc]
  let c : ∀ (U : Scheme.{u}) (a b : U ⟶ V), a ≫ q = b ≫ q → Γ(U, ⊤)ˣ :=
    fun U a b h ↦ structureAutScalar (unitAut a b τ (D.pullbackθ w a b (hθ h)))
  obtain ⟨L, α, hα⟩ := unitCocycleDescentEffective V T q inferInstance inferInstance
    inferInstance c (fun U U' k a b h h' ↦ by
      simp only [c]
      rw [D.pullbackθ_precomp w k a b (hθ h) (hθ h'), unitAut_precomp,
        structureAutScalar_pullback])
    (fun U a b d h h' h'' ↦ by
      simp only [c]
      rw [← structureAutScalar_trans, unitAut_trans, D.pullbackθ_trans])
  refine ⟨L.obj, L.property, α ≪≫ τ.symm, fun U a b h hθ' ↦ ?_⟩
  have e₀ := hα U a b h
  simp only [c] at e₀
  have e₁ := structureAutScalar_injective e₀
  have e₂ := unitAut_eq a b α τ (equalCompositeIso q a b h L.obj)
    (D.pullbackθ w a b (hθ h)) e₁
  rw [equalCompositeIso_hom_eq_compIso q a b h (a ≫ q) rfl h.symm] at e₂
  simp only [Datum.pullbackθ, Iso.trans_hom, Iso.symm_hom, Category.assoc] at e₂
  unfold tr
  rw [← cancel_epi (compIso a q (a ≫ q) rfl L.obj).hom,
    ← cancel_mono (compIso b w (b ≫ w) rfl F).inv]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact e₂.symm

/-- The intertwining property with arbitrary prescribed composites. -/
lemma descent_compat_gen {T V : Scheme.{u}} {q : V ⟶ T} {w : V ⟶ X} {L : T.Modules}
    (Ξ : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback w).obj F)
    (hK : ∀ (U : Scheme.{u}) (a b : U ⟶ V) (h : a ≫ q = b ≫ q)
        (hθ : (a ≫ w) ≫ p = (b ≫ w) ≫ p),
        tr a rfl rfl Ξ.hom ≫ (D.θ U (a ≫ w) (b ≫ w) hθ).hom = tr b h.symm rfl Ξ.hom)
    {U : Scheme.{u}} (a b : U ⟶ V) (z : U ⟶ T) (ha : a ≫ q = z) (hb : b ≫ q = z)
    (c₁ c₂ : U ⟶ X) (hc₁ : a ≫ w = c₁) (hc₂ : b ≫ w = c₂) (hθ : c₁ ≫ p = c₂ ≫ p) :
    tr a ha hc₁ Ξ.hom ≫ (D.θ U c₁ c₂ hθ).hom = tr b hb hc₂ Ξ.hom := by
  subst ha hc₁ hc₂
  exact hK U a b hb.symm hθ

end Unit

section Core

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} (D : Datum p F)

/-- Effective descent over an affine scheme mapping to the base: for `t : T ⟶ Y` with `T`
affine, the descent data produce a line bundle on `T` with a descended structure. -/
theorem exists_str [IsAffineHom p] [Flat p] [Surjective p] (hF : IsLocallyFreeRankOne F)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ Y) :
    ∃ N : T.Modules, IsLocallyFreeRankOne N ∧ Nonempty (Str D t N) := by
  have : IsAffine (Limits.pullback p t) := isAffine_of_isAffineHom (pullback.snd p t)
  obtain ⟨V, v, hV, hv, hv', ⟨τ₀⟩⟩ :=
    exists_trivializing_cover (hF.pullback (pullback.fst p t))
  let P := pullback.snd p t
  let Q := pullback.fst p t
  let q := v ≫ P
  let w := v ≫ Q
  have hqw : q ≫ t = w ≫ p := by
    simp only [q, w, P, Q, Category.assoc, pullback.condition]
  obtain ⟨L, hL, Ξ, hK⟩ := exists_descent_of_trivial D t q w hqw
    ((compIso v Q w rfl F).symm ≪≫ τ₀)
  let e := compIso v P q rfl L ≪≫ Ξ ≪≫ (compIso v Q w rfl F).symm
  have hcompat : ∀ (U : Scheme.{u}) (a b : U ⟶ V) (h : a ≫ v = b ≫ v),
      tr a rfl rfl e.hom = tr b h.symm h.symm e.hom := by
    intro U a b h
    have hq : b ≫ q = a ≫ q := by simp only [q, ← Category.assoc, h]
    have hw : b ≫ w = a ≫ w := by simp only [w, ← Category.assoc, h]
    have hP : (a ≫ v) ≫ P = a ≫ q := Category.assoc _ _ _
    have hQ : (a ≫ v) ≫ Q = a ≫ w := Category.assoc _ _ _
    have hθ : (a ≫ w) ≫ p = (a ≫ w) ≫ p := rfl
    have K := descent_compat_gen D Ξ hK a b (a ≫ q) rfl hq (a ≫ w) (a ≫ w) rfl hw hθ
    rw [D.θ_self, Category.comp_id] at K
    simp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [tr_comp a rfl rfl rfl, tr_comp a rfl rfl rfl, tr_comp b h.symm hq h.symm,
      tr_comp b hq hw h.symm, tr_compIso a v P q rfl (a ≫ v) (a ≫ q) rfl rfl hP,
      tr_compIso b v P q rfl (a ≫ v) (a ≫ q) h.symm hq hP,
      tr_compIso_inv a v Q w rfl (a ≫ v) (a ≫ w) rfl rfl hQ,
      tr_compIso_inv b v Q w rfl (a ≫ v) (a ≫ w) h.symm hw hQ, K]
  obtain ⟨γ₀, hγ₀, -⟩ := LineBundleIsoDescent.lineBundleIsoDescent V _ v inferInstance
    inferInstance inferInstance _ _ (hL.pullback P) (hF.pullback Q) e
    (fun U a b h ↦ compat_of_tr_eq v e.hom a b h (a ≫ v) rfl h.symm (hcompat U a b h))
  have key : tr v rfl rfl γ₀.hom = Ξ.hom := by
    have h₀ : (Scheme.Modules.pullback v).map γ₀.hom = e.hom := congrArg Iso.hom hγ₀
    unfold tr
    rw [h₀]
    simp [e]
  have key' : ∀ {U : Scheme.{u}} (a : U ⟶ V) (m : U ⟶ Limits.pullback p t) (hm : a ≫ v = m)
      (z : U ⟶ T) (c : U ⟶ X) (hz : m ≫ P = z) (hc : m ≫ Q = c) (hz' : a ≫ q = z)
      (hc' : a ≫ w = c), tr m hz hc γ₀.hom = tr a hz' hc' Ξ.hom := by
    intro U a m hm z c hz hc hz' hc'
    rw [← key, tr_tr_eq v a hm rfl rfl hz' hc' hz hc]
  refine ⟨L, hL, ⟨{
    γ := fun Z g h hs ↦ CommonSourceCocycle.transport (pullback.lift g h hs.symm)
      P Q h g (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) γ₀
    nat := ?_
    coc := ?_ }⟩⟩
  · intro Z Z' k g h hs g' h' hs' hg hh
    have hm : k ≫ pullback.lift g h hs.symm = pullback.lift g' h' hs'.symm :=
      pullback.hom_ext (by simp [hg]) (by simp [hh])
    rw [transport_hom, transport_hom, tr_tr_eq _ k hm _ _ _ _ (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _)]
  · intro Z g₁ g₂ h hs₁ hs₂ hθ
    let ℓ₁ := pullback.lift g₁ h hs₁.symm
    let ℓ₂ := pullback.lift g₂ h hs₂.symm
    let f₁ := pullback.fst ℓ₁ v
    let s₁ := pullback.snd ℓ₁ v
    let f' := pullback.fst (f₁ ≫ ℓ₂) v
    let a₂ := pullback.snd (f₁ ≫ ℓ₂) v
    let r := f' ≫ f₁
    let a₁ := f' ≫ s₁
    have hm₁ : a₁ ≫ v = r ≫ ℓ₁ := by
      simp only [a₁, r, s₁, f₁, Category.assoc, ← pullback.condition]
    have hm₂ : a₂ ≫ v = r ≫ ℓ₂ := by
      simp only [a₂, r, f', Category.assoc, ← pullback.condition]
    have hℓ₁P : ℓ₁ ≫ P = h := pullback.lift_snd _ _ _
    have hℓ₁Q : ℓ₁ ≫ Q = g₁ := pullback.lift_fst _ _ _
    have hℓ₂P : ℓ₂ ≫ P = h := pullback.lift_snd _ _ _
    have hℓ₂Q : ℓ₂ ≫ Q = g₂ := pullback.lift_fst _ _ _
    have hz₁ : a₁ ≫ q = r ≫ h := by
      simp only [q, ← Category.assoc, hm₁]; simp only [Category.assoc, hℓ₁P]
    have hz₂ : a₂ ≫ q = r ≫ h := by
      simp only [q, ← Category.assoc, hm₂]; simp only [Category.assoc, hℓ₂P]
    have hc₁ : a₁ ≫ w = r ≫ g₁ := by
      simp only [w, ← Category.assoc, hm₁]; simp only [Category.assoc, hℓ₁Q]
    have hc₂ : a₂ ≫ w = r ≫ g₂ := by
      simp only [w, ← Category.assoc, hm₂]; simp only [Category.assoc, hℓ₂Q]
    have hθr : (r ≫ g₁) ≫ p = (r ≫ g₂) ≫ p := by
      simp only [Category.assoc, hθ]
    have hP₁ : (r ≫ ℓ₁) ≫ P = r ≫ h := by rw [Category.assoc, hℓ₁P]
    have hQ₁ : (r ≫ ℓ₁) ≫ Q = r ≫ g₁ := by rw [Category.assoc, hℓ₁Q]
    have hP₂ : (r ≫ ℓ₂) ≫ P = r ≫ h := by rw [Category.assoc, hℓ₂P]
    have hQ₂ : (r ≫ ℓ₂) ≫ Q = r ≫ g₂ := by rw [Category.assoc, hℓ₂Q]
    let φ := CommonSourceCocycle.transport ℓ₁ P Q h g₁ hℓ₁P hℓ₁Q γ₀ ≪≫ D.θ Z g₁ g₂ hθ
    let ψ := CommonSourceCocycle.transport ℓ₂ P Q h g₂ hℓ₂P hℓ₂Q γ₀
    suffices H : φ = ψ from congrArg Iso.hom H
    refine iso_ext_of_tr r (hL.pullback h) (hF.pullback g₂) rfl rfl φ ψ ?_
    have E₁ : tr r rfl rfl φ.hom = tr a₁ hz₁ hc₁ Ξ.hom ≫ (D.θ _ (r ≫ g₁) (r ≫ g₂) hθr).hom := by
      simp only [φ, Iso.trans_hom, transport_hom]
      rw [tr_comp r rfl rfl rfl, tr_tr_eq ℓ₁ r rfl hℓ₁P hℓ₁Q rfl rfl hP₁ hQ₁,
        ← D.θ_tr r rfl rfl hθ hθr, key' a₁ (r ≫ ℓ₁) hm₁ (r ≫ h) (r ≫ g₁) hP₁ hQ₁ hz₁ hc₁]
    have E₂ : tr r rfl rfl ψ.hom = tr a₂ hz₂ hc₂ Ξ.hom := by
      simp only [ψ, transport_hom]
      rw [tr_tr_eq ℓ₂ r rfl hℓ₂P hℓ₂Q rfl rfl hP₂ hQ₂,
        key' a₂ (r ≫ ℓ₂) hm₂ (r ≫ h) (r ≫ g₂) hP₂ hQ₂ hz₂ hc₂]
    rw [E₁, E₂]
    exact descent_compat_gen D Ξ hK a₁ a₂ (r ≫ h) hz₁ hz₂ (r ≫ g₁) (r ≫ g₂) hc₁ hc₂ hθr

end Core

end Langlands.Scheme.Modules.LineBundleFlatDescent
