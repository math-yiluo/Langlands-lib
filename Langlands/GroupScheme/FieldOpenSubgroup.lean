import Langlands.AlgebraicGeometry.Picard.FieldGroupOpenSubgroupClosedProof
import Langlands.AbelianScheme.GroupScheme

/-! # Open subgroups of arbitrary group schemes over a field -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FieldOpenSubgroup

variable {k : Type u} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]

/-- Stability under division on points with values in arbitrary fields. -/
def DivisionStable (U : Set G.left) : Prop :=
  ∀ (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (p q : Over.mk b ⟶ G),
    Set.range p.left ⊆ U → Set.range q.left ⊆ U →
      Set.range (p * q⁻¹).left ⊆ U

/-- An open set stable under division on all field-valued points is closed.
There is no finite-type hypothesis on the ambient group. -/
theorem isClosed_of_divisionStable (U : Set G.left) (hU : IsOpen U)
    (hmul : DivisionStable G U) : IsClosed U := by
  by_cases hne : U.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isClosed_empty
  let E : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let e := (1 : E ⟶ G).left (IsLocalRing.closedPoint k)
  have heval : ∀ (K : Type u) [Field K]
      (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
      (t : Spec (CommRingCat.of K)), (1 : Over.mk b ⟶ G).left t = e := by
    intro K _ b t
    let a : Over.mk b ⟶ E := Over.homMk b (by simp [E])
    have ha := MonObj.comp_one (M := G) a
    calc
      _ = (1 : E ⟶ G).left (b t) :=
        (congrArg (fun f : Over.mk b ⟶ G => f.left t) ha).symm
      _ = e := by
        have ht : b t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
        exact congrArg (1 : E ⟶ G).left ht
  have he : e ∈ U := by
    obtain ⟨x, hx⟩ := hne
    let L := G.left.residueField x
    let t : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L
    let a := G.left.fromSpecResidueField x
    let b := a ≫ G.hom
    let p : Over.mk b ⟶ G := Over.homMk a rfl
    have hp : Set.range p.left ⊆ U := by
      rintro _ ⟨z, rfl⟩
      change a z ∈ U
      have haz : a z = x := Scheme.fromSpecResidueField_apply _ _
      rwa [haz]
    have h := hmul L b p p hp hp
    rw [mul_inv_cancel] at h
    rw [← heval L b t]
    exact h ⟨t, rfl⟩
  have hone : ∀ (K : Type u) [Field K]
      (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
      Set.range (1 : Over.mk b ⟶ G).left ⊆ U := by
    intro K _ b z hz
    obtain ⟨t, rfl⟩ := hz
    rw [heval K b t]
    exact he
  rw [← closure_subset_iff_isClosed]
  intro y hy
  let K := G.left.residueField y
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let s : Spec (CommRingCat.of K) ⟶ G.left := G.left.fromSpecResidueField y
  have hspt : s pt = y := Scheme.fromSpecResidueField_apply _ _
  let b := s ≫ G.hom
  let GK := pullback G.hom b
  let fst : GK ⟶ G.left := pullback.fst G.hom b
  let snd : GK ⟶ Spec (CommRingCat.of K) := pullback.snd G.hom b
  have hfst : IsOpenMap fst := fst.isOpenMap
  let UK : Set GK := fst ⁻¹' U
  have hUK : IsOpen UK := hU.preimage fst.continuous
  let s' : Spec (CommRingCat.of K) ⟶ GK := pullback.lift s (𝟙 _) (by simp [b])
  have hs'cl : s' pt ∈ closure UK := by
    apply hfst.preimage_closure_subset_closure_preimage
    change (s' ≫ fst) pt ∈ closure U
    have hs'fst : s' ≫ fst = s := pullback.lift_fst _ _ _
    rw [hs'fst, hspt]
    exact hy
  let XK : Over (Spec (CommRingCat.of k)) := Over.mk (snd ≫ b)
  let fstO : XK ⟶ G := Over.homMk fst (by simp [XK, fst, snd, pullback.condition])
  let sO : XK ⟶ G := Over.homMk (snd ≫ s) (by simp [XK, b])
  let ρ₀ : XK ⟶ G := sO * fstO⁻¹
  let ρ : GK ⟶ GK := pullback.lift ρ₀.left snd (by simp [XK])
  have hρfst : ρ ≫ fst = ρ₀.left := pullback.lift_fst _ _ _
  let s'O : Over.mk b ⟶ XK := Over.homMk s' (by
    change s' ≫ snd ≫ b = b
    rw [← Category.assoc, show s' ≫ snd = 𝟙 _ from pullback.lift_snd _ _ _,
      Category.id_comp])
  have hs'fstO : s'O ≫ fstO = Over.homMk s rfl := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hs'sO : s'O ≫ sO = Over.homMk s rfl := by
    apply Over.OverMorphism.ext
    change s' ≫ snd ≫ s = s
    rw [← Category.assoc, show s' ≫ snd = 𝟙 _ from pullback.lift_snd _ _ _,
      Category.id_comp]
  have hρs' : s' pt ∈ ρ ⁻¹' UK := by
    change (s' ≫ ρ ≫ fst) pt ∈ U
    rw [hρfst]
    have h : s'O ≫ ρ₀ = 1 := by
      simp only [ρ₀, MonObj.comp_mul, GrpObj.comp_inv, hs'fstO, hs'sO, mul_inv_cancel]
    exact hone K b ⟨pt, (congrArg (fun f : Over.mk b ⟶ G => f.left pt) h).symm⟩
  obtain ⟨z, hzU, hzρ⟩ : (UK ∩ ρ ⁻¹' UK).Nonempty := by
    rw [Set.inter_comm]
    exact mem_closure_iff.mp hs'cl _ (hUK.preimage ρ.continuous) hρs'
  let L := GK.residueField z
  let w : Spec (CommRingCat.of L) ⟶ GK := GK.fromSpecResidueField z
  let c := w ≫ snd ≫ b
  let wO : Over.mk c ⟶ XK := Over.homMk w rfl
  let q : Over.mk c ⟶ G := wO ≫ fstO
  let r : Over.mk c ⟶ G := wO ≫ sO
  have hq : Set.range q.left ⊆ U := by
    rintro _ ⟨t, rfl⟩
    change fst (w t) ∈ U
    rw [show w t = z from Scheme.fromSpecResidueField_apply _ _]
    exact hzU
  have hrq : Set.range (r * q⁻¹).left ⊆ U := by
    have h : r * q⁻¹ = wO ≫ ρ₀ := by
      simp only [r, q, ρ₀, MonObj.comp_mul, GrpObj.comp_inv]
    rw [h]
    rintro _ ⟨t, rfl⟩
    change (w ≫ ρ₀.left) t ∈ U
    rw [← hρfst]
    change fst (ρ (w t)) ∈ U
    rw [show w t = z from Scheme.fromSpecResidueField_apply _ _]
    exact hzρ
  have hqinv : Set.range q⁻¹.left ⊆ U := by
    have h := hmul L c 1 q (hone L c) hq
    simpa only [one_mul] using h
  have hr : Set.range r.left ⊆ U := by
    have h := hmul L c (r * q⁻¹) q⁻¹ hrq hqinv
    simpa only [inv_inv, inv_mul_cancel_right] using h
  have hyU := hr ⟨IsLocalRing.closedPoint L, rfl⟩
  change s (snd (w (IsLocalRing.closedPoint L))) ∈ U at hyU
  have hsy : s (snd (w (IsLocalRing.closedPoint L))) = y :=
    Scheme.fromSpecResidueField_apply _ _
  exact hsy ▸ hyU

/-- The clopen subset determined by an open set stable under field-valued division. -/
def clopen (U : Set G.left) (hU : IsOpen U) (hdiv : DivisionStable G U) :
    TopologicalSpace.Clopens G.left :=
  ⟨U, isClosed_of_divisionStable G U hU hdiv, hU⟩

section Homomorphism

variable {G} {H : Over (Spec (CommRingCat.of k))} [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] [IsOpenImmersion f.left]

/-- The image of an open-immersion homomorphism is stable under division on
all field-valued points. -/
theorem divisionStable_range : DivisionStable H (Set.range f.left) := by
  intro K _ b p q hp hq
  let p' := IsOpenImmersion.lift f.left p.left hp
  let q' := IsOpenImmersion.lift f.left q.left hq
  have hp'fac : p' ≫ f.left = p.left := IsOpenImmersion.lift_fac _ _ _
  have hq'fac : q' ≫ f.left = q.left := IsOpenImmersion.lift_fac _ _ _
  let pO : Over.mk b ⟶ G := Over.homMk p' (by
    rw [← Over.w f, ← Category.assoc, hp'fac, Over.w p])
  let qO : Over.mk b ⟶ G := Over.homMk q' (by
    rw [← Over.w f, ← Category.assoc, hq'fac, Over.w q])
  have hpO : pO ≫ f = p := Over.OverMorphism.ext hp'fac
  have hqO : qO ≫ f = q := Over.OverMorphism.ext hq'fac
  have hfac : (pO * qO⁻¹) ≫ f = p * q⁻¹ := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hpO, hqO]
  rintro _ ⟨t, rfl⟩
  refine ⟨(pO * qO⁻¹).left t, ?_⟩
  exact congrArg (fun h : Over.mk b ⟶ H => h.left t) hfac

/-- The image of an open-immersion homomorphism is closed even when the
ambient field group is not locally of finite type. -/
theorem isClosed_range : IsClosed (Set.range f.left) :=
  isClosed_of_divisionStable H _ f.left.isOpenEmbedding.isOpen_range (divisionStable_range f)

/-- The actual clopen image of an open-immersion homomorphism over a field. -/
def clopenRange : TopologicalSpace.Clopens H.left :=
  clopen H (Set.range f.left) f.left.isOpenEmbedding.isOpen_range (divisionStable_range f)

end Homomorphism

end Langlands.GroupScheme.FieldOpenSubgroup
