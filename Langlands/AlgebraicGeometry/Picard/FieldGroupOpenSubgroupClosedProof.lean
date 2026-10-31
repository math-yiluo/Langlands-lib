import Langlands.AlgebraicGeometry.Picard.FieldGroupOpenSubgroupClosedStatement
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Open subsets of group schemes over a field closed under geometric division -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]

/-- An open subset of a group object over a field, locally of finite type, is closed as soon as
its points over every algebraically closed field are closed under `p, q ↦ p * q⁻¹`. -/
theorem isClosed_of_isOpen_of_mul_inv_mem [LocallyOfFiniteType G.hom]
    (U : Set G.left) (hU : IsOpen U)
    (hmul : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (p q : Over.mk b ⟶ G),
      Set.range p.left ⊆ U → Set.range q.left ⊆ U → Set.range (p * q⁻¹).left ⊆ U) :
    IsClosed U := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  let K := AlgebraicClosure (G.left.residueField y)
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let s : Spec (CommRingCat.of K) ⟶ G.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (G.left.residueField y) K)) ≫
      G.left.fromSpecResidueField y
  have hspt : s pt = y := by
    simp only [s, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  let b := s ≫ G.hom
  -- membership of a geometric point is membership of its unique image point
  have mem_iff : ∀ (p : Over.mk b ⟶ G), Set.range p.left ⊆ U ↔ p.left pt ∈ U := by
    intro p
    constructor
    · intro h; exact h ⟨pt, rfl⟩
    · rintro h _ ⟨w, rfl⟩
      have hw : w = pt := Subsingleton.elim (α := ↥(Spec (CommRingCat.of K))) w pt
      rwa [hw]
  have hmul' : ∀ p q : Over.mk b ⟶ G, p.left pt ∈ U → q.left pt ∈ U →
      (p * q⁻¹).left pt ∈ U := by
    intro p q hp hq
    rw [← mem_iff] at hp hq ⊢
    exact hmul K b p q hp hq
  -- the base change of `G` to `K`
  let GK : Scheme.{u} := pullback G.hom b
  let fst : GK ⟶ G.left := pullback.fst G.hom b
  let snd : GK ⟶ Spec (CommRingCat.of K) := pullback.snd G.hom b
  have hfst : IsOpenMap fst := fst.isOpenMap
  have : JacobsonSpace GK := LocallyOfFiniteType.jacobsonSpace snd
  let UK : Set GK := fst ⁻¹' U
  have hUK : IsOpen UK := hU.preimage fst.continuous
  let s' : Spec (CommRingCat.of K) ⟶ GK := pullback.lift s (𝟙 _) (by simp [b])
  have hs'cl : s' pt ∈ closure UK := by
    apply hfst.preimage_closure_subset_closure_preimage
    change (s' ≫ fst) pt ∈ closure U
    have hs'fst : s' ≫ fst = s := pullback.lift_fst _ _ _
    rw [hs'fst, hspt]
    exact hy
  -- slice objects and the translation map `z ↦ s * z⁻¹`
  let XK : Over (Spec (CommRingCat.of k)) := Over.mk (snd ≫ b)
  let fstO : XK ⟶ G := Over.homMk fst (by simp [XK, fst, snd, pullback.condition])
  let sO : XK ⟶ G := Over.homMk (snd ≫ s) (by simp [XK, b])
  let ρ₀ : XK ⟶ G := sO * fstO⁻¹
  let ρ : GK ⟶ GK := pullback.lift ρ₀.left snd (by simp [XK])
  have hρ : Continuous ρ := ρ.continuous
  -- sections over `K` as slice morphisms
  let secO : ∀ z : Spec (CommRingCat.of K) ⟶ GK, z ≫ snd = 𝟙 _ → (Over.mk b ⟶ XK) :=
    fun z hz ↦ Over.homMk z (by simp [XK, reassoc_of% hz])
  have secO_sO : ∀ z hz, secO z hz ≫ sO = Over.homMk s rfl := by
    intro z hz
    apply Over.OverMorphism.ext
    simp [secO, sO, reassoc_of% hz]
  have secO_fst : ∀ z hz, (secO z hz ≫ fstO).left pt = fst (z pt) := by
    intro z hz
    simp [secO, fstO]
  have secO_ρ : ∀ z hz, (Over.homMk s rfl * (secO z hz ≫ fstO)⁻¹ : Over.mk b ⟶ G).left pt =
      fst (ρ (z pt)) := by
    intro z hz
    rw [← secO_sO z hz, ← GrpObj.comp_inv, ← MonObj.comp_mul]
    change (z ≫ ρ₀.left) pt = (z ≫ ρ ≫ fst) pt
    have hρfst : ρ ≫ fst = ρ₀.left := pullback.lift_fst _ _ _
    rw [hρfst]
  -- closed points of nonempty open subsets of `GK` come from sections over `K`
  have exists_sec : ∀ W : Set GK, IsOpen W → W.Nonempty →
      ∃ (z : Spec (CommRingCat.of K) ⟶ GK) (hz : z ≫ snd = 𝟙 _), z pt ∈ W := by
    intro W hW hne
    obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hne hW.isLocallyClosed
    have hc' : IsClosed {c} := hc
    exact ⟨pointOfClosedPoint snd c hc', pointOfClosedPoint_comp snd c hc',
      by rwa [pointOfClosedPoint_apply snd c hc']⟩
  -- the identity lies in `U`
  obtain ⟨z₀, hz₀, hz₀U⟩ := exists_sec UK hUK
    (by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      simp [UK, h] at hs'cl)
  have hq₀ : (secO z₀ hz₀ ≫ fstO).left pt ∈ U := by rw [secO_fst z₀ hz₀]; exact hz₀U
  have hone : (1 : Over.mk b ⟶ G).left pt ∈ U := by
    have := hmul' _ _ hq₀ hq₀
    rwa [mul_inv_cancel] at this
  -- `ρ (s' pt)` lies in `UK`
  have hs'sec : s' ≫ snd = 𝟙 _ := pullback.lift_snd _ _ _
  have hρs' : s' pt ∈ ρ ⁻¹' UK := by
    change fst (ρ (s' pt)) ∈ U
    rw [← secO_ρ s' hs'sec]
    have : secO s' hs'sec ≫ fstO = Over.homMk s rfl := by
      apply Over.OverMorphism.ext
      exact pullback.lift_fst _ _ _
    rw [this, mul_inv_cancel]
    exact hone
  -- a section in `UK ∩ ρ⁻¹ UK`
  obtain ⟨z, hz, hzU, hzρ⟩ := exists_sec (UK ∩ ρ ⁻¹' UK) (hUK.inter (hUK.preimage hρ))
    (by
      rw [Set.inter_comm]
      exact mem_closure_iff.mp hs'cl _ (hUK.preimage hρ) hρs')
  let q : Over.mk b ⟶ G := secO z hz ≫ fstO
  have hq : q.left pt ∈ U := by rw [secO_fst z hz]; exact hzU
  have hr : (Over.homMk s rfl * q⁻¹ : Over.mk b ⟶ G).left pt ∈ U := by
    rw [secO_ρ z hz]; exact hzρ
  have hqinv : (q⁻¹).left pt ∈ U := by
    have := hmul' 1 q hone hq
    rwa [one_mul] at this
  have hsU := hmul' _ _ hr hqinv
  rw [inv_inv, inv_mul_cancel_right] at hsU
  simpa [hspt] using hsU

/-- The published statement `FieldGroupOpenSubgroupClosedStatement`. -/
theorem fieldGroupOpenSubgroupClosed : FieldGroupOpenSubgroupClosedStatement.{u} :=
  fun _ _ G _ _ U hU hmul => isClosed_of_isOpen_of_mul_inv_mem G U hU hmul

end Langlands.GroupScheme
