import Langlands.AlgebraicGeometry.EtaleLocalSystemDescent
import Langlands.AlgebraicGeometry.FiniteLocallyConstantRepresentableStatement
import Langlands.AlgebraicGeometry.EtaleLocalSystemNormalIsotrivialStatement
import Langlands.AlgebraicGeometry.EtaleLocalSystemIsotrivialSpreadingStatement
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Level structures and isotriviality of étale local systems over normal schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.EtaleLocalSystem

/-! ## Level-`n` frames and the frames presheaf -/

section PartLevel

section Frames

variable (M : Type u) [AddCommGroup M] (n : ℕ)

/-- The subgroup `n M`. -/
abbrev nsmulRange : AddSubgroup M := (nsmulAddMonoidHom n : M →+ M).range

/-- Reduction modulo `n M`. -/
abbrev reduce : M →+ M ⧸ nsmulRange M n := QuotientAddGroup.mk' (nsmulRange M n)

/-- Level-`n` frames of `M`: reductions modulo `n M` of automorphisms of `M`. -/
def Frames : Type u :=
  {φ : M →+ M ⧸ nsmulRange M n // ∃ α : M ≃+ M, φ = (reduce M n).comp α.toAddMonoidHom}

variable {M n}

theorem finite_quotient_nsmulRange [AddGroup.FG M] (hn : 0 < n) :
    Finite (M ⧸ nsmulRange M n) := by
  have : AddGroup.FG (M ⧸ nsmulRange M n) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective (nsmulRange M n))
  have : Module.Finite ℤ (M ⧸ nsmulRange M n) := Module.Finite.iff_addGroup_fg.mpr this
  refine Module.finite_of_fg_torsion _ fun q => ?_
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
  obtain ⟨m, rfl⟩ := QuotientAddGroup.mk'_surjective (nsmulRange M n) q
  change (n : ℤ) • (QuotientAddGroup.mk' (nsmulRange M n) m) = 0
  rw [natCast_zsmul, ← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨m, rfl⟩

instance finite_frames [AddGroup.FG M] [NeZero n] : Finite (Frames M n) := by
  classical
  have := finite_quotient_nsmulRange (M := M) (n := n) (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨G, hG⟩ := AddGroup.exists_of_isAddFG M
  let Λ : Frames M n → (G → M ⧸ nsmulRange M n) := fun φ g => φ.1 g
  refine Finite.of_injective Λ fun φ ψ e => Subtype.ext (AddMonoidHom.ext fun m => ?_)
  have hm : m ∈ AddSubgroup.closure (G : Set M) := hG ▸ AddSubgroup.mem_top m
  induction hm using AddSubgroup.closure_induction with
  | mem x hx => exact congrFun e ⟨x, hx⟩
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]

/-- Automorphisms of `M` act on frames by precomposition. -/
def Frames.comp (φ : Frames M n) (γ : M ≃+ M) : Frames M n :=
  ⟨φ.1.comp γ.toAddMonoidHom, by
    obtain ⟨α, hα⟩ := φ.2
    exact ⟨γ.trans α, by rw [hα]; rfl⟩⟩

@[simp] theorem Frames.comp_val (φ : Frames M n) (γ : M ≃+ M) :
    (φ.comp γ).1 = φ.1.comp γ.toAddMonoidHom := rfl

theorem Frames.comp_comp (φ : Frames M n) (γ δ : M ≃+ M) :
    (φ.comp γ).comp δ = φ.comp (δ.trans γ) := rfl

theorem Frames.comp_refl (φ : Frames M n) : φ.comp (AddEquiv.refl M) = φ := rfl

/-- Two automorphisms with the same frame differ by an automorphism congruent to the identity. -/
theorem congr_of_frames_eq {α β : M ≃+ M}
    (h : (reduce M n).comp α.toAddMonoidHom = (reduce M n).comp β.toAddMonoidHom) (x : M) :
    ∃ y, β.symm (α x) = x + n • y := by
  have hx := congrArg (fun φ => φ x) h
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reduce,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at hx
  obtain ⟨z, hz⟩ := hx
  rw [nsmulAddMonoidHom_apply] at hz
  have h1 : α x = β x + -(n • z) := by rw [hz]; abel
  exact ⟨-(β.symm z), by
    rw [h1, map_add, AddEquiv.symm_apply_apply, map_neg, map_nsmul, smul_neg]⟩

end Frames

section LabelLocal

variable {W : Scheme.{u}} {M : AddCommGrpCat.{u}}

/-- For finitely generated `M`, the label of an automorphism of the constant sheaf is locally
constant as an automorphism-valued function. -/
theorem isLocallyConstant_labelEquiv [AddGroup.FG M] (τ : constant W M ≅ constant W M) :
    IsLocallyConstant (labelEquiv τ) := by
  classical
  obtain ⟨G, hG⟩ := AddGroup.exists_of_isAddFG M
  rw [IsLocallyConstant.iff_exists_open]
  intro w
  refine ⟨⋂ g : G, (fun w' => label τ.hom w' g) ⁻¹' {label τ.hom w g},
    isOpen_iInter_of_finite fun g => (isLocallyConstant_label τ.hom g).isOpen_fiber _,
    Set.mem_iInter.2 fun g => rfl, fun w' hw' => ?_⟩
  apply AddEquiv.ext
  intro m
  have hm : m ∈ AddSubgroup.closure (G : Set M) := hG ▸ AddSubgroup.mem_top m
  induction hm using AddSubgroup.closure_induction with
  | mem x hx => exact Set.mem_iInter.1 hw' ⟨x, hx⟩
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | neg x _ hx => simp only [map_neg, hx]

theorem labelEquiv_trans (τ τ' : constant W M ≅ constant W M) (w : W) :
    labelEquiv (τ ≪≫ τ') w = (labelEquiv τ w).trans (labelEquiv τ' w) := by
  apply AddEquiv.ext
  intro m
  simp only [labelEquiv_apply, Iso.trans_hom, label_comp, AddMonoidHom.comp_apply,
    AddEquiv.trans_apply]

end LabelLocal

section Presheaf

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} {M : AddCommGrpCat.{u}} (n : ℕ)
  {ι : Type u} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  (e : ∀ i, restrict (f i) F ≅ constant (X i) M)

/-- The two projections of `(U ×_S X i) ×_U (U ×_S X j)` composed to `X i` and `X j` agree over
`S`. -/
theorem overlap_condition (U : Over S) (i j : ι) :
    (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
        pullback.snd U.hom (f i)) ≫ f i =
      (pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
        pullback.snd U.hom (f j)) ≫ f j := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
    Category.assoc, Category.assoc, pullback.condition]

/-- The label of the transition from `e i` to `e j` on `(U ×_S X i) ×_U (U ×_S X j)`. -/
noncomputable def overlapLabel (U : Over S) (i j : ι)
    (z : ↥(pullback (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)))) : M ≃+ M :=
  labelEquiv (transition (e i) (e j) _ _ (overlap_condition U i j)) z

/-- Level-`n` frames of `F` over `U`, expressed through the trivializations `e i`: a locally
constant frame on each `U ×_S X i`, related on overlaps by the transitions. -/
def FramesFamily (U : Over S) : Type u :=
  {g : ∀ i, ↥(pullback U.hom (f i)) → Frames M n //
    (∀ i, IsLocallyConstant (g i)) ∧
    ∀ i j (z : ↥(pullback (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)))),
      g j (pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) z) =
        (g i (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) z)).comp
          (overlapLabel e U i j z).symm}

/-- The map `U' ×_S X i ⟶ U ×_S X i` induced by `φ : U' ⟶ U`. -/
noncomputable def pullbackMapOver {U U' : Over S} (φ : U' ⟶ U) (i : ι) :
    pullback U'.hom (f i) ⟶ pullback U.hom (f i) :=
  pullback.lift (pullback.fst U'.hom (f i) ≫ φ.left) (pullback.snd U'.hom (f i))
    (by rw [Category.assoc, Over.w φ, pullback.condition])

theorem pullbackMapOver_fst {U U' : Over S} (φ : U' ⟶ U) (i : ι) :
    pullbackMapOver φ i ≫ pullback.fst U.hom (f i) = pullback.fst U'.hom (f i) ≫ φ.left :=
  pullback.lift_fst _ _ _

theorem pullbackMapOver_snd {U U' : Over S} (φ : U' ⟶ U) (i : ι) :
    pullbackMapOver φ i ≫ pullback.snd U.hom (f i) = pullback.snd U'.hom (f i) :=
  pullback.lift_snd _ _ _

/-- The induced map on overlaps. -/
noncomputable def overlapMap {U U' : Over S} (φ : U' ⟶ U) (i j : ι) :
    pullback (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)) ⟶
      pullback (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) :=
  pullback.map _ _ _ _ (pullbackMapOver φ i) (pullbackMapOver φ j) φ.left
    (pullbackMapOver_fst φ i).symm (pullbackMapOver_fst φ j).symm

theorem overlapMap_fst {U U' : Over S} (φ : U' ⟶ U) (i j : ι) :
    overlapMap (f := f) φ i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullbackMapOver φ i :=
  pullback.lift_fst _ _ _

theorem overlapMap_snd {U U' : Over S} (φ : U' ⟶ U) (i j : ι) :
    overlapMap (f := f) φ i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullbackMapOver φ j :=
  pullback.lift_snd _ _ _

/-- Overlap labels are natural in `U`. -/
theorem overlapLabel_map {U U' : Over S} (φ : U' ⟶ U) (i j : ι)
    (z : ↥(pullback (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)))) :
    overlapLabel e U' i j z = overlapLabel e U i j (overlapMap φ i j z) := by
  have hl : pullback.lift
        (pullback.fst (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)) ≫
          pullback.snd U'.hom (f i))
        (pullback.snd (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)) ≫
          pullback.snd U'.hom (f j)) (overlap_condition U' i j) =
      overlapMap φ i j ≫ pullback.lift
        (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
          pullback.snd U.hom (f i))
        (pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
          pullback.snd U.hom (f j)) (overlap_condition U i j) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, overlapMap_fst,
        Category.assoc, pullbackMapOver_snd]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, overlapMap_snd,
        Category.assoc, pullbackMapOver_snd]
  apply AddEquiv.ext
  intro m
  simp only [overlapLabel, labelEquiv_apply]
  rw [label_transition_eq_lift, hl, Scheme.Hom.comp_apply, ← label_transition_eq_lift]

/-- Restriction of frame families along `φ : U' ⟶ U`. -/
noncomputable def FramesFamily.map {U U' : Over S} (φ : U' ⟶ U) (g : FramesFamily n e U) :
    FramesFamily n e U' :=
  ⟨fun i z => g.1 i (pullbackMapOver φ i z), fun i => (g.2.1 i).comp_continuous
      (pullbackMapOver φ i).continuous, fun i j z => by
    show g.1 j (pullbackMapOver φ j
        (pullback.snd (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)) z)) =
      (g.1 i (pullbackMapOver φ i
        (pullback.fst (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)) z))).comp
          (overlapLabel e U' i j z).symm
    have h1 : pullbackMapOver φ j
        (pullback.snd (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)) z) =
        pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j))
          (overlapMap φ i j z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapMap_snd]
    have h2 : pullbackMapOver φ i
        (pullback.fst (pullback.fst U'.hom (f i)) (pullback.fst U'.hom (f j)) z) =
        pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j))
          (overlapMap φ i j z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapMap_fst]
    rw [h1, h2, g.2.2 i j, overlapLabel_map e φ i j z]⟩

theorem pullbackMapOver_id (U : Over S) (i : ι) :
    pullbackMapOver (f := f) (𝟙 U) i = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [pullbackMapOver_fst, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [pullbackMapOver_snd, Category.id_comp]

theorem pullbackMapOver_comp {U U' U'' : Over S} (φ : U' ⟶ U) (ψ : U'' ⟶ U') (i : ι) :
    pullbackMapOver (f := f) (ψ ≫ φ) i = pullbackMapOver ψ i ≫ pullbackMapOver φ i := by
  apply pullback.hom_ext
  · rw [pullbackMapOver_fst, Category.assoc, pullbackMapOver_fst, ← Category.assoc,
      pullbackMapOver_fst, Over.comp_left, Category.assoc]
  · rw [pullbackMapOver_snd, Category.assoc, pullbackMapOver_snd, pullbackMapOver_snd]

/-- The presheaf of level-`n` frames of `F`, expressed through the trivializations `e i`. -/
noncomputable def framesPresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj U := FramesFamily n e U.unop
  map φ := ↾(FramesFamily.map n e φ.unop)
  map_id U := by
    ext g
    apply Subtype.ext
    funext i z
    change g.1 i (pullbackMapOver (𝟙 U.unop) i z) = g.1 i z
    rw [pullbackMapOver_id]
    rfl
  map_comp φ ψ := by
    ext g
    apply Subtype.ext
    funext i z
    change g.1 i (pullbackMapOver (ψ.unop ≫ φ.unop) i z) =
      g.1 i (pullbackMapOver φ.unop i (pullbackMapOver ψ.unop i z))
    rw [pullbackMapOver_comp, Scheme.Hom.comp_apply]

theorem labelEquiv_transition_comp {X Y W W' : Scheme.{u}} {f₁ : X ⟶ S} {g₁ : Y ⟶ S}
    (ef : restrict f₁ F ≅ constant X M) (eg : restrict g₁ F ≅ constant Y M) (a : W ⟶ X)
    (b : W ⟶ Y) (h : a ≫ f₁ = b ≫ g₁) (k : W' ⟶ W) (w : W') :
    labelEquiv (transition ef eg (k ≫ a) (k ≫ b) (by simp [h])) w =
      labelEquiv (transition ef eg a b h) (k w) := by
  apply AddEquiv.ext
  intro m
  simp only [labelEquiv_apply]
  rw [label_transition_comp]

theorem trans_cond (k : ι) (V : Over (X k)) (i : ι) :
    (pullback.fst (V.hom ≫ f k) (f i) ≫ V.hom) ≫ f k = pullback.snd (V.hom ≫ f k) (f i) ≫ f i := by
  rw [Category.assoc]
  exact pullback.condition

/-- The transition from `e k` to `e i` over `U ×_S X i`, for `U` over `X k`. -/
noncomputable def tlabV (k : ι) (V : Over (X k)) (i : ι)
    (z : ↥(pullback (V.hom ≫ f k) (f i))) : M ≃+ M :=
  labelEquiv (transition (e k) (e i) _ _ (trans_cond k V i)) z

/-- The frame family attached to a locally constant frame over an object over `X k`. -/
noncomputable def familyOfLocallyConstant [AddGroup.FG M] (k : ι) (V : Over (X k))
    (lf : LocallyConstant V.left (Frames M n)) :
    FramesFamily n e ((Over.map (f k)).obj V) :=
  ⟨fun i z => (lf (pullback.fst (V.hom ≫ f k) (f i) z)).comp (tlabV e k V i z).symm,
    fun i => IsLocallyConstant.comp₂ (lf.isLocallyConstant.comp_continuous
        (pullback.fst (V.hom ≫ f k) (f i)).continuous)
      (isLocallyConstant_labelEquiv _) (fun a b => a.comp b.symm),
    fun i j w => by
      set q₁ := pullback.fst (pullback.fst (V.hom ≫ f k) (f i)) (pullback.fst (V.hom ≫ f k) (f j))
      set q₂ := pullback.snd (pullback.fst (V.hom ≫ f k) (f i)) (pullback.fst (V.hom ≫ f k) (f j))
      have hq : q₁ ≫ pullback.fst (V.hom ≫ f k) (f i) = q₂ ≫ pullback.fst (V.hom ≫ f k) (f j) :=
        pullback.condition
      have hpt : pullback.fst (V.hom ≫ f k) (f j) (q₂ w) =
          pullback.fst (V.hom ≫ f k) (f i) (q₁ w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq]
      have ha : (q₁ ≫ (pullback.fst (V.hom ≫ f k) (f i) ≫ V.hom)) ≫ f k =
          (q₁ ≫ pullback.snd (V.hom ≫ f k) (f i)) ≫ f i := by
        rw [Category.assoc, trans_cond, ← Category.assoc]
      have hb : (q₁ ≫ pullback.snd (V.hom ≫ f k) (f i)) ≫ f i =
          (q₂ ≫ pullback.snd (V.hom ≫ f k) (f j)) ≫ f j :=
        overlap_condition ((Over.map (f k)).obj V) i j
      have hc := transition_trans (e k) (e i) (e j) _ _ _ ha hb
      have hlab := congrArg (fun τ => labelEquiv τ w) hc
      simp only [labelEquiv_trans] at hlab
      have e1 : labelEquiv (transition (e k) (e i) _ _ ha) w = tlabV e k V i (q₁ w) :=
        labelEquiv_transition_comp (e k) (e i) _ _ (trans_cond k V i) q₁ w
      have e3 : labelEquiv (transition (e k) (e j) _ _ (ha.trans hb)) w =
          tlabV e k V j (q₂ w) := by
        rw [transition_congr (e k) (e j)
          (show q₁ ≫ (pullback.fst (V.hom ≫ f k) (f i) ≫ V.hom) =
            q₂ ≫ (pullback.fst (V.hom ≫ f k) (f j) ≫ V.hom) by
              rw [← Category.assoc, hq, Category.assoc]) rfl]
        exact labelEquiv_transition_comp (e k) (e j) _ _ (trans_cond k V j) q₂ w
      rw [e1, e3] at hlab
      show (lf (pullback.fst (V.hom ≫ f k) (f j) (q₂ w))).comp (tlabV e k V j (q₂ w)).symm =
        ((lf (pullback.fst (V.hom ≫ f k) (f i) (q₁ w))).comp (tlabV e k V i (q₁ w)).symm).comp
          (overlapLabel e ((Over.map (f k)).obj V) i j w).symm
      rw [hpt, Frames.comp_comp, ← hlab]
      rfl⟩

/-- The diagonal section `V ⟶ V ×_S X k` for an object `V` over `X k`. -/
noncomputable def secPt (k : ι) (V : Over (X k)) : V.left ⟶ pullback (V.hom ≫ f k) (f k) :=
  pullback.lift (𝟙 V.left) V.hom (by simp)

theorem secPt_fst (k : ι) (V : Over (X k)) :
    secPt (f := f) k V ≫ pullback.fst (V.hom ≫ f k) (f k) = 𝟙 V.left :=
  pullback.lift_fst _ _ _

theorem secPt_snd (k : ι) (V : Over (X k)) :
    secPt (f := f) k V ≫ pullback.snd (V.hom ≫ f k) (f k) = V.hom :=
  pullback.lift_snd _ _ _

theorem labelEquiv_refl {W : Scheme.{u}} (w : W) :
    labelEquiv (Iso.refl (constant W M)) w = AddEquiv.refl M := by
  apply AddEquiv.ext
  intro m
  simp only [labelEquiv_apply, Iso.refl_hom, label_id]
  rfl

theorem tlabV_secPt (k : ι) (V : Over (X k)) (v : V.left) :
    tlabV e k V k (secPt k V v) = AddEquiv.refl M := by
  unfold tlabV
  rw [← labelEquiv_transition_comp (e k) (e k) _ _ (trans_cond k V k) (secPt k V) v,
    transition_congr (e k) (e k)
      (show secPt k V ≫ (pullback.fst (V.hom ≫ f k) (f k) ≫ V.hom) = V.hom by
        rw [← Category.assoc, secPt_fst, Category.id_comp]) (secPt_snd k V),
    transition_self, labelEquiv_refl]

/-- Restriction of a frame family to the diagonal section. -/
noncomputable def locallyConstantOfFamily (k : ι) (V : Over (X k))
    (g : FramesFamily n e ((Over.map (f k)).obj V)) : LocallyConstant V.left (Frames M n) :=
  ⟨fun v => g.1 k (secPt k V v), (g.2.1 k).comp_continuous (secPt k V).continuous⟩

theorem locallyConstantOfFamily_familyOfLocallyConstant [AddGroup.FG M] (k : ι) (V : Over (X k))
    (lf : LocallyConstant V.left (Frames M n)) :
    locallyConstantOfFamily n e k V (familyOfLocallyConstant n e k V lf) = lf := by
  ext v
  change (lf (pullback.fst (V.hom ≫ f k) (f k) (secPt k V v))).comp
    (tlabV e k V k (secPt k V v)).symm = lf v
  rw [tlabV_secPt, ← Scheme.Hom.comp_apply, secPt_fst]
  rfl

theorem familyOfLocallyConstant_locallyConstantOfFamily [AddGroup.FG M] (k : ι)
    (V : Over (X k)) (g : FramesFamily n e ((Over.map (f k)).obj V)) :
    familyOfLocallyConstant n e k V (locallyConstantOfFamily n e k V g) = g := by
  apply Subtype.ext
  funext i z
  change (g.1 k (secPt k V (pullback.fst (V.hom ≫ f k) (f i) z))).comp (tlabV e k V i z).symm =
    g.1 i z
  let L : pullback (V.hom ≫ f k) (f i) ⟶
      pullback (pullback.fst (V.hom ≫ f k) (f k)) (pullback.fst (V.hom ≫ f k) (f i)) :=
    pullback.lift (pullback.fst _ _ ≫ secPt k V) (𝟙 _)
      (by rw [Category.assoc, secPt_fst, Category.comp_id, Category.id_comp])
  have hc := g.2.2 k i (L z)
  have h1 : pullback.snd (pullback.fst (V.hom ≫ f k) (f k)) (pullback.fst (V.hom ≫ f k) (f i))
      (L z) = z := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    rfl
  have h2 : pullback.fst (pullback.fst (V.hom ≫ f k) (f k)) (pullback.fst (V.hom ≫ f k) (f i))
      (L z) = secPt k V (pullback.fst (V.hom ≫ f k) (f i) z) := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
  have h3 : overlapLabel e ((Over.map (f k)).obj V) k i (L z) = tlabV e k V i z := by
    unfold overlapLabel tlabV
    rw [← labelEquiv_transition_comp (e k) (e i) _ _
      (overlap_condition ((Over.map (f k)).obj V) k i) L z]
    exact congrArg (fun τ => labelEquiv τ z) (transition_congr (e k) (e i)
      (show L ≫ (pullback.fst (pullback.fst (V.hom ≫ f k) (f k))
          (pullback.fst (V.hom ≫ f k) (f i)) ≫ pullback.snd (V.hom ≫ f k) (f k)) =
          pullback.fst (V.hom ≫ f k) (f i) ≫ V.hom by
        rw [← Category.assoc, pullback.lift_fst, Category.assoc, secPt_snd])
      (show L ≫ (pullback.snd (pullback.fst (V.hom ≫ f k) (f k))
          (pullback.fst (V.hom ≫ f k) (f i)) ≫ pullback.snd (V.hom ≫ f k) (f i)) =
          pullback.snd (V.hom ≫ f k) (f i) by
        rw [← Category.assoc, pullback.lift_snd, Category.id_comp]) _)
  have h1' : pullback.snd (pullback.fst ((Over.map (f k)).obj V).hom (f k))
      (pullback.fst ((Over.map (f k)).obj V).hom (f i)) (L z) = z := h1
  have h2' : pullback.fst (pullback.fst ((Over.map (f k)).obj V).hom (f k))
      (pullback.fst ((Over.map (f k)).obj V).hom (f i)) (L z) =
      secPt k V (pullback.fst (V.hom ≫ f k) (f i) z) := h2
  rw [h1', h2', h3] at hc
  exact hc.symm

theorem secPt_pullbackMapOver (k : ι) {V V' : Over (X k)} (ψ : V' ⟶ V) :
    secPt (f := f) k V' ≫ pullbackMapOver (f := f) ((Over.map (f k)).map ψ) k =
      ψ.left ≫ secPt k V := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMapOver_fst, Category.assoc]
    change secPt k V' ≫ pullback.fst (V'.hom ≫ f k) (f k) ≫ ψ.left =
      ψ.left ≫ secPt k V ≫ pullback.fst (V.hom ≫ f k) (f k)
    rw [← Category.assoc, secPt_fst, secPt_fst, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, pullbackMapOver_snd, Category.assoc]
    change secPt k V' ≫ pullback.snd (V'.hom ≫ f k) (f k) =
      ψ.left ≫ secPt k V ≫ pullback.snd (V.hom ≫ f k) (f k)
    rw [secPt_snd, secPt_snd, Over.w ψ]

/-- **Local triviality of the frames presheaf.** Over the member `X k`, the frames presheaf is
the constant presheaf of the set of level-`n` frames: continuous maps to `Frames M n` with the
discrete topology. -/
noncomputable def framesPresheafRestrictIso [AddGroup.FG M] (k : ι) :
    letI : TopologicalSpace (Frames M n) := ⊥
    (Over.map (f k)).op ⋙ framesPresheaf n e ≅
      (Over.forget (X k)).op ⋙ continuousMapPresheaf.{u, u} (Frames M n) :=
  letI : TopologicalSpace (Frames M n) := ⊥
  haveI : DiscreteTopology (Frames M n) := ⟨rfl⟩
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun g => (⟨fun v => g.1 k (secPt k V.unop v),
        ((g.2.1 k).comp_continuous (secPt k V.unop).continuous).continuous⟩ :
          C(V.unop.left, Frames M n))
      invFun := fun (c : C(V.unop.left, Frames M n)) => familyOfLocallyConstant n e k V.unop
        ⟨c, (IsLocallyConstant.iff_continuous c).2 c.continuous⟩
      left_inv := fun g => familyOfLocallyConstant_locallyConstantOfFamily n e k V.unop g
      right_inv := fun (c : C(V.unop.left, Frames M n)) => by
        refine ContinuousMap.ext fun v => ?_
        exact congrArg (fun lf => lf v)
          (locallyConstantOfFamily_familyOfLocallyConstant n e k V.unop
            ⟨c, (IsLocallyConstant.iff_continuous c).2 c.continuous⟩) })
    (fun {V V'} ψ => by
      ext g
      refine ContinuousMap.ext fun v => ?_
      change g.1 k (pullbackMapOver ((Over.map (f k)).map ψ.unop) k (secPt k V'.unop v)) =
        g.1 k (secPt k V.unop (ψ.unop.left v))
      rw [← Scheme.Hom.comp_apply, secPt_pullbackMapOver, Scheme.Hom.comp_apply])

end Presheaf

end PartLevel

/-! ## The frames presheaf is an étale sheaf -/

section PartFramesSheaf

variable {S : Scheme.{u}}

/-- Every point of `U` lifts along some arrow of an étale covering sieve of `U`. -/
theorem exists_mem_sieve_apply_eq {U : Over S} {R : Sieve U}
    (hR : R ∈ (Scheme.etaleTopology.over S) U) (u : U.left) :
    ∃ (W : Over S) (h : W ⟶ U), R h ∧ ∃ w : W.left, h.left w = u := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨𝒱, h𝒱⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  obtain ⟨a, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒱.mem₀).1 u
  have ha := h𝒱 _ _ (Presieve.ofArrows.mk a)
  rw [Sieve.overEquiv_iff] at ha
  exact ⟨_, _, ha, v, hv⟩

section Sheaf

variable {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} {M : AddCommGrpCat.{u}} (n : ℕ)
  {ι : Type u} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  (e : ∀ i, restrict (f i) F ≅ constant (X i) M)

/-- Every point of the overlap over `U` that lies over the image of `h : W ⟶ U` comes from the
overlap over `W`. -/
theorem exists_overlapMap_eq_of_apply_eq {W U : Over S} (h : W ⟶ U) (i j : ι)
    (w : ↥(pullback (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)))) (v : W.left)
    (hv : h.left v =
      pullback.fst U.hom (f i) (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) w)) :
    ∃ y : ↥(pullback (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j))),
      overlapMap h i j y = w := by
  have hv' : h.left v = (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
      pullback.fst U.hom (f i)) w := by
    rw [Scheme.Hom.comp_apply]
    exact hv
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback v w hv'
  have hp := pullback.condition (f := h.left)
    (g := pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
      pullback.fst U.hom (f i))
  have hq := pullback.condition (f := pullback.fst U.hom (f i)) (g := pullback.fst U.hom (f j))
  have hW := Over.w h
  obtain ⟨mi, hmi₁, hmi₂⟩ : ∃ mi : pullback h.left
      (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
        pullback.fst U.hom (f i)) ⟶ pullback W.hom (f i),
      mi ≫ pullback.fst W.hom (f i) = pullback.fst _ _ ∧
      mi ≫ pullback.snd W.hom (f i) = pullback.snd _ _ ≫
        pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
          pullback.snd U.hom (f i) := by
    refine ⟨pullback.lift _ _ ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [← hW, reassoc_of% hp]
    simp only [Category.assoc]
    rw [pullback.condition (f := U.hom) (g := f i)]
  obtain ⟨mj, hmj₁, hmj₂⟩ : ∃ mj : pullback h.left
      (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
        pullback.fst U.hom (f i)) ⟶ pullback W.hom (f j),
      mj ≫ pullback.fst W.hom (f j) = pullback.fst _ _ ∧
      mj ≫ pullback.snd W.hom (f j) = pullback.snd _ _ ≫
        pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
          pullback.snd U.hom (f j) := by
    refine ⟨pullback.lift _ _ ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [← hW, reassoc_of% hp]
    simp only [Category.assoc]
    rw [reassoc_of% hq, pullback.condition (f := U.hom) (g := f j)]
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : pullback h.left
      (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ≫
        pullback.fst U.hom (f i)) ⟶
        pullback (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)),
      m ≫ pullback.fst _ _ = mi ∧ m ≫ pullback.snd _ _ = mj :=
    ⟨pullback.lift mi mj (by rw [hmi₁, hmj₁]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hm : m ≫ overlapMap h i j = pullback.snd _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, overlapMap_fst, ← Category.assoc, hm₁]
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackMapOver_fst, ← Category.assoc, hmi₁, hp, Category.assoc]
      · rw [Category.assoc, pullbackMapOver_snd, hmi₂, Category.assoc]
    · rw [Category.assoc, overlapMap_snd, ← Category.assoc, hm₂]
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackMapOver_fst, ← Category.assoc, hmj₁, hp, Category.assoc,
          ← hq]
      · rw [Category.assoc, pullbackMapOver_snd, hmj₂, Category.assoc]
  exact ⟨m t, by rw [← Scheme.Hom.comp_apply, hm, ht]⟩

/-- Continuous maps on `U ×_S X i`, as a presheaf on `Over S`. -/
noncomputable abbrev pullbackContinuousMapPresheaf (T : Type u) [TopologicalSpace T] (i : ι) :
    (Over S)ᵒᵖ ⥤ Type u :=
  (Over.pullback (f i)).op ⋙ (Over.forget (X i)).op ⋙ continuousMapPresheaf.{u, u} T

theorem isSheaf_pullbackContinuousMapPresheaf (T : Type u) [TopologicalSpace T] (i : ι) :
    Presieve.IsSheaf (Scheme.etaleTopology.over S)
      (pullbackContinuousMapPresheaf (f := f) T i) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  apply (Over.pullback (f i)).op_comp_isSheaf_of_isSheaf (Scheme.etaleTopology.over S)
    (Scheme.etaleTopology.over (X i))
  apply (Over.forget (X i)).op_comp_isSheaf_of_isSheaf (Scheme.etaleTopology.over (X i))
    Scheme.etaleTopology
  exact (isSheaf_fpqcTopology_continuousMapPresheaf T).of_le
    (le_trans Scheme.etaleTopology_le_proetaleTopology Scheme.proetaleTopology_le_fpqcTopology)

/-- **The frames presheaf is an étale sheaf.** -/
theorem isSheaf_framesPresheaf :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) (framesPresheaf n e) := by
  let _ : TopologicalSpace (Frames M n) := ⊥
  have : DiscreteTopology (Frames M n) := discreteTopology_bot _
  intro U R hR x hx
  let xi : ∀ i, Presieve.FamilyOfElements
      (pullbackContinuousMapPresheaf (f := f) (Frames M n) i) R.arrows :=
    fun i V h hh => (⟨(x h hh : FramesFamily n e V).1 i,
      ((x h hh : FramesFamily n e V).2.1 i).continuous⟩ : C(↥(pullback V.hom (f i)), Frames M n))
  have hxi : ∀ i, (xi i).Compatible := by
    intro i V₁ V₂ W g₁ g₂ h₁ h₂ hh₁ hh₂ hcomm
    have hc := congrArg (fun g : FramesFamily n e W => g.1 i) (hx g₁ g₂ hh₁ hh₂ hcomm)
    exact ContinuousMap.ext fun z => congrFun hc z
  have hsh := fun i => isSheaf_pullbackContinuousMapPresheaf (f := f) (Frames M n) i R hR
    (xi i) (hxi i)
  obtain ⟨c, hc⟩ : ∃ c : ∀ i, C(↥(pullback U.hom (f i)), Frames M n),
      ∀ i, (xi i).IsAmalgamation (c i) :=
    ⟨fun i => (hsh i).exists.choose, fun i => (hsh i).exists.choose_spec⟩
  have hpt : ∀ i {V : Over S} (h : V ⟶ U) (hh : R h) (z : ↥(pullback V.hom (f i))),
      c i (pullbackMapOver h i z) = (x h hh : FramesFamily n e V).1 i z :=
    fun i V h hh z =>
      congrArg (fun φ : C(↥(pullback V.hom (f i)), Frames M n) => φ z) (hc i h hh)
  have hov : ∀ i j (w : ↥(pullback (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)))),
      c j (pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) w) =
        (c i (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) w)).comp
          (overlapLabel e U i j w).symm := by
    intro i j w
    obtain ⟨W, h, hh, v, hv⟩ := exists_mem_sieve_apply_eq hR (pullback.fst U.hom (f i)
      (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) w))
    obtain ⟨y, rfl⟩ := exists_overlapMap_eq_of_apply_eq h i j w v hv
    have h1 : pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j))
        (overlapMap h i j y) =
        pullbackMapOver h j (pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapMap_snd]
    have h2 : pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j))
        (overlapMap h i j y) =
        pullbackMapOver h i (pullback.fst (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlapMap_fst]
    rw [h1, h2, hpt j h hh, hpt i h hh, ← overlapLabel_map e h i j y]
    exact (x h hh : FramesFamily n e W).2.2 i j y
  refine ⟨(⟨fun i => c i, fun i => (IsLocallyConstant.iff_continuous _).2 (c i).continuous,
    hov⟩ : FramesFamily n e U), ?_, ?_⟩
  · intro V h hh
    apply Subtype.ext
    funext i z
    exact hpt i h hh z
  · intro t' ht'
    apply Subtype.ext
    funext i z
    have hc' : (xi i).IsAmalgamation (⟨(t' : FramesFamily n e U).1 i,
        ((t' : FramesFamily n e U).2.1 i).continuous⟩ : C(↥(pullback U.hom (f i)), Frames M n)) := by
      intro V h hh
      refine ContinuousMap.ext fun z => ?_
      exact congrFun (congrArg (fun g : FramesFamily n e V => g.1 i) (ht' h hh)) z
    exact congrArg (fun φ : C(↥(pullback U.hom (f i)), Frames M n) => φ z)
      ((hsh i).unique hc' (hc i))

end Sheaf

end PartFramesSheaf

/-! ## Level covers from sections of the frames sheaf -/

section PartLevelCover

section Transport

variable {S T : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} {M : AddCommGrpCat.{u}}

/-- A trivialization of `F` along `a ≫ q`, read as a trivialization of `restrict q F` along `a`.
The two restrictions agree definitionally. -/
def toRestrict (q : T ⟶ S) {X : Scheme.{u}} {a : X ⟶ T}
    (ef : restrict (a ≫ q) F ≅ constant X M) : restrict a (restrict q F) ≅ constant X M :=
  ef

theorem transition_toRestrict (q : T ⟶ S) {X Y W : Scheme.{u}} {a' : X ⟶ T} {b' : Y ⟶ T}
    (ef : restrict (a' ≫ q) F ≅ constant X M) (eg : restrict (b' ≫ q) F ≅ constant Y M)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ a' = b ≫ b') :
    transition (toRestrict q ef) (toRestrict q eg) a b h =
      transition ef eg a b (by rw [← Category.assoc, h, Category.assoc]) := by
  ext V : 3
  rfl

theorem transition_congrIso_left {X Y W : Scheme.{u}} {x x' : X ⟶ S} {g : Y ⟶ S}
    (w : x = x') (ef : restrict x' F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ x = b ≫ g) :
    transition (congrIso.{u, u} w F ≪≫ ef) eg a b h =
      transition ef eg a b (by rw [← w]; exact h) := by
  subst w
  rw [congrIso_rfl, Iso.refl_trans]

theorem transition_congrIso_right {X Y W : Scheme.{u}} {x : X ⟶ S} {g g' : Y ⟶ S}
    (w : g = g') (ef : restrict x F ≅ constant X M) (eg : restrict g' F ≅ constant Y M)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ x = b ≫ g) :
    transition ef (congrIso.{u, u} w F ≪≫ eg) a b h =
      transition ef eg a b (by rw [← w]; exact h) := by
  subst w
  rw [congrIso_rfl, Iso.refl_trans]

end Transport

section Cover

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} {M : AddCommGrpCat.{u}} (n : ℕ)
  {ι : Type u} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  (e : ∀ i, restrict (f i) F ≅ constant (X i) M)

/-- An automorphism representing a frame. -/
noncomputable def Frames.rep (r : Frames M n) : M ≃+ M := r.2.choose

theorem Frames.rep_spec (r : Frames M n) :
    r.1 = (reduce M n).comp (Frames.rep n r).toAddMonoidHom :=
  r.2.choose_spec

/-- If two frames are related by `τ`, then the automorphism `α_s ∘ τ ∘ α_r⁻¹` built from their
representatives is congruent to the identity modulo `n`. -/
theorem exists_eq_add_nsmul_of_frames {r s : Frames M n} {τ : M ≃+ M} (h : s = r.comp τ.symm)
    (m : M) : ∃ y, Frames.rep n s (τ ((Frames.rep n r).symm m)) = m + n • y := by
  have key := congrArg (fun φ : Frames M n => φ.1 (τ ((Frames.rep n r).symm m))) h
  simp only [Frames.comp_val, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply] at key
  rw [Frames.rep_spec n s, Frames.rep_spec n r] at key
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply,
    reduce, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at key
  obtain ⟨y, hy⟩ := key
  rw [nsmulAddMonoidHom_apply] at hy
  refine ⟨-y, ?_⟩
  rw [smul_neg, hy]
  abel

/-- The open subscheme of `U ×_S X i` on which the frame `g i` takes the value `r`. -/
def frameLocus {U : Over S} (g : FramesFamily n e U) (i : ι) (r : Frames M n) :
    (pullback U.hom (f i)).Opens :=
  ⟨(g.1 i) ⁻¹' {r}, (g.2.1 i).isOpen_fiber r⟩

/-- The member of the level cover of `U.left` indexed by `i` and the frame value `r`. -/
noncomputable def levelMap {U : Over S} (g : FramesFamily n e U) (i : ι) (r : Frames M n) :
    (frameLocus n e g i r).toScheme ⟶ U.left :=
  (frameLocus n e g i r).ι ≫ pullback.fst U.hom (f i)

theorem levelMap_cond {U : Over S} (g : FramesFamily n e U) (i : ι) (r : Frames M n) :
    levelMap n e g i r ≫ U.hom = ((frameLocus n e g i r).ι ≫ pullback.snd U.hom (f i)) ≫ f i := by
  rw [levelMap, Category.assoc, Category.assoc, pullback.condition]

/-- The trivialization of `F` over the member `(i, r)`: the pullback of `e i`, adjusted by the
representative of `r`. -/
noncomputable def levelTriv {U : Over S} (g : FramesFamily n e U) (i : ι) (r : Frames M n) :
    restrict (levelMap n e g i r) (restrict U.hom F) ≅ constant (frameLocus n e g i r).toScheme M :=
  toRestrict U.hom ((congrIso.{u, u} (levelMap_cond n e g i r) F ≪≫
    fromRestrict (e i) ((frameLocus n e g i r).ι ≫ pullback.snd U.hom (f i))) ≪≫
      constantCongr _ (Frames.rep n r))

/-- The map from the overlap of two members of the level cover to the overlap over `U`. -/
noncomputable def levelLift {U : Over S} (g : FramesFamily n e U) (i j : ι) (r s : Frames M n) :
    pullback (levelMap n e g i r) (levelMap n e g j s) ⟶
      pullback (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) :=
  pullback.lift (pullback.fst _ _ ≫ (frameLocus n e g i r).ι)
    (pullback.snd _ _ ≫ (frameLocus n e g j s).ι)
    (by simpa only [levelMap, Category.assoc] using pullback.condition)

theorem label_levelTriv {U : Over S} (g : FramesFamily n e U) (i j : ι) (r s : Frames M n)
    (w : ↥(pullback (levelMap n e g i r) (levelMap n e g j s))) :
    label (transition (levelTriv n e g i r) (levelTriv n e g j s) (pullback.fst _ _)
        (pullback.snd _ _) pullback.condition).hom w =
      ((Frames.rep n s).toAddMonoidHom.comp
        (overlapLabel e U i j (levelLift n e g i j r s w)).toAddMonoidHom).comp
          (Frames.rep n r).symm.toAddMonoidHom := by
  rw [levelTriv, levelTriv, transition_toRestrict, constantCongr_transition,
    transition_trans_constantCongr, Iso.trans_hom, Iso.trans_hom, label_comp, label_comp,
    Iso.symm_hom, label_constantCongr, label_constantCongr_inv, transition_congrIso_left,
    transition_congrIso_right, transition_fromRestrict]
  congr 2
  have hl := labelEquiv_transition_comp (e i) (e j) _ _ (overlap_condition U i j)
    (levelLift n e g i j r s) w
  rw [transition_congr (e i) (e j)
    (show levelLift n e g i j r s ≫ pullback.fst (pullback.fst U.hom (f i))
        (pullback.fst U.hom (f j)) ≫ pullback.snd U.hom (f i) =
        pullback.fst _ _ ≫ (frameLocus n e g i r).ι ≫ pullback.snd U.hom (f i) by
      rw [levelLift, ← Category.assoc, pullback.lift_fst, Category.assoc])
    (show levelLift n e g i j r s ≫ pullback.snd (pullback.fst U.hom (f i))
        (pullback.fst U.hom (f j)) ≫ pullback.snd U.hom (f j) =
        pullback.snd _ _ ≫ (frameLocus n e g j s).ι ≫ pullback.snd U.hom (f j) by
      rw [levelLift, ← Category.assoc, pullback.lift_snd, Category.assoc])] at hl
  ext m
  exact congrArg (fun φ : M ≃+ M => φ m) hl

theorem levelLift_frames {U : Over S} (g : FramesFamily n e U) (i j : ι) (r s : Frames M n)
    (w : ↥(pullback (levelMap n e g i r) (levelMap n e g j s))) :
    s = r.comp (overlapLabel e U i j (levelLift n e g i j r s w)).symm := by
  have hc := g.2.2 i j (levelLift n e g i j r s w)
  have h1 : g.1 i (pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j))
      (levelLift n e g i j r s w)) = r := by
    rw [← Scheme.Hom.comp_apply, levelLift, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact Subtype.prop (pullback.fst (levelMap n e g i r) (levelMap n e g j s) w)
  have h2 : g.1 j (pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j))
      (levelLift n e g i j r s w)) = s := by
    rw [← Scheme.Hom.comp_apply, levelLift, pullback.lift_snd, Scheme.Hom.comp_apply]
    exact Subtype.prop (pullback.snd (levelMap n e g i r) (levelMap n e g j s) w)
  rw [h1, h2] at hc
  exact hc

/-- **A section of the frames sheaf gives a level-`n` structure.** A frame family over `U` gives
an étale cover of `U.left` with trivializations of `restrict U.hom F` whose transitions are
congruent to the identity modulo `n`. -/
theorem exists_level_cover (hcov : ∀ s : S, ∃ i x, f i x = s) [∀ i, Etale (f i)]
    {U : Over S} (g : FramesFamily n e U) :
    ∃ (κ : Type u) (Z : κ → Scheme.{u}) (z : ∀ k, Z k ⟶ U.left) (_ : ∀ k, Etale (z k))
      (E : ∀ k, restrict (z k) (restrict U.hom F) ≅ constant (Z k) M),
      (∀ t : U.left, ∃ k y, z k y = t) ∧
      ∀ k l (w : ↥(pullback (z k) (z l))) (m : M), ∃ y,
        label (transition (E k) (E l) (pullback.fst _ _) (pullback.snd _ _)
          pullback.condition).hom w m = m + n • y := by
  refine ⟨Σ _ : ι, Frames M n, fun k => (frameLocus n e g k.1 k.2).toScheme,
    fun k => levelMap n e g k.1 k.2, fun k => by unfold levelMap; infer_instance,
    fun k => levelTriv n e g k.1 k.2, ?_, ?_⟩
  · intro t
    obtain ⟨i, x, hx⟩ := hcov (U.hom t)
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback t x hx.symm
    exact ⟨⟨i, g.1 i p⟩, ⟨p, rfl⟩, hp⟩
  · rintro ⟨i, r⟩ ⟨j, s⟩ w m
    obtain ⟨y, hy⟩ := exists_eq_add_nsmul_of_frames n (levelLift_frames n e g i j r s w) m
    exact ⟨y, (congrArg (fun φ : M →+ M => φ m) (label_levelTriv n e g i j r s w)).trans hy⟩

end Cover

end PartLevelCover

/-! ## Isotriviality over irreducible normal schemes -/

section PartIsotrivial

/-- A positive integer killing the torsion of a finitely generated abelian group. -/
theorem exists_pos_nsmul_torsion_eq_zero (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    ∃ N : ℕ, 0 < N ∧ ∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → N • x = 0 := by
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let T : Submodule ℤ M := AddSubgroup.toIntSubmodule (AddCommGroup.torsion M)
  have : Module.Finite ℤ T := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian T)
  have : AddGroup.FG T := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hT : IsAddTorsion T := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk, hkx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨k, hk, Subtype.ext hkx⟩
  have : Finite T := AddCommGroup.finite_of_fg_isAddTorsion T hT
  refine ⟨AddMonoid.exponent T, Nat.pos_of_ne_zero AddMonoid.exponent_ne_zero_of_finite,
    fun x hx => ?_⟩
  have hxT : x ∈ T := isOfFinAddOrder_iff_nsmul_eq_zero.2 hx
  exact congrArg Subtype.val (AddMonoid.exponent_nsmul_eq_zero (⟨x, hxT⟩ : T))

/-- **Local systems over irreducible normal schemes are isotrivial**, assuming the
representability of finite locally constant étale sheaves and the finite-order congruence
detection statement. -/
theorem isotrivial_of_irreducible
    (hFOC : Langlands.FiniteOrderCongruenceDetectionStatement.{u})
    (hRep : FiniteLocallyConstantRepresentableStatement.{u})
    {S : Scheme.{u}} [IrreducibleSpace S]
    (hS : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x))
    {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} (hF : IsFinitelyGeneratedLocallyConstant.{u, u} F) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S), IsFinite p ∧ Etale p ∧ Surjective p ∧
      ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧ Nonempty (restrict p F ≅ constant S' M) := by
  obtain ⟨M, hM, 𝒰, h𝒰⟩ := exists_common_model hF
  have := hM
  let e : ∀ i, restrict (𝒰.f i) F ≅ constant (𝒰.X i) M := fun i => (h𝒰 i).some
  have : ∀ i, Etale (𝒰.f i) := fun i => 𝒰.map_prop i
  have hcov : ∀ s : S, ∃ i x, 𝒰.f i x = s := fun s => by
    obtain ⟨i, x, hx⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 s
    exact ⟨i, x, hx⟩
  obtain ⟨N, hN, hNtors⟩ := exists_pos_nsmul_torsion_eq_zero M
  have hn : 3 ≤ 3 * N := by omega
  have : NeZero (3 * N) := ⟨by omega⟩
  have htors : ∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → (3 * N) • x = 0 := fun x hx => by
    rw [mul_comm, mul_nsmul, hNtors x hx, nsmul_zero]
  -- the frames sheaf is represented by a finite étale scheme
  have hsh : Presheaf.IsSheaf (Scheme.etaleTopology.over S) (framesPresheaf (3 * N) e) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_framesPresheaf (3 * N) e)
  obtain ⟨W, q, hqF, hqE, ⟨rep⟩⟩ := hRep S (framesPresheaf (3 * N) e) hsh
    ⟨𝒰, fun i => ⟨Frames M (3 * N), inferInstance, ⟨framesPresheafRestrictIso (3 * N) e i⟩⟩⟩
  -- `W` is nonempty
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  obtain ⟨i₀, x₀, -⟩ := hcov s₀
  let r₀ : Frames M (3 * N) := ⟨reduce M (3 * N), AddEquiv.refl M, rfl⟩
  let c₀ := familyOfLocallyConstant (3 * N) e i₀ (Over.mk (𝟙 (𝒰.X i₀)))
    (LocallyConstant.const _ r₀)
  let w₀ : W := (rep.homEquiv.symm c₀).left x₀
  -- a connected component of `W`
  obtain ⟨hirr, hopen⟩ :=
    EtaleNormalLocallyIrreducible.isIrreducible_connectedComponent_of_etale q hS w₀
  let W' : W.Opens := ⟨connectedComponent w₀, hopen⟩
  have hW'c : IsClosed (Set.range W'.ι) := by
    rw [Scheme.Opens.range_ι]
    exact isClosed_connectedComponent
  have : IsClosedImmersion W'.ι := IsClosedImmersion.of_isPreimmersion _ hW'c
  have : IrreducibleSpace W'.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty W'.toScheme := ⟨⟨w₀, mem_connectedComponent⟩⟩
  have hsurj : Surjective (W'.ι ≫ q) :=
    ⟨EtaleNormalLocallyIrreducible.surjective_of_isFinite_of_etale (W'.ι ≫ q)⟩
  have hT' := EtaleNormalLocallyIrreducible.stalk_isDomain_isIntegrallyClosed_of_etale
    (W'.ι ≫ q) hS
  -- the universal frame over the component gives a level structure
  let g' : FramesFamily (3 * N) e (Over.mk (W'.ι ≫ q)) :=
    (framesPresheaf (3 * N) e).map (Over.homMk W'.ι rfl : Over.mk (W'.ι ≫ q) ⟶ Over.mk q).op
      (rep.homEquiv (𝟙 (Over.mk q)))
  obtain ⟨κ, Z, z, hz, E, hcovZ, hlev⟩ := exists_level_cover (3 * N) e hcov g'
  have hFs : IsEtaleSheaf (restrict (W'.ι ≫ q) F) := isEtaleSheaf_restrict _ hF.1
  obtain ⟨iso⟩ :=
    nonempty_iso_constant_of_level_of_irreducible hFOC hT' hFs hn htors hcovZ E hlev
  exact ⟨W'.toScheme, W'.ι ≫ q, inferInstance, inferInstance, hsurj, M, hM, ⟨iso⟩⟩

end PartIsotrivial

/-! ## The local-system statement from three prerequisite statements -/

section PartNormalIsotrivialOfHypotheses

/-- The spectrum of a local ring of a normal scheme has integrally closed domain stalks. -/
theorem stalk_isDomain_isIntegrallyClosed_spec_stalk {S : Scheme.{u}}
    (hS : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x))
    (s : S) (x : Spec (S.presheaf.stalk s)) :
    IsDomain ((Spec (S.presheaf.stalk s)).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Spec (S.presheaf.stalk s)).presheaf.stalk x) := by
  obtain ⟨h1, h2⟩ := hS s
  have hx : x.asIdeal.IsPrime := x.isPrime
  have h3 : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) :=
    isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors
  have h4 : IsDomain (Localization.AtPrime x.asIdeal) := inferInstance
  exact EtaleNormalLocallyIrreducible.isDomain_isIntegrallyClosed_of_ringEquiv
    (Spec.stalkIso (S.presheaf.stalk s) x).commRingCatIsoToRingEquiv.symm ⟨h4, h3⟩

/-- **Local systems over normal schemes are locally isotrivial**, assuming the finite-order
congruence detection statement, representability of finite locally constant étale sheaves, and
the spreading out of isotriviality from local rings. -/
theorem etaleLocalSystemNormalIsotrivial_of
    (hFOC : Langlands.FiniteOrderCongruenceDetectionStatement.{u})
    (hRep : FiniteLocallyConstantRepresentableStatement.{u})
    (hSpread : EtaleLocalSystemIsotrivialSpreadingStatement.{u}) :
    EtaleLocalSystemNormalIsotrivialStatement.{u} := by
  intro S hS F hF
  refine ⟨fun s => ?_, fun hirr => isotrivial_of_irreducible hFOC hRep hS hF⟩
  apply hSpread S F hF s
  have : IsDomain (S.presheaf.stalk s) := (hS s).1
  obtain ⟨L, p, hp1, hp2, hp3, M, hM, ⟨e⟩⟩ := isotrivial_of_irreducible hFOC hRep
    (stalk_isDomain_isIntegrallyClosed_spec_stalk hS s)
    (isFinitelyGeneratedLocallyConstant_restrict (S.fromSpecStalk s) hF)
  exact ⟨L, p, hp1, hp2, hp3, M, hM, ⟨e⟩⟩

end PartNormalIsotrivialOfHypotheses

end Langlands.AlgebraicGeometry.EtaleLocalSystem
