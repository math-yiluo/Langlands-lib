import Langlands.AlgebraicGeometry.AlgebraicSpace.OrbitStratumActionRestrictionStatement
import Langlands.AlgebraicGeometry.SchemeLocalDimensionBaseChangeProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

/-!
# Proof that smooth group actions restrict to reduced orbit-dimension strata
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace OrbitStratumActionRestriction

/-! ### Fibre dimension under base change -/

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre of a base change of a morphism locally of finite type has the dimension of the
original fibre: it is the scalar extension of that fibre to a larger residue field. -/
theorem topologicalKrullDim_fiber_of_isPullback
    {P X Y W : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ W} {g : Y ⟶ W}
    [LocallyOfFiniteType f] (h : IsPullback a b f g) (y : Y) :
    topologicalKrullDim (b.fiber y) = topologicalKrullDim (f.fiber (g y)) := by
  let : Algebra (W.residueField (g y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hsq := fiberBaseChangeSquare h y
  have hsurj : Function.Surjective (fiberBaseChangeMap h y) := by
    have : Surjective (Spec.map (g.residueFieldMap y)) := by
      refine ⟨fun w => ?_⟩
      obtain ⟨z⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
      exact ⟨z, Subsingleton.elim (α := PrimeSpectrum (W.residueField (g y))) _ _⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) hsq.flip this).surj
  rw [topologicalKrullDim_eq_iSup_at, topologicalKrullDim_eq_iSup_at, ← hsurj.iSup_comp]
  exact iSup_congr fun z => topologicalKrullDimAt_isPullback_fieldExtension
    (W.residueField (g y)) (Y.residueField y) hsq z

/-! ### The stabilizer scheme and its points -/

variable {S : Scheme.{u}} {G : GroupScheme S} {V Z : Over S}

/-- The stabilizer scheme of `a`, the pullback used in `HasOrbitDimension`. -/
abbrev stab (a : SchemeAction G V) : Over S :=
  Limits.pullback (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))

/-- The projection of the stabilizer scheme to `V`, whose fibres define orbit dimensions. -/
abbrev stabπ (a : SchemeAction G V) : stab a ⟶ V :=
  pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))

/-- The projection of the stabilizer scheme to `G`. -/
def stabG (a : SchemeAction G V) : stab a ⟶ G.X :=
  pullback.fst (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) ≫ fst G.X V

@[reassoc (attr := simp)]
theorem stab_fst_snd (a : SchemeAction G V) :
    pullback.fst (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) ≫ snd G.X V = stabπ a := by
  simpa using pullback.condition (f := lift a.hom (snd G.X V)) (g := lift (𝟙 V) (𝟙 V)) =≫
    snd V V

@[reassoc (attr := simp)]
theorem stab_fst_hom (a : SchemeAction G V) :
    pullback.fst (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) ≫ a.hom = stabπ a := by
  simpa using pullback.condition (f := lift a.hom (snd G.X V)) (g := lift (𝟙 V) (𝟙 V)) =≫
    fst V V

/-- The universal point of the stabilizer fixes the universal point of `V`. -/
theorem act_stab (a : SchemeAction G V) : a.act (stabG a) (stabπ a) = stabπ a := by
  rw [SchemeAction.act, stabG]
  nth_rw 1 [← stab_fst_snd a]
  rw [← comp_lift, lift_fst_snd, Category.comp_id, stab_fst_hom]

/-- A point `(h, v)` with `h.v = v` is a point of the stabilizer scheme. -/
def stabMk (a : SchemeAction G V) {T : Over S} (h : T ⟶ G.X) (v : T ⟶ V)
    (hv : a.act h v = v) : T ⟶ stab a :=
  pullback.lift (lift h v) v (by
    apply CartesianMonoidalCategory.hom_ext
    · simpa [SchemeAction.act] using hv
    · simp)

@[reassoc (attr := simp)]
theorem stabMk_stabπ (a : SchemeAction G V) {T : Over S} (h : T ⟶ G.X) (v : T ⟶ V)
    (hv : a.act h v = v) : stabMk a h v hv ≫ stabπ a = v :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem stabMk_stabG (a : SchemeAction G V) {T : Over S} (h : T ⟶ G.X) (v : T ⟶ V)
    (hv : a.act h v = v) : stabMk a h v hv ≫ stabG a = h := by
  simp only [stabMk, stabG]
  exact (pullback.lift_fst_assoc _ _ _ _).trans (lift_fst _ _)

theorem stab_hom_ext (a : SchemeAction G V) {T : Over S} {x y : T ⟶ stab a}
    (hG : x ≫ stabG a = y ≫ stabG a) (hπ : x ≫ stabπ a = y ≫ stabπ a) : x = y := by
  refine pullback.hom_ext ?_ hπ
  apply CartesianMonoidalCategory.hom_ext
  · simpa [stabG] using hG
  · simpa using hπ

/-! ### Equivariant restriction: the stabilizer is a base change -/

theorem act_comp_of_equivariant (a : SchemeAction G V) (b : SchemeAction G Z) {i : Z ⟶ V}
    (hb : b.hom ≫ i = (G.X ◁ i) ≫ a.hom) {T : Over S} (h : T ⟶ G.X) (z : T ⟶ Z) :
    b.act h z ≫ i = a.act h (z ≫ i) := by
  simp only [SchemeAction.act, Category.assoc, hb, lift_whiskerLeft_assoc]

/-- The stabilizer of an equivariant action maps to the stabilizer of `a`. -/
def stabMap (a : SchemeAction G V) (b : SchemeAction G Z) {i : Z ⟶ V}
    (hb : b.hom ≫ i = (G.X ◁ i) ≫ a.hom) : stab b ⟶ stab a :=
  stabMk a (stabG b) (stabπ b ≫ i) (by rw [← act_comp_of_equivariant a b hb, act_stab])

/-- For a monomorphism `i`, the stabilizer of an equivariant action is the base change along
`i` of the stabilizer of `a`. -/
theorem isPullback_stabMap (a : SchemeAction G V) (b : SchemeAction G Z) {i : Z ⟶ V} [Mono i]
    (hb : b.hom ≫ i = (G.X ◁ i) ≫ a.hom) :
    IsPullback (stabMap a b hb) (stabπ b) (stabπ a) i := by
  refine IsPullback.of_isLimit' ⟨by simp [stabMap]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s => stabMk b (s.fst ≫ stabG a) s.snd ?_) ?_ ?_ ?_
  · rw [← cancel_mono i, act_comp_of_equivariant a b hb, ← s.condition,
      ← SchemeAction.naturality, act_stab]
  · intro s
    apply stab_hom_ext <;> simp [stabMap, s.condition]
  · intro s
    simp
  · intro s m h₁ h₂
    apply stab_hom_ext
    · simpa [stabMap] using congrArg (· ≫ stabG a) h₁
    · simpa using h₂

/-! ### Conjugation: the stabilizer at `g.v` is conjugate to the stabilizer at `v` -/

/-- The conjugation map from the pullback of the stabilizer along `snd : G × V ⟶ V` to the
stabilizer, `(h, v, g) ↦ (g h g⁻¹, g.v)`. -/
def conjMap (a : SchemeAction G V) : Limits.pullback (stabπ a) (snd G.X V) ⟶ stab a :=
  stabMk a ((pullback.snd (stabπ a) (snd G.X V) ≫ fst G.X V) *
      (pullback.fst (stabπ a) (snd G.X V) ≫ stabG a) *
      (pullback.snd (stabπ a) (snd G.X V) ≫ fst G.X V)⁻¹)
    (a.act (pullback.snd (stabπ a) (snd G.X V) ≫ fst G.X V)
      (pullback.snd (stabπ a) (snd G.X V) ≫ snd G.X V)) (by
    have hv : a.act (pullback.fst (stabπ a) (snd G.X V) ≫ stabG a)
        (pullback.snd (stabπ a) (snd G.X V) ≫ snd G.X V) =
        pullback.snd (stabπ a) (snd G.X V) ≫ snd G.X V := by
      rw [← pullback.condition, ← SchemeAction.naturality, act_stab]
    rw [SchemeAction.act_mul, SchemeAction.act_mul, ← SchemeAction.act_mul a _ _ (_ ≫ snd G.X V),
      inv_mul_cancel, SchemeAction.act_one, hv])

/-- The inverse of conjugation on points: a point `h` of the stabilizer at `g.v` and a point
`(g, v)` of `G × V` give the point `(g⁻¹ h g, v)` of the stabilizer at `v`, together with
`(g, v)`. -/
def conjInv (a : SchemeAction G V) {T : Over S} (x : T ⟶ stab a) (p : T ⟶ G.X ⊗ V)
    (hx : x ≫ stabπ a = p ≫ a.hom) : T ⟶ Limits.pullback (stabπ a) (snd G.X V) :=
  pullback.lift (stabMk a ((p ≫ fst G.X V)⁻¹ * (x ≫ stabG a) * (p ≫ fst G.X V))
      (p ≫ snd G.X V) (by
        have e₁ : a.act (p ≫ fst G.X V) (p ≫ snd G.X V) = x ≫ stabπ a := by
          rw [hx, SchemeAction.act, ← comp_lift, lift_fst_snd, Category.comp_id]
        have e₂ : a.act (x ≫ stabG a) (x ≫ stabπ a) = x ≫ stabπ a := by
          rw [← SchemeAction.naturality, act_stab]
        rw [SchemeAction.act_mul, SchemeAction.act_mul, e₁, e₂, ← e₁, ← SchemeAction.act_mul,
          inv_mul_cancel, SchemeAction.act_one]))
    p (stabMk_stabπ _ _ _ _)

@[reassoc (attr := simp)]
theorem conjInv_fst_stabG (a : SchemeAction G V) {T : Over S} (x : T ⟶ stab a)
    (p : T ⟶ G.X ⊗ V) (hx : x ≫ stabπ a = p ≫ a.hom) :
    conjInv a x p hx ≫ pullback.fst (stabπ a) (snd G.X V) ≫ stabG a =
      (p ≫ fst G.X V)⁻¹ * (x ≫ stabG a) * (p ≫ fst G.X V) :=
  (pullback.lift_fst_assoc _ _ _ _).trans (stabMk_stabG _ _ _ _)

@[reassoc (attr := simp)]
theorem conjInv_fst_stabπ (a : SchemeAction G V) {T : Over S} (x : T ⟶ stab a)
    (p : T ⟶ G.X ⊗ V) (hx : x ≫ stabπ a = p ≫ a.hom) :
    conjInv a x p hx ≫ pullback.fst (stabπ a) (snd G.X V) ≫ stabπ a = p ≫ snd G.X V :=
  (pullback.lift_fst_assoc _ _ _ _).trans (stabMk_stabπ _ _ _ _)

@[reassoc (attr := simp)]
theorem conjInv_snd (a : SchemeAction G V) {T : Over S} (x : T ⟶ stab a)
    (p : T ⟶ G.X ⊗ V) (hx : x ≫ stabπ a = p ≫ a.hom) :
    conjInv a x p hx ≫ pullback.snd (stabπ a) (snd G.X V) = p :=
  pullback.lift_snd _ _ _

/-- Conjugation identifies the pullbacks of the stabilizer along `snd` and along the action
map `G × V ⟶ V`. -/
theorem isPullback_conjMap (a : SchemeAction G V) :
    IsPullback (conjMap a) (pullback.snd (stabπ a) (snd G.X V)) (stabπ a) a.hom := by
  refine IsPullback.of_isLimit' ⟨by simp [conjMap, SchemeAction.act]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun c => conjInv a c.fst c.snd c.condition) ?_ ?_ ?_
  · intro c
    have e₁ : a.act (c.snd ≫ fst G.X V) (c.snd ≫ snd G.X V) = c.fst ≫ stabπ a := by
      rw [c.condition, SchemeAction.act, ← comp_lift, lift_fst_snd, Category.comp_id]
    apply stab_hom_ext
    · simp only [conjMap, Category.assoc, stabMk_stabG, MonObj.comp_mul, GrpObj.comp_inv,
        conjInv_snd_assoc, conjInv_fst_stabG]
      group
    · simp only [conjMap, Category.assoc, stabMk_stabπ, SchemeAction.naturality,
        conjInv_snd_assoc, e₁]
  · intro c
    exact conjInv_snd _ _ _ _
  · intro c m h₁ h₂
    have h₂' : m ≫ pullback.snd (stabπ a) (snd G.X V) ≫ fst G.X V = c.snd ≫ fst G.X V := by
      rw [← Category.assoc, h₂]
    have hG := congrArg (· ≫ stabG a) h₁
    simp only [conjMap, Category.assoc, stabMk_stabG, MonObj.comp_mul, GrpObj.comp_inv,
      h₂'] at hG
    apply pullback.hom_ext
    · apply stab_hom_ext
      · simp only [Category.assoc, conjInv_fst_stabG]
        rw [← hG]
        group
      · simp only [Category.assoc, pullback.condition, conjInv_snd_assoc]
        rw [← Category.assoc, h₂]
    · rw [h₂, conjInv_snd]

/-! ### Orbit dimensions -/

/-- The stabilizer scheme is locally of finite type over `V` when `G` is locally of finite
type: it is a base change of `(a, snd) : G × V ⟶ V × V`. -/
theorem locallyOfFiniteType_stabπ (a : SchemeAction G V) [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (stabπ a).left := by
  have : LocallyOfFiniteType (lift a.hom (snd G.X V)).left := by
    have : LocallyOfFiniteType ((lift a.hom (snd G.X V)).left ≫ (snd V V).left) := by
      rw [← Over.comp_left, lift_snd, Over.snd_left]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (snd V V).left
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))).map
      (Over.forget S)) this

/-- `HasOrbitDimension` in terms of the fibres of `stabπ a`. -/
theorem hasOrbitDimension_iff (a : SchemeAction G V) (v : V.left) (d : ℕ) :
    HasOrbitDimension a v d ↔ topologicalKrullDim G.X.left =
      topologicalKrullDim ((stabπ a).left.fiber v) + (d : WithBot ℕ∞) :=
  Iff.rfl

/-- The orbit dimension at `g.v` is the orbit dimension at `v`. -/
theorem hasOrbitDimension_act_iff (a : SchemeAction G V) [LocallyOfFiniteType G.X.hom]
    (q : (G.X ⊗ V).left) (d : ℕ) :
    HasOrbitDimension a (a.hom.left q) d ↔ HasOrbitDimension a ((snd G.X V).left q) d := by
  have : LocallyOfFiniteType ((Over.forget S).map (stabπ a)) := locallyOfFiniteType_stabπ a
  have h₁ := topologicalKrullDim_fiber_of_isPullback
    ((isPullback_conjMap a).map (Over.forget S)) q
  have h₂ := topologicalKrullDim_fiber_of_isPullback
    ((IsPullback.of_hasPullback (stabπ a) (snd G.X V)).map (Over.forget S)) q
  rw [hasOrbitDimension_iff, hasOrbitDimension_iff]
  exact Iff.of_eq (congrArg (topologicalKrullDim G.X.left = · + (d : WithBot ℕ∞))
    (h₁.symm.trans h₂))

/-- For an equivariant monomorphism `i`, the orbit dimension at `z` is the orbit dimension at
`i z`. -/
theorem hasOrbitDimension_iff_of_equivariant (a : SchemeAction G V) (b : SchemeAction G Z)
    {i : Z ⟶ V} [Mono i] [LocallyOfFiniteType G.X.hom]
    (hb : b.hom ≫ i = (G.X ◁ i) ≫ a.hom) (z : Z.left) (d : ℕ) :
    HasOrbitDimension b z d ↔ HasOrbitDimension a (i.left z) d := by
  have : LocallyOfFiniteType ((Over.forget S).map (stabπ a)) := locallyOfFiniteType_stabπ a
  have h := topologicalKrullDim_fiber_of_isPullback
    ((isPullback_stabMap a b hb).map (Over.forget S)) z
  rw [hasOrbitDimension_iff, hasOrbitDimension_iff]
  exact Iff.of_eq (congrArg (topologicalKrullDim G.X.left = · + (d : WithBot ℕ∞)) h)

/-! ### Factoring through an immersion -/

/-- A morphism from a reduced scheme whose image lies in the image of an immersion factors
through the immersion. -/
theorem exists_lift_of_isImmersion {X Y T : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]
    [IsReduced T] (f : T ⟶ Y) (hf : Set.range f ⊆ Set.range i) : ∃ l : T ⟶ X, l ≫ i = f := by
  have hU : Set.range f ⊆ Set.range i.coborderRange.ι := by
    refine hf.trans ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨i.liftCoborder x, by rw [← Scheme.Hom.comp_apply, i.liftCoborder_ι]⟩
  let f' := IsOpenImmersion.lift i.coborderRange.ι f hU
  have hker : i.liftCoborder.ker ≤ f'.ker := by
    refine (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl).trans ?_
    refine (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).2 f' ?_
    rintro _ ⟨t, rfl⟩
    obtain ⟨x, hx⟩ := hf ⟨t, rfl⟩
    refine i.liftCoborder.range_subset_ker_support
      ⟨x, i.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, i.liftCoborder_ι,
      IsOpenImmersion.lift_fac, hx]
  refine ⟨IsClosedImmersion.lift i.liftCoborder f' hker, ?_⟩
  calc _ = IsClosedImmersion.lift i.liftCoborder f' hker ≫ i.liftCoborder ≫
        i.coborderRange.ι := by rw [i.liftCoborder_ι]
    _ = f := by rw [IsClosedImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac]

/-! ### Restricting an action along a monomorphism -/

/-- The unit axiom of `a`, stated with `a.hom`. -/
theorem one_smul_hom (a : SchemeAction G V) : η[G.X] ▷ V ≫ a.hom = (λ_ V).hom := by
  let := a
  exact ModObj.one_smul V

/-- The associativity axiom of `a`, stated with `a.hom`. -/
theorem mul_smul_hom (a : SchemeAction G V) :
    μ[G.X] ▷ V ≫ a.hom = (α_ G.X G.X V).hom ≫ G.X ◁ a.hom ≫ a.hom := by
  let := a
  exact ModObj.mul_smul V

/-- An action on `Z` whose action map is a factorization of `G × Z ⟶ G × V ⟶ V` through a
monomorphism `i : Z ⟶ V`. -/
@[instance_reducible]
def restrictAction (a : SchemeAction G V) (i : Z ⟶ V) [Mono i] (β : G.X ⊗ Z ⟶ Z)
    (hβ : β ≫ i = (G.X ◁ i) ≫ a.hom) : SchemeAction G Z where
  smul := β
  one_smul := by
    change η[G.X] ▷ Z ≫ β = (λ_ Z).hom
    rw [← cancel_mono i, Category.assoc, hβ, ← whisker_exchange_assoc, one_smul_hom,
      leftUnitor_naturality]
  mul_smul := by
    change μ[G.X] ▷ Z ≫ β = (α_ G.X G.X Z).hom ≫ G.X ◁ β ≫ β
    rw [← cancel_mono i]
    simp only [Category.assoc]
    rw [hβ, ← whisker_exchange_assoc, mul_smul_hom,
      ← MonoidalCategory.whiskerLeft_comp_assoc, hβ, MonoidalCategory.whiskerLeft_comp_assoc,
      associator_naturality_right_assoc]

@[simp]
theorem restrictAction_hom (a : SchemeAction G V) (i : Z ⟶ V) [Mono i] (β : G.X ⊗ Z ⟶ Z)
    (hβ : β ≫ i = (G.X ◁ i) ≫ a.hom) : (restrictAction a i β hβ).hom = β :=
  rfl

end OrbitStratumActionRestriction

open OrbitStratumActionRestriction in
/-- Smooth group actions restrict to reduced orbit-dimension strata. -/
theorem orbitStratumActionRestriction : OrbitStratumActionRestrictionStatement.{u} := by
  intro k _ G hG V _ a d Z i hi hZ hrange
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have : Mono i := Over.mono_of_mono_left i
  refine ⟨?_, fun b hb z => (hasOrbitDimension_iff_of_equivariant a b hb z d).2 ?_⟩
  · have hsub : Set.range ((G.X ◁ i) ≫ a.hom).left ⊆ Set.range i.left := by
      rintro _ ⟨q, rfl⟩
      have hq : HasOrbitDimension a ((snd G.X V).left ((G.X ◁ i).left q)) d := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerLeft_snd, Over.comp_left,
          Scheme.Hom.comp_apply]
        exact hrange.subset ⟨_, rfl⟩
      rw [Over.comp_left, Scheme.Hom.comp_apply]
      exact hrange.symm.subset ((hasOrbitDimension_act_iff a _ d).2 hq)
    have : GeometricallyReduced G.X.hom :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth G.X.hom
    have : LocallyOfFiniteType Z.hom := by
      rw [← Over.w i]
      infer_instance
    have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
    have : IsReduced (G.X ⊗ Z).left :=
      inferInstanceAs (IsReduced (Limits.pullback G.X.hom Z.hom))
    obtain ⟨l, hl⟩ := exists_lift_of_isImmersion i.left _ hsub
    let β : G.X ⊗ Z ⟶ Z := Over.homMk l (by
      rw [← Over.w i, ← Category.assoc, hl, Over.w])
    have hβ : β ≫ i = (G.X ◁ i) ≫ a.hom := Over.OverMorphism.ext hl
    exact ⟨restrictAction a i β hβ, hβ⟩
  · exact hrange.subset ⟨z, rfl⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
