import Langlands.Geometry.Analytic.LocalizedDisjointUnion
import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedAction
import Mathlib.CategoryTheory.Action.Basic

/-! # Berkovich's induced analytic spaces `X_{G/H}` -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

open PresentedAffinoidAlgebra.InducedAction (correction correction_coe correction_spec
  correction_one correction_mul)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)
  (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)

/-! ## The copies of `X` indexed by cosets -/

/-- The disjoint union of copies of `X`, one for each coset in `G ⧸ H`. -/
abbrev copies : Cofan fun _ : G ⧸ H => X.V :=
  localizedSigmaCofan fun _ : G ⧸ H => X.V

/-- The disjoint union of the copies is a coproduct. -/
def isColimitCopies : IsColimit (copies H X) :=
  isColimitLocalizedSigmaCofan _

/-- The inclusion of the copy indexed by a coset. -/
abbrev copy (c : G ⧸ H) : X.V ⟶ (copies H X).pt :=
  (copies H X).inj c

theorem copies_hom_ext {Y : LocalizedCategory.{u, max z v, max z v} (K := K)}
    {f f' : (copies H X).pt ⟶ Y} (h : ∀ c, copy H X c ≫ f = copy H X c ≫ f') : f = f' :=
  Cofan.IsColimit.hom_ext (isColimitCopies H X) _ _ h

/-! ## The action of `G` -/

/-- The action of `g ∈ G`: it sends the copy indexed by `c` to the copy indexed by `g • c`,
acting there by the correction `κ(g, c) = (g • c).out⁻¹ * (g * c.out) ∈ H`. -/
def actionMap (g : G) : (copies H X).pt ⟶ (copies H X).pt :=
  Cofan.IsColimit.desc (isColimitCopies H X) fun c =>
    X.ρ (correction H g c) ≫ copy H X (g • c)

@[reassoc (attr := simp)]
theorem copy_actionMap (g : G) (c : G ⧸ H) :
    copy H X c ≫ actionMap H X g = X.ρ (correction H g c) ≫ copy H X (g • c) :=
  Cofan.IsColimit.fac _ _ c

omit [IsUltrametricDist K] [CompleteSpace K] in
@[reassoc]
theorem ρ_comp {M : Type*} [Monoid M] {V : Type*} [Category V] (A : Action V M) (a b : M) :
    A.ρ a ≫ A.ρ b = A.ρ (b * a) := by
  rw [map_mul, End.mul_def]

theorem actionMap_one : actionMap H X 1 = 𝟙 _ :=
  copies_hom_ext H X fun c => by
    rw [copy_actionMap, correction_one, Action.ρ_one, one_smul, Category.id_comp,
      Category.comp_id]

theorem actionMap_mul (g k : G) :
    actionMap H X (g * k) = actionMap H X k ≫ actionMap H X g :=
  copies_hom_ext H X fun c => by
    rw [copy_actionMap, copy_actionMap_assoc, copy_actionMap, ← Category.assoc, ρ_comp,
      correction_mul, mul_smul]

/-- Berkovich's induced space `X_{G/H}` with its action of `G`. -/
abbrev inducedAction : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G where
  V := (copies H X).pt
  ρ :=
    { toFun := actionMap H X
      map_one' := actionMap_one H X
      map_mul' := actionMap_mul H X }

@[simp]
theorem inducedAction_ρ (g : G) : (inducedAction H X).ρ g = actionMap H X g := rfl

/-! ## The unit `X → X_{G/H}` -/

/-- The coset of `H` itself. -/
abbrev baseCoset : G ⧸ H := ((1 : G) : G ⧸ H)

theorem out_baseCoset_mem : (baseCoset H).out ∈ H := by
  have h : (((baseCoset H).out : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := QuotientGroup.out_eq' _
  rw [QuotientGroup.eq] at h
  simpa using h

/-- The chosen representative of the coset `H`, an element of `H`. -/
def baseRep : H := ⟨(baseCoset H).out, out_baseCoset_mem H⟩

theorem smul_baseCoset (h : H) : (h : G) • baseCoset H = baseCoset H := by
  change ((h * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
  rw [QuotientGroup.eq]
  simp

theorem out_smul_baseCoset (c : G ⧸ H) : c.out • baseCoset H = c := by
  change ((c.out * 1 : G) : G ⧸ H) = c
  rw [mul_one]
  exact QuotientGroup.out_eq' c

theorem correction_baseCoset (h : H) :
    correction H (h : G) (baseCoset H) = (baseRep H)⁻¹ * h * baseRep H := by
  apply Subtype.ext
  rw [correction_coe, smul_baseCoset]
  simp [baseRep, mul_assoc]

theorem correction_out_baseCoset (c : G ⧸ H) :
    correction H c.out (baseCoset H) = baseRep H := by
  apply Subtype.ext
  rw [correction_coe, out_smul_baseCoset]
  simp [baseRep]

/-- The underlying morphism of the unit: `X` is identified with the copy indexed by the coset
`H`, corrected by the chosen representative of that coset. -/
def unitHom : X.V ⟶ (copies H X).pt :=
  X.ρ (baseRep H)⁻¹ ≫ copy H X (baseCoset H)

theorem unitHom_comm (h : H) :
    X.ρ h ≫ unitHom H X = unitHom H X ≫ actionMap H X h := by
  rw [unitHom, Category.assoc, copy_actionMap, correction_baseCoset, smul_baseCoset,
    ← Category.assoc, ← Category.assoc, ρ_comp, ρ_comp]
  congr 2
  group

/-- The unit `X → X_{G/H}`, a morphism of `H`-objects. -/
def unit : X ⟶ (Action.res _ H.subtype).obj (inducedAction H X) where
  hom := unitHom H X
  comm h := unitHom_comm H X h

@[simp]
theorem unit_hom : (unit H X).hom = unitHom H X := rfl

/-! ## The universal property -/

variable {X} {Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G}

/-- The morphism `X_{G/H} → Y` extending a morphism `f : X → Y`: on the copy indexed by `c` it
is `f` followed by the action of the representative `c.out`. -/
def liftHom (f : X.V ⟶ Y.V) : (copies H X).pt ⟶ Y.V :=
  Cofan.IsColimit.desc (isColimitCopies H X) fun c => f ≫ Y.ρ c.out

@[reassoc (attr := simp)]
theorem copy_liftHom (f : X.V ⟶ Y.V) (c : G ⧸ H) :
    copy H X c ≫ liftHom H f = f ≫ Y.ρ c.out :=
  Cofan.IsColimit.fac _ _ c

/-- For an `H`-equivariant `f`, the extension is `G`-equivariant. -/
theorem actionMap_liftHom (f : X.V ⟶ Y.V) (hf : ∀ h : H, X.ρ h ≫ f = f ≫ Y.ρ h) (g : G) :
    actionMap H X g ≫ liftHom H f = liftHom H f ≫ Y.ρ g :=
  copies_hom_ext H X fun c => by
    have hf' : ∀ (h : H) {Z} (k : Y.V ⟶ Z), X.ρ h ≫ f ≫ k = f ≫ Y.ρ h ≫ k := fun h Z k => by
      rw [← Category.assoc, hf, Category.assoc]
    rw [copy_actionMap_assoc, copy_liftHom, copy_liftHom_assoc, hf', ρ_comp, ρ_comp,
      ← correction_spec]

theorem unitHom_liftHom (f : X.V ⟶ Y.V) (hf : ∀ h : H, X.ρ h ≫ f = f ≫ Y.ρ h) :
    unitHom H X ≫ liftHom H f = f := by
  have hf' : ∀ (h : H) {Z} (k : Y.V ⟶ Z), X.ρ h ≫ f ≫ k = f ≫ Y.ρ h ≫ k := fun h Z k => by
    rw [← Category.assoc, hf, Category.assoc]
  have e : (baseCoset H).out * (((baseRep H)⁻¹ : H) : G) = 1 := by
    rw [Subgroup.coe_inv]
    exact mul_inv_cancel _
  rw [unitHom, Category.assoc, copy_liftHom, hf', ρ_comp, e, Action.ρ_one, Category.comp_id]

theorem liftHom_unitHom_comp (f : (copies H X).pt ⟶ Y.V)
    (hf : ∀ g : G, actionMap H X g ≫ f = f ≫ Y.ρ g) :
    liftHom H (unitHom H X ≫ f) = f :=
  copies_hom_ext H X fun c => by
    rw [copy_liftHom, Category.assoc, ← hf, unitHom, Category.assoc, copy_actionMap_assoc,
      correction_out_baseCoset, out_smul_baseCoset, ρ_comp_assoc, mul_inv_cancel,
      Action.ρ_one, Category.id_comp]

/-- The extension of an `H`-morphism to a `G`-morphism out of the induced space. -/
def lift (φ : X ⟶ (Action.res _ H.subtype).obj Y) : inducedAction H X ⟶ Y where
  hom := liftHom H φ.hom
  comm g := actionMap_liftHom H φ.hom φ.comm g

@[simp]
theorem lift_hom (φ : X ⟶ (Action.res _ H.subtype).obj Y) : (lift H φ).hom = liftHom H φ.hom :=
  rfl

theorem unit_comp_lift (φ : X ⟶ (Action.res _ H.subtype).obj Y) :
    unit H X ≫ (Action.res _ H.subtype).map (lift H φ) = φ :=
  Action.hom_ext _ _ (unitHom_liftHom H φ.hom φ.comm)

theorem lift_unit_comp (ψ : inducedAction H X ⟶ Y) :
    lift H (unit H X ≫ (Action.res _ H.subtype).map ψ) = ψ :=
  Action.hom_ext _ _ (liftHom_unitHom_comp H ψ.hom ψ.comm)

/-- Berkovich's universal property of `X_{G/H}`: `G`-morphisms `X_{G/H} → Y` correspond to
`H`-morphisms `X → Y`, by composition with the unit. -/
def homEquiv : (inducedAction H X ⟶ Y) ≃ (X ⟶ (Action.res _ H.subtype).obj Y) where
  toFun ψ := unit H X ≫ (Action.res _ H.subtype).map ψ
  invFun := lift H
  left_inv := lift_unit_comp H
  right_inv := unit_comp_lift H

@[simp]
theorem homEquiv_apply (ψ : inducedAction H X ⟶ Y) :
    homEquiv H ψ = unit H X ≫ (Action.res _ H.subtype).map ψ := rfl

@[simp]
theorem homEquiv_symm_apply (φ : X ⟶ (Action.res _ H.subtype).obj Y) :
    (homEquiv H).symm φ = lift H φ := rfl

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
