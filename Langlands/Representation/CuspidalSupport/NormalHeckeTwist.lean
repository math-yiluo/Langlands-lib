import Langlands.Representation.CuspidalSupport.NormalHeckeGrading
import Langlands.Representation.Category.Twist
import Langlands.Representation.Category.UniverseLiftFunctor
import Langlands.Representation.CompactCoefficient.AmbientProjector

/-!
# Maps out of `ind_H^G ρ`: Frobenius reciprocity and character twists

For an open subgroup `H` of `G` and a smooth representation `ρ` of `H`, maps from
`ind_H^G ρ` to a smooth representation `B` of `G` correspond to `H`-equivariant maps
`ρ → B|_H`, by `T ↦ (w ↦ T(f_w))` (`inducedHomEquiv`). Unlike the published adjunction,
`ρ` keeps its own carrier universe. Composed with the carrier lift, this identifies the maps
from `ind_H^G ρ` to the universe lift of `π` with the maps `ρ → π|_H`
(`inducedLiftHomEquiv`).

For a character `ω` of `G` trivial on `H`, the restrictions of `B ⊗ ω` and `B` to `H`
agree, so Frobenius reciprocity gives a linear bijection
`Φ : Hom(ind ρ, B ⊗ ω) ≃ Hom(ind ρ, B)` with `Φ(φ)(f_w) = φ(f_w)` (`twistHomEquiv`).
On a function supported on the coset `H g₀` the map `Φ(φ)` is `ω(g₀) φ`
(`hom_twistHomEquiv_of_support`); hence for `α` in the piece of degree `a` of a degree `p`
and `p g₀ = a`, `Φ(α ≫ φ) = ω(g₀)⁻¹ (α ≫ Φ(φ))` (`twistHomEquiv_comp`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H) (hH : IsOpen (H : Set G))

section Frobenius

variable (B : SmoothRep.{0, uG, max uG uV} ℂ G)

/-- **Frobenius reciprocity** for `ind_H^G ρ`, `H` open: `T ↦ (w ↦ T(f_w))`, with inverse
`φ ↦ (f ↦ ∑ᶠ_{H x} B(x⁻¹) φ(f x))`. -/
def inducedHomEquiv : (inducedRep H ρ ⟶ B) ≃ₗ[ℂ]
    ρ.representation.IntertwiningMap (B.representation.comp H.subtype) where
  toFun T := (resIntertwining H B.representation (SmoothRep.hom T)).comp
    (unitMap H hH ρ.representation ρ.isSmooth)
  map_add' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  invFun φ := SmoothRep.ofHom (cosetSum H hH B.representation ρ.representation φ)
  left_inv T := by
    refine (congrArg SmoothRep.ofHom ?_).trans (SmoothRep.ofHom_hom T)
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_)
    exact (cosetSum_resIntertwining_comp H hH B.representation ρ.representation
      (SmoothRep.hom T) (unitMap H hH ρ.representation ρ.isSmooth) f).trans
      (congrArg (SmoothRep.hom T) (cosetSum_unitMap H hH ρ.representation ρ.isSmooth f))
  right_inv φ := by
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    exact cosetSum_comp_unitMap H hH B.representation ρ.representation ρ.isSmooth φ v

theorem inducedHomEquiv_apply (T : inducedRep H ρ ⟶ B) (w : ρ) :
    inducedHomEquiv H ρ hH B T w =
      SmoothRep.hom T (unitFunction H hH ρ.representation ρ.isSmooth w) :=
  rfl

variable {H ρ B} in
/-- Maps out of `ind_H^G ρ` agreeing on every `f_w` are equal. -/
theorem induced_hom_ext {T T' : inducedRep H ρ ⟶ B}
    (h : ∀ w, SmoothRep.hom T (unitFunction H hH ρ.representation ρ.isSmooth w) =
      SmoothRep.hom T' (unitFunction H hH ρ.representation ρ.isSmooth w)) : T = T' :=
  (inducedHomEquiv H ρ hH B).injective
    (Representation.IntertwiningMap.ext (LinearMap.ext h))

variable (π : SmoothRep.{0, uG, uV} ℂ G)

/-- Equivariant maps into the restriction of the carrier lift of `π` are the maps into the
restriction of `π`. -/
def liftIntertwiningEquiv :
    ρ.representation.IntertwiningMap
        (((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π).representation.comp
          H.subtype) ≃ₗ[ℂ]
      (ρ ⟶ SmoothRep.restrictSubgroup H π) where
  toFun φ := SmoothRep.ofHom
    { toLinearMap := (ULift.moduleEquiv (R := ℂ)).toLinearMap.comp φ.toLinearMap
      isIntertwining' := fun h => LinearMap.ext fun w => by
        exact congrArg ULift.down (Representation.IntertwiningMap.isIntertwining _ _ φ h w) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ :=
    { toLinearMap := (ULift.moduleEquiv (R := ℂ)).symm.toLinearMap.comp
        (SmoothRep.hom ψ).toLinearMap
      isIntertwining' := fun h => LinearMap.ext fun w => by
        exact congrArg ULift.up
          (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom ψ) h w) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Frobenius reciprocity into the carrier lift: maps `ind_H^G ρ → π` (lifted to the carrier
universe of `ind_H^G ρ`) are the maps `ρ → π|_H`, by `T ↦ (w ↦ T(f_w))`. -/
def inducedLiftHomEquiv :
    (inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) ≃ₗ[ℂ]
      (ρ ⟶ SmoothRep.restrictSubgroup H π) :=
  (inducedHomEquiv H ρ hH _).trans (liftIntertwiningEquiv H ρ π)

theorem hom_inducedLiftHomEquiv_apply
    (T : inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) (w : ρ) :
    SmoothRep.hom (inducedLiftHomEquiv H ρ hH π T) w =
      (SmoothRep.hom T (unitFunction H hH ρ.representation ρ.isSmooth w)).down := by
  simp only [inducedLiftHomEquiv, liftIntertwiningEquiv]
  exact congrArg ULift.down (inducedHomEquiv_apply H ρ hH _ T w)

include hH in
/-- The multiplicity space has the same rank on both sides of Frobenius reciprocity. -/
theorem rank_inducedLiftHom :
    Module.rank ℂ (inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) =
      Cardinal.lift.{uG} (Module.rank ℂ (ρ ⟶ SmoothRep.restrictSubgroup H π)) := by
  have := (inducedLiftHomEquiv H ρ hH π).lift_rank_eq
  rwa [Cardinal.lift_id'.{uV, uG}, Cardinal.lift_umax.{uV, uG}] at this

end Frobenius

section Support

variable {H ρ}

/-- A compactly induced function vanishing off the coset `H g₀` is the translate by `g₀⁻¹`
of the function `f_v`, `v = F(g₀)`. -/
theorem eq_translate_unitFunction {g₀ : G} (F : CompactFunctions H ρ.representation)
    (hF : ∀ x, x * g₀⁻¹ ∉ H → eval H ρ.representation F.1 x = 0) :
    F = compactInduced H ρ.representation g₀⁻¹
      (unitFunction H hH ρ.representation ρ.isSmooth (eval H ρ.representation F.1 g₀)) := by
  refine compactFunctions_ext H _ fun x => ?_
  rw [eval_compactInduced, eval_unitFunction]
  by_cases hx : x * g₀⁻¹ ∈ H
  · rw [dite_eq_left hx, ← eval_mul_left H ρ F ⟨x * g₀⁻¹, hx⟩ g₀, inv_mul_cancel_right]
  · rw [dite_eq_right hx, hF x hx]

/-- A map out of `ind_H^G ρ` on a function vanishing off `H g₀`. -/
theorem hom_of_support {B : SmoothRep.{0, uG, max uG uV} ℂ G} (T : inducedRep H ρ ⟶ B)
    {g₀ : G} (F : CompactFunctions H ρ.representation)
    (hF : ∀ x, x * g₀⁻¹ ∉ H → eval H ρ.representation F.1 x = 0) :
    SmoothRep.hom T F = B.representation g₀⁻¹ (SmoothRep.hom T
      (unitFunction H hH ρ.representation ρ.isSmooth (eval H ρ.representation F.1 g₀))) := by
  rw [show SmoothRep.hom T F = SmoothRep.hom T (compactInduced H ρ.representation g₀⁻¹
      (unitFunction H hH ρ.representation ρ.isSmooth (eval H ρ.representation F.1 g₀))) from
    congrArg _ (eq_translate_unitFunction hH F hF)]
  exact Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom T) g₀⁻¹ _

end Support

section Twist

variable (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G))
variable {H} (hωH : H ≤ ω.ker)
variable (B : SmoothRep.{0, uG, max uG uV} ℂ G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem twist_representation_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (g : G) (v : W) :
    Langlands.twist ω σ g v = (ω g : ℂ) • σ g v :=
  rfl

include hωH in
omit [IsTopologicalGroup G] in
/-- The restriction to `H` of `B ⊗ ω` is that of `B` when `ω` is trivial on `H`. -/
theorem twist_comp_subtype :
    (B.twist ω hω).representation.comp H.subtype = B.representation.comp H.subtype := by
  refine MonoidHom.ext fun h => LinearMap.ext fun v => ?_
  change (ω h : ℂ) • B.representation h v = B.representation h v
  rw [(MonoidHom.mem_ker).mp (hωH h.2), Units.val_one, one_smul]

/-- The twist does not change equivariant maps into the restriction to `H`. -/
def twistRestrictEquiv :
    ρ.representation.IntertwiningMap ((B.twist ω hω).representation.comp H.subtype) ≃ₗ[ℂ]
      ρ.representation.IntertwiningMap (B.representation.comp H.subtype) where
  toFun φ := ⟨φ.toLinearMap, fun h => by
    rw [← twist_comp_subtype ω hω hωH B]
    exact φ.isIntertwining' h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := ⟨φ.toLinearMap, fun h => by
    rw [twist_comp_subtype ω hω hωH B]
    exact φ.isIntertwining' h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The linear bijection `Φ : Hom(ind_H^G ρ, B ⊗ ω) ≃ Hom(ind_H^G ρ, B)` determined by
`Φ(φ)(f_w) = φ(f_w)`, for `ω` trivial on `H`. -/
def twistHomEquiv : (inducedRep H ρ ⟶ B.twist ω hω) ≃ₗ[ℂ] (inducedRep H ρ ⟶ B) :=
  (inducedHomEquiv H ρ hH _).trans
    ((twistRestrictEquiv ρ ω hω hωH B).trans (inducedHomEquiv H ρ hH B).symm)

variable {ρ ω hω B}

theorem hom_twistHomEquiv_unitFunction (φ : inducedRep H ρ ⟶ B.twist ω hω) (w : ρ) :
    SmoothRep.hom (twistHomEquiv ρ hH ω hω hωH B φ)
        (unitFunction H hH ρ.representation ρ.isSmooth w) =
      SmoothRep.hom φ (unitFunction H hH ρ.representation ρ.isSmooth w) := by
  rw [← inducedHomEquiv_apply, twistHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- On a function vanishing off the coset `H g₀`, `Φ(φ)` is `ω(g₀) φ`. -/
theorem hom_twistHomEquiv_of_support (φ : inducedRep H ρ ⟶ B.twist ω hω) {g₀ : G}
    (F : CompactFunctions H ρ.representation)
    (hF : ∀ x, x * g₀⁻¹ ∉ H → eval H ρ.representation F.1 x = 0) :
    SmoothRep.hom (twistHomEquiv ρ hH ω hω hωH B φ) F =
      (ω g₀ : ℂ) • SmoothRep.hom φ F := by
  rw [hom_of_support hH _ F hF, hom_of_support hH φ F hF, hom_twistHomEquiv_unitFunction]
  change _ = (ω g₀ : ℂ) • ((ω g₀⁻¹ : ℂ) • B.representation g₀⁻¹ _)
  rw [smul_smul, map_inv ω g₀, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _),
    one_smul]

variable {ι : Type*} [AddCommGroup ι] {p : G → ι}

/-- **The twist law**: for `α` in the piece of degree `a` and `p g₀ = a`,
`Φ(α ≫ φ) = ω(g₀)⁻¹ • (α ≫ Φ(φ))`. -/
theorem twistHomEquiv_comp (hp : IsDegree H p) {a : ι} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p a) {g₀ : G} (hg₀ : p g₀ = a)
    (φ : inducedRep H ρ ⟶ B.twist ω hω) :
    twistHomEquiv ρ hH ω hω hωH B (α ≫ φ) =
      ((ω g₀ : ℂ)⁻¹) • (α ≫ twistHomEquiv ρ hH ω hω hωH B φ) := by
  refine induced_hom_ext hH fun w => ?_
  have hF : ∀ x, x * g₀⁻¹ ∉ H → eval H ρ.representation
      (SmoothRep.hom α (unitFunction H hH ρ.representation ρ.isSmooth w)).1 x = 0 := by
    intro x hx
    refine congrArg (fun T : Module.End ℂ ρ => T w) (hα x fun hpx => hx ?_)
    rw [← hp.eq_zero_iff, hp.map_mul, hp.map_inv, hpx, hg₀, add_neg_cancel]
  rw [hom_twistHomEquiv_unitFunction]
  change SmoothRep.hom φ (SmoothRep.hom α _) = (ω g₀ : ℂ)⁻¹ •
    SmoothRep.hom (twistHomEquiv ρ hH ω hω hωH B φ) (SmoothRep.hom α _)
  rw [hom_twistHomEquiv_of_support hH hωH φ _ hF, smul_smul,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]

end Twist

end Langlands.CuspidalSupport.NormalHecke
