import Langlands.Sheaf.Equivariant.TwistedOver
import Langlands.Sheaf.Equivariant.LocalActionDiscretePart
import Langlands.Geometry.Analytic.EtaleSiteTranslation
import Langlands.Geometry.Analytic.LocalActionLifts

/-!
# Étale and quasi-étale `G`-sheaves on analytic spaces

Let `G` act on an analytic space `X`. Translations are cocontinuous for the étale
and the quasi-étale topologies, so both sites have twisted sites, whose sheaves
are Berkovich's `G^d`-sheaves. Lifts of the action to objects give local actions
on the twisted category. With the lifts on distinguished étale objects, locally
discrete étale sheaves are Berkovich's étale `G`-sheaves; with the lifts on
compact quasi-étale objects, discrete quasi-étale sheaves are his quasi-étale
`G`-sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]

section Etale

variable (ρ : G →* Aut X)

/-- Translations of the étale site are cocontinuous. -/
instance etale_isTranslationInvariant :
    IsTranslationInvariant (P := etale (K := K)) (ρ := ρ) (etaleTopology X) where
  isCocontinuous g := EtaleSite.isCocontinuous_translate_functor (ρ g)

/-- The twisted étale site of `X` with the action `ρ`. -/
abbrev twistedEtaleTopology : GrothendieckTopology (TwistedOver (etale (K := K)) ρ) :=
  twistedTopology ρ (etaleTopology X)

end Etale

section QuasiEtale

/-- Translation of the quasi-étale category along an isomorphism `e : X ≅ Y`: the
structure morphism is composed with `e`. -/
def QuasiEtaleSite.translate {Y : LocalizedCategory.{u, v, v} (K := K)} (e : X ≅ Y) :
    QuasiEtaleSite X ≌ QuasiEtaleSite Y :=
  MorphismProperty.Comma.mapRightIso (𝟭 _) (Discrete.natIso fun _ => e)

/-- Translating back a quasi-étale covering gives a quasi-étale covering: the
covering condition only involves the sources of the arrows. -/
theorem QuasiEtaleSite.map_translate_inverse_mem {Y : LocalizedCategory.{u, v, v} (K := K)}
    (e : X ≅ Y) {V : QuasiEtaleSite Y} {R : Presieve V} (hR : R ∈ quasiEtalePrecoverage Y V) :
    R.map (translate e).inverse ∈
      quasiEtalePrecoverage X ((translate e).inverse.obj V) := by
  intro x
  obtain ⟨σ, hσ, hn, hT⟩ := hR x
  refine ⟨σ, hσ, hn, fun T hT' => ?_⟩
  obtain ⟨W, f, i, hf, rfl⟩ := hT T hT'
  exact ⟨(translate e).inverse.obj W, (translate e).inverse.map f, i, Presieve.map_map hf, rfl⟩

variable (ρ : G →* Aut X)

/-- Translations of the quasi-étale site are cocontinuous. -/
instance quasiEtale_isTranslationInvariant :
    IsTranslationInvariant (P := quasiEtale (K := K)) (ρ := ρ) (quasiEtaleTopology X) where
  isCocontinuous g := isCocontinuous_toGrothendieck_of_equivalence
    (QuasiEtaleSite.translate (ρ g)) _ _ fun hR => QuasiEtaleSite.map_translate_inverse_mem _ hR

/-- The twisted quasi-étale site of `X` with the action `ρ`. -/
abbrev twistedQuasiEtaleTopology :
    GrothendieckTopology (TwistedOver (quasiEtale (K := K)) ρ) :=
  twistedTopology ρ (quasiEtaleTopology X)

end QuasiEtale

section Lifts

variable [TopologicalSpace G] {P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))}
variable {ρ : G →* Aut X}

theorem actionLift_inv_mul_hom {U : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}
    (l : ActionLift ρ f) (g h : l.subgroup) :
    (l.action (g * h)⁻¹).hom = (l.action g⁻¹).hom ≫ (l.action h⁻¹).hom := by
  rw [mul_inv_rev, map_mul]
  rfl

/-- The open subgroup of a lift. -/
def liftOpenSubgroup {U : TwistedOver P ρ} (l : ActionLift ρ (TwistedOver.hom U)) :
    OpenSubgroup G :=
  ⟨l.subgroup, l.isOpen_subgroup⟩

/-- The local action of a lift on an object of the twisted category: `h` acts by the
twisted endomorphism with twist `h⁻¹` whose arrow is the action of `h⁻¹`. -/
def liftAction {U : TwistedOver P ρ} (l : ActionLift ρ (TwistedOver.hom U)) :
    ((liftOpenSubgroup l : OpenSubgroup G) : Subgroup G) →* (End U)ᵐᵒᵖ where
  toFun h := MulOpposite.op (homMk ((h : G)⁻¹) (l.action h⁻¹).hom (l.equivariant h⁻¹))
  map_one' := by
    apply MulOpposite.unop_injective
    refine hom_ext ?_ ?_
    · exact inv_one
    · change (l.action 1⁻¹).hom = 𝟙 _
      rw [inv_one, map_one]
      rfl
  map_mul' g h := by
    apply MulOpposite.unop_injective
    refine hom_ext ?_ ?_
    · exact mul_inv_rev (g : G) h
    · exact actionLift_inv_mul_hom l g h

@[simp]
theorem liftAction_twist {U : TwistedOver P ρ} (l : ActionLift ρ (TwistedOver.hom U))
    (h : ((liftOpenSubgroup l : OpenSubgroup G) : Subgroup G)) :
    Hom.twist (liftAction l h).unop = (h : G)⁻¹ :=
  rfl

@[simp]
theorem liftAction_left {U : TwistedOver P ρ} (l : ActionLift ρ (TwistedOver.hom U))
    (h : ((liftOpenSubgroup l : OpenSubgroup G) : Subgroup G)) :
    Hom.left (liftAction l h).unop = (l.action h⁻¹).hom :=
  rfl

/-- The local action of a lift, restricted to an open subgroup, lifts the action on
`X`. -/
theorem isLift_liftAction {U : TwistedOver P ρ} (l : ActionLift ρ (TwistedOver.hom U))
    {H : Subgroup G} (hH : H ≤ l.subgroup) :
    IsLift ((liftAction l).comp (Subgroup.inclusion hH)) :=
  fun _ => rfl

/-- Two lifts agreeing on an open subgroup have the same discrete sections. -/
theorem isDiscreteSection_liftAction_of_agreeOn {A : Type*} [Category A] {FA : A → A → Type*}
    {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ A) {U : TwistedOver P ρ}
    {l l' : ActionLift ρ (TwistedOver.hom U)} {N : Subgroup G} (h : l.AgreeOn l' N)
    {s : ToType (F.obj (op U))} (hs : IsDiscreteSection F (liftAction l) s) :
    IsDiscreteSection F (liftAction l') s := by
  obtain ⟨hN, ha, hb, hab⟩ := h
  refine IsDiscreteSection.of_agree (N := ⟨N, hN⟩) ha hb (fun g hg => ?_) hs
  apply MulOpposite.unop_injective
  refine hom_ext rfl ?_
  change (l.action ⟨g, ha hg⟩⁻¹).hom = (l'.action ⟨g, hb hg⟩⁻¹).hom
  have hg' : g⁻¹ ∈ N := inv_mem hg
  have := hab g⁻¹ hg'
  exact congrArg Iso.hom this

variable (P ρ) in
/-- The local action system of lifts on the objects satisfying `Adm`: an action of
an open subgroup `H` is admissible on `U` when `Adm U` holds and the action is the
restriction to `H` of the local action of a lift. -/
def liftSystem (Adm : P.Over ⊤ X → Prop) : LocalActionSystem (TwistedOver P ρ) G where
  IsAdmissible U H a := Adm U.obj ∧ ∃ (l : ActionLift ρ (TwistedOver.hom U))
    (hH : (H : Subgroup G) ≤ l.subgroup), a = (liftAction l).comp (Subgroup.inclusion hH)

/-- The admissible actions of a lift system are lifts. -/
theorem isLiftSystem_liftSystem (Adm : P.Over ⊤ X → Prop) :
    (liftSystem P ρ Adm).IsLiftSystem := by
  rintro U H a ⟨-, l, hH, rfl⟩
  exact isLift_liftAction l hH

end Lifts

section GSheaves

variable [TopologicalSpace G] (ρ : G →* Aut X)

/-- Lifts of the action to distinguished étale objects. -/
abbrev distinguishedLiftSystem : LocalActionSystem (TwistedOver (etale (K := K)) ρ) G :=
  liftSystem etale ρ fun U => IsDistinguishedEtale U.hom

/-- Lifts of the action to compact quasi-étale objects. -/
abbrev compactLiftSystem : LocalActionSystem (TwistedOver (quasiEtale (K := K)) ρ) G :=
  liftSystem quasiEtale ρ fun U => IsCompactSpace U.left

variable (A : Type*) [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Berkovich's étale `G`-sheaves `T_G(X_ét)`: sheaves on the twisted étale site whose
sections are locally discrete for the lifts on distinguished étale objects. -/
abbrev EtaleGSheaf := (distinguishedLiftSystem ρ).SmoothSheaf A (twistedEtaleTopology ρ)

/-- Berkovich's quasi-étale `G`-sheaves `T_G(X_qét)`: sheaves on the twisted
quasi-étale site whose sections over compact objects are discrete for all lifts. -/
abbrev QuasiEtaleGSheaf :=
  (compactLiftSystem ρ).DiscreteSheaf A (twistedQuasiEtaleTopology ρ)

end GSheaves

end Langlands.Sheaf.Equivariant.Analytic
