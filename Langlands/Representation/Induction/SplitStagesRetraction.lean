import Langlands.Representation.Induction.SplitQuotientProof
import Langlands.Representation.Jacquet.Coinvariants

/-! Restricted split retractions and their actual coefficient intersections. -/

noncomputable section

namespace Langlands.Induction

universe uR uG uL uV uW

section RestrictedSplit

variable {G : Type uG} [Group G]
variable {L : Type uL} [Group L]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (P : Subgroup G) (hker : r.ker ≤ P)

/-- The canonical restricted retraction, with section `s.subgroupComap P`. -/
def splitStagesRetraction : P →* P.comap s where
  toFun := splitQuotientRetract r s hrs P hker
  map_one' := Subtype.ext (map_one r)
  map_mul' p q := Subtype.ext (map_mul r (p : G) (q : G))

@[simp] theorem splitStagesRetraction_apply (p : P) :
    (splitStagesRetraction r s hrs P hker p : L) = r (p : G) := rfl

@[simp] theorem splitStagesRetraction_section (l : P.comap s) :
    splitStagesRetraction r s hrs P hker (s.subgroupComap P l) = l :=
  Subtype.ext (hrs l)

@[simp] theorem splitStagesRetraction_ker :
    (splitStagesRetraction r s hrs P hker).ker = r.ker.subgroupOf P := by
  ext p
  change splitStagesRetraction r s hrs P hker p = 1 ↔ r (p : G) = 1
  exact Subtype.ext_iff

variable [TopologicalSpace G] [TopologicalSpace L]

theorem continuous_splitStagesRetraction (hr : Continuous r) :
    Continuous (splitStagesRetraction r s hrs P hker) :=
  (hr.comp continuous_subtype_val).subtype_mk _

theorem continuous_splitStagesSection (hs : Continuous s) :
    Continuous (s.subgroupComap P) :=
  (hs.comp continuous_subtype_val).subtype_mk _

end RestrictedSplit

section Intersection

variable {G : Type uG} [Group G] {L : Type uL} [Group L]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)

local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "HP" => H.subgroupOf P
local notation "I" => Subgroup.comap
  (Subgroup.subtype (MonoidHom.ker (splitStagesRetraction r s hrs P hker)))
  (H.subgroupOf P)
local notation "J" => H.comap r.ker.subtype
local notation "N" => r.ker.comap H.subtype
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "j" => MonoidHom.subgroupComap
  (Subgroup.subtype (MonoidHom.ker (splitStagesRetraction r s hrs P hker)))
  (H.subgroupOf P)

/-- Removing the intermediate subgroup gives the actual ambient kernel. -/
def splitStagesKernelEquiv : (rP).ker ≃* r.ker where
  toFun n := ⟨n.val.val, congrArg Subtype.val n.property⟩
  invFun n := ⟨⟨n.val, hker n.property⟩, Subtype.ext n.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem splitStagesKernelEquiv_apply (n : (rP).ker) :
    (splitStagesKernelEquiv r s hrs P hker n : G) = n.val.val := rfl

/-- Removing the intermediate subgroup gives the actual intersection inside
the ambient kernel, with the same group element in both directions. -/
def splitStagesIntersectionEquiv : I ≃* J where
  toFun i := ⟨splitStagesKernelEquiv r s hrs P hker i.val, i.property⟩
  invFun i := ⟨(splitStagesKernelEquiv r s hrs P hker).symm i.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The same actual intersection viewed as a normal subgroup of the inducing
group, with the intermediate subgroup removed. -/
def splitStagesCoefficientIntersectionEquiv : I ≃* N where
  toFun i := ⟨⟨i.val.val.val, i.property⟩, congrArg Subtype.val i.val.property⟩
  invFun i := ⟨⟨⟨i.val.val, hHP i.val.property⟩,
    Subtype.ext i.property⟩, i.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem splitStagesCoefficientIntersectionEquiv_inclusion (i : I) :
    (splitStagesCoefficientIntersectionEquiv r s hrs P H hker hHP i : H) =
      φ (j i) := rfl

variable {R : Type uR} [CommRing R]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- The nested coefficient quotient and the actual ambient intersection
quotient have identical representatives. -/
def splitStagesCoefficientEquiv (σ : Representation R H V) :
    Representation.Coinvariants ((σ.comp φ).comp j) ≃ₗ[R]
      Jacquet.Coinvariants σ N where
  toLinearMap := Representation.Coinvariants.lift _
    (Jacquet.mk σ N) (fun i => LinearMap.ext fun v =>
      Jacquet.mk_apply_subgroup σ N
        (splitStagesCoefficientIntersectionEquiv r s hrs P H hker hHP i) v)
  invFun := Jacquet.lift σ N (Representation.Coinvariants.mk _)
    (fun i => LinearMap.ext fun v => by
      change Representation.Coinvariants.mk ((σ.comp φ).comp j)
          (((σ.comp φ).comp j)
            ((splitStagesCoefficientIntersectionEquiv r s hrs P H hker hHP).symm i) v) =
        Representation.Coinvariants.mk ((σ.comp φ).comp j) v
      exact Representation.Coinvariants.mk_self_apply _ _ v)
  left_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => rfl
  right_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => rfl

@[simp] theorem splitStagesCoefficientEquiv_mk (σ : Representation R H V) (v : V) :
    splitStagesCoefficientEquiv r s hrs P H hker hHP σ
        (Representation.Coinvariants.mk ((σ.comp φ).comp j) v) =
      Jacquet.mk σ N v := rfl

@[simp] theorem splitStagesCoefficientEquiv_symm_mk (σ : Representation R H V) (v : V) :
    (splitStagesCoefficientEquiv r s hrs P H hker hHP σ).symm (Jacquet.mk σ N v) =
      Representation.Coinvariants.mk ((σ.comp φ).comp j) v := rfl

/-- Restriction of an inducing intertwiner to the actual nested intersection. -/
def splitStagesIntersectionMap
    {σ : Representation R H V} {τ : Representation R H W} (T : σ.IntertwiningMap τ) :
    Representation.IntertwiningMap ((σ.comp φ).comp j) ((τ.comp φ).comp j) where
  toLinearMap := T.toLinearMap
  isIntertwining' i := T.isIntertwining' (φ (j i))

/-- Removing the intermediate subgroup commutes with all coefficient maps. -/
theorem splitStagesCoefficientEquiv_natural
    {σ : Representation R H V} {τ : Representation R H W} (T : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants ((σ.comp φ).comp j)) :
    splitStagesCoefficientEquiv r s hrs P H hker hHP τ
        (Representation.Coinvariants.map _ _
          (splitStagesIntersectionMap r s hrs P H hker hHP T) z) =
      Representation.Coinvariants.map _ _ (Jacquet.restrictMap T N)
        (splitStagesCoefficientEquiv r s hrs P H hker hHP σ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v => rfl

variable (hsH : ∀ l : P.comap s, s (l : L) ∈ H)

/-- The original section over the intermediate quotient takes values in the
actual inducing group. -/
def splitStagesInducingSection : P.comap s →* H where
  toFun l := ⟨s l.val, hsH l⟩
  map_one' := Subtype.ext (map_one s)
  map_mul' l k := Subtype.ext (map_mul s l.val k.val)

/-- The quotient identification retains the actual section action on every
representative. This formula uses the ambient normal-coinvariant action. -/
theorem splitStagesCoefficientEquiv_section_mk
    (σ : Representation R H V) (l : P.comap s) (v : V) :
    splitStagesCoefficientEquiv r s hrs P H hker hHP σ
        (Representation.Coinvariants.mk ((σ.comp φ).comp j)
          (σ ⟨s l.val, hsH l⟩ v)) =
      ((σ.toCoinvariants N).comp (splitStagesInducingSection s P H hsH)) l
        (splitStagesCoefficientEquiv r s hrs P H hker hHP σ
          (Representation.Coinvariants.mk ((σ.comp φ).comp j) v)) := rfl

section Topology

variable [TopologicalSpace G] [TopologicalSpace L]

/-- The actual kernel identification preserves the induced subgroup topology. -/
def splitStagesKernelContinuousEquiv : (rP).ker ≃ₜ* r.ker where
  toMulEquiv := splitStagesKernelEquiv r s hrs P hker
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual radical intersections have the same induced topology. -/
def splitStagesIntersectionContinuousEquiv : I ≃ₜ* J where
  toMulEquiv := splitStagesIntersectionEquiv r s hrs P H hker
  continuous_toFun :=
    ((splitStagesKernelContinuousEquiv r s hrs P hker).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((splitStagesKernelContinuousEquiv r s hrs P hker).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

/-- Switching the order of inclusions also preserves the actual coefficient
intersection topology. -/
def splitStagesCoefficientIntersectionContinuousEquiv : I ≃ₜ* N where
  toMulEquiv := splitStagesCoefficientIntersectionEquiv r s hrs P H hker hHP
  continuous_toFun :=
    ((continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk
      _).subtype_mk _

end Topology
end Intersection

end Langlands.Induction
