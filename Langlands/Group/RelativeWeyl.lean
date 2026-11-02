import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Relative Weyl quotients on actual subgroups

The ambient quotient is `N_G(T) / Z_G(T)`. The subgroup version uses the
actual intersection `N_G(T) ⊓ L` and its centralizer kernel. No root system,
finiteness, or reductive-group assertion is assumed in these constructions.
-/

namespace Langlands.Group.RelativeWeyl

universe u

variable {G : Type u} [Group G]

/-- The actual subgroup normalizer. -/
abbrev normalizer (T : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (T : Set G)

/-- The full centralizer, rather than the torus itself. -/
abbrev centralizer (T : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (T : Set G)

/-- The denominator as a normal subgroup of the actual normalizer. -/
abbrev denominator (T : Subgroup G) : Subgroup (normalizer T) :=
  (centralizer T).subgroupOf (normalizer T)

/-- The actual normalizer modulo the full centralizer. -/
abbrev Weyl (T : Subgroup G) : Type u :=
  (normalizer T) ⧸ denominator T

/-- The normalizer elements which belong to an actual subgroup `L`. -/
abbrev normalizerIn (T L : Subgroup G) : Subgroup G :=
  (normalizer T) ⊓ L

/-- The same centralizer kernel restricted to `N_G(T) ⊓ L`. -/
abbrev denominatorIn (T L : Subgroup G) : Subgroup (normalizerIn T L) :=
  (centralizer T).subgroupOf (normalizerIn T L)

instance denominatorIn_normal (T L : Subgroup G) : (denominatorIn T L).Normal :=
  inferInstanceAs
    (((denominator T).comap
      (Subgroup.inclusion (show normalizerIn T L ≤ (normalizer T) from inf_le_left))).Normal)

/-- The actual subgroup Weyl quotient. If `Z_G(T) ≤ L`, its denominator is the
whole of `Z_G(T)`, viewed inside `N_G(T) ∩ L`. -/
abbrev WeylIn (T L : Subgroup G) : Type u :=
  normalizerIn T L ⧸ denominatorIn T L

/-- The natural homomorphism of actual subgroup Weyl quotients. -/
def inclusion (T L : Subgroup G) : WeylIn T L →* Weyl T :=
  QuotientGroup.quotientMapSubgroupOfOfLe
    (show centralizer T ≤ centralizer T from le_rfl)
    (show normalizerIn T L ≤ (normalizer T) from inf_le_left)

@[simp]
theorem inclusion_mk (T L : Subgroup G) (n : normalizerIn T L) :
    inclusion T L (QuotientGroup.mk n) =
      QuotientGroup.mk
        (Subgroup.inclusion (show normalizerIn T L ≤ (normalizer T) from inf_le_left) n) :=
  rfl

@[simp]
theorem inclusion_eq_one_iff (T L : Subgroup G) (w : WeylIn T L) :
    inclusion T L w = 1 ↔ w = 1 := by
  induction w using Quotient.inductionOn' with
  | h n =>
    change
      (QuotientGroup.mk
        (Subgroup.inclusion (show normalizerIn T L ≤ (normalizer T) from inf_le_left) n) :
          Weyl T) = 1 ↔
        (QuotientGroup.mk n : WeylIn T L) = 1
    rw [QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    rfl

/-- Subgroup Weyl quotients embed in the ambient quotient. -/
theorem inclusion_injective (T L : Subgroup G) :
    Function.Injective (inclusion T L) :=
  (injective_iff_map_eq_one' (inclusion T L)).mpr
    (inclusion_eq_one_iff T L)

/-- Conjugation of the actual torus subgroup descends to the Weyl quotient. -/
def torusAction (T : Subgroup G) : Weyl T →* MulAut T :=
  QuotientGroup.lift (denominator T) T.normalizerMonoidHom
    T.normalizerMonoidHom_ker.symm.le

/-- The quotient by the full centralizer acts faithfully on `T`. -/
theorem torusAction_injective (T : Subgroup G) :
    Function.Injective (torusAction T) :=
  (QuotientGroup.injective_lift_iff (denominator T) T.normalizerMonoidHom
    T.normalizerMonoidHom_ker.symm.le).mpr T.normalizerMonoidHom_ker.symm

@[simp]
theorem torusAction_mk_apply (T : Subgroup G) (n : (normalizer T)) (t : T) :
    (torusAction T (QuotientGroup.mk n) t : G) = n * t * (n : G)⁻¹ :=
  rfl

/-- Identification of the intersection numerator with the actual intrinsic
normalizer in `L`, after applying the inclusion into `G`. -/
theorem intrinsicNormalizer_map (T L : Subgroup G) (hTL : T ≤ L) :
    (Subgroup.normalizer (T.subgroupOf L : Set L)).map L.subtype =
      normalizerIn T L := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTL, Subgroup.subgroupOf_map_subtype]

/-- For a Levi containing the full centralizer, the centralizer denominator
really is contained in its normalizer numerator. -/
theorem centralizer_le_normalizerIn (T L : Subgroup G) (hZL : centralizer T ≤ L) :
    centralizer T ≤ normalizerIn T L :=
  le_inf (Subgroup.centralizer_le_normalizer (T : Set G)) hZL

/-- Conjugation between actual subgroups, with its actual ambient map visible. -/
def conjugationEquiv (g : G) (L L' : Subgroup G)
    (h : L.map (MulAut.conj g : G →* G) = L') : L ≃* L' :=
  ((MulAut.conj g).subgroupMap L).trans (MulEquiv.subgroupCongr h)

@[simp]
theorem conjugationEquiv_apply (g : G) (L L' : Subgroup G)
    (h : L.map (MulAut.conj g : G →* G) = L') (l : L) :
    (conjugationEquiv g L L' h l : G) = g * l * g⁻¹ :=
  rfl

/-- The empty-standard-Levi quotient is trivial when that Levi is `Z_G(T)`. -/
theorem weylIn_centralizer_subsingleton (T : Subgroup G) :
    Subsingleton (WeylIn T (centralizer T)) := by
  apply (QuotientGroup.subsingleton_iff).mpr
  apply top_unique
  intro n _
  exact n.property.2

end Langlands.Group.RelativeWeyl
