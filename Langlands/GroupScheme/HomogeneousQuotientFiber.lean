import Langlands.GroupScheme.Dynamic.FlagQuotientFiber
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.SmoothProducts

/-! # The subgroup as the identity fiber of a homogeneous quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotient

open _root_.Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} (G P : GroupScheme S) (i : P ⟶ G)
variable {Q : Over S} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

/-- The actual identity coset of the supplied quotient map. -/
def identityCoset : Over.mk (𝟙 S) ⟶ Q :=
  (1 : Over.mk (𝟙 S) ⟶ G.X) ≫ q

include hfib

/-- Every subgroup point maps to the identity coset. -/
theorem subgroup_comp_eq_identity {T : Over S} (a : T ⟶ P.X) :
    (a ≫ i.hom.hom) ≫ q = toUnit T ≫ identityCoset G q := by
  have he : (1 : T ⟶ G.X) ≫ q = (a ≫ i.hom.hom) ≫ q :=
    (hfib T 1 (a ≫ i.hom.hom)).mpr (by
      simpa only [inv_one, one_mul] using
        (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩))
  rw [← he, identityCoset, ← Category.assoc, MonObj.comp_one]

/-- The canonical map from the actual subgroup into the identity fiber. -/
def subgroupToIdentityFiber :
    P.X ⟶ flagQuotientFiber G q (identityCoset G q) :=
  flagQuotientFiberLift G q (identityCoset G q) i.hom.hom
    (by simpa only [Category.id_comp] using
      subgroup_comp_eq_identity G P i q hfib (𝟙 P.X))

@[reassoc]
theorem subgroupToIdentityFiber_comp :
    subgroupToIdentityFiber G P i q hfib ≫
      flagQuotientFiberι G q (identityCoset G q) = i.hom.hom :=
  flagQuotientFiberLift_ι G q (identityCoset G q) _ _

/-- The exact all-test coset relation identifies the subgroup with the actual
scheme fiber over the identity coset. -/
theorem subgroupToIdentityFiber_isIso [Mono i.hom.hom] :
    IsIso (subgroupToIdentityFiber G P i q hfib) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  constructor
  · intro a b hab
    apply (cancel_mono i.hom.hom).mp
    simpa only [Category.assoc, subgroupToIdentityFiber_comp] using
      congrArg (fun z => z ≫ flagQuotientFiberι G q (identityCoset G q)) hab
  · intro x
    have hx : (1 : T ⟶ G.X) ≫ q =
        (x ≫ flagQuotientFiberι G q (identityCoset G q)) ≫ q := by
      rw [Category.assoc, flagQuotientFiberι_comp, comp_toUnit_assoc,
        identityCoset, ← Category.assoc, MonObj.comp_one]
    obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp
      ((hfib T 1 (x ≫ flagQuotientFiberι G q (identityCoset G q))).mp hx)
    refine ⟨a, ?_⟩
    apply flagQuotientFiber_hom_ext G q (identityCoset G q)
    rw [Category.assoc, subgroupToIdentityFiber_comp]
    simpa only [inv_one, one_mul] using ha

/-- The actual subgroup is isomorphic over the base to the identity fiber. -/
def subgroupIdentityFiberIso [Mono i.hom.hom] :
    P.X ≅ flagQuotientFiber G q (identityCoset G q) := by
  letI := subgroupToIdentityFiber_isIso G P i q hfib
  exact asIso (subgroupToIdentityFiber G P i q hfib)

/-- Smoothness of a supplied quotient map already forces smoothness of its
monic exact-fiber subgroup; no separate subgroup structure theorem is needed. -/
theorem smooth_subgroup_of_smooth_quotient [Mono i.hom.hom] [Smooth q.left] :
    Smooth P.X.hom := by
  have hf : Smooth (flagQuotientFiber G q (identityCoset G q)).hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd q.left (identityCoset G q).left)
    infer_instance
  exact smooth_of_over_iso (subgroupIdentityFiberIso G P i q hfib) hf

omit hfib

/-- A closed subgroup of an affine group over its base is affine over that base. -/
theorem affine_subgroup_of_closed [IsAffineHom G.X.hom]
    (hi : IsClosedSubgroup i) : IsAffineHom P.X.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi
  rw [← Over.w i.hom.hom]
  infer_instance

end Langlands.GroupScheme.HomogeneousQuotient
