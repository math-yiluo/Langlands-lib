import Langlands.Representation.Smooth.FixedVectors.Detection
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Classification.SupercuspidalSupport

noncomputable section

namespace Langlands.SmoothRep

open CategoryTheory

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The central action minus a scalar identity is an actual equivariant
endomorphism. -/
def centralShift (A : SmoothRep.{uR, uG, uV} R G)
    (z : Subgroup.center G) (c : R) : A ⟶ A :=
  ofHom ({
    toLinearMap := A.representation z
    isIntertwining' g := by
      change A.representation (z : G) * A.representation g =
        A.representation g * A.representation (z : G)
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.property g] } -
    c • Representation.IntertwiningMap.id A.representation)

@[simp]
theorem centralShift_apply (A : SmoothRep.{uR, uG, uV} R G)
    (z : Subgroup.center G) (c : R) (v : A) :
    hom (centralShift A z c) v = A.representation z v - c • v := rfl

/-- Central shifts commute with every actual intertwiner. -/
theorem centralShift_natural {A B : SmoothRep.{uR, uG, uV} R G}
    (z : Subgroup.center G) (c : R) (f : A ⟶ B) :
    (hom f).comp (hom (centralShift A z c)) =
      (hom (centralShift B z c)).comp (hom f) := by
  ext v
  change hom f (A.representation z v - c • v) =
    B.representation z (hom f v) - c • hom f v
  rw [map_sub, map_smul, (hom f).isIntertwining]

theorem centralShift_eq_zero_iff (A : SmoothRep.{uR, uG, uV} R G)
    (z : Subgroup.center G) (c : R) :
    hom (centralShift A z c) = 0 ↔ ∀ v : A, A.representation z v = c • v := by
  constructor
  · intro h v
    exact sub_eq_zero.mp (congrArg (fun f => f v) h)
  · intro h
    ext v
    exact sub_eq_zero.mpr (h v)

/-- Generation over a subgroup implies generation over the ambient group. -/
theorem fixedVectors_generate_of_subgroup
    (A : SmoothRep.{uR, uG, uV} R G) (H K : Subgroup G)
    (hgen : ∀ S : Subrepresentation (A.representation.comp H.subtype),
      fixedVectors A.representation K ≤ S.toSubmodule → S = ⊤) :
    ∀ S : Subrepresentation A.representation,
      fixedVectors A.representation K ≤ S.toSubmodule → S = ⊤ := by
  intro S hS
  let T : Subrepresentation (A.representation.comp H.subtype) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _ hv => S.apply_mem_toSubmodule g hv }
  have hT : T = ⊤ := hgen T hS
  apply Subrepresentation.toSubmodule_injective
  exact congrArg (fun U : Subrepresentation (A.representation.comp H.subtype) =>
    U.toSubmodule) hT

variable [IsTopologicalGroup G]

/-- A central shift annihilating an occurring constituent with nonzero fixed
vectors cannot act injectively on the ambient finite fixed-vector space. -/
theorem centralShift_not_injective_fixedVectorsMap
    {A D : SmoothRep.{0, uG, uV} ℂ G}
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)]
    [Nontrivial (fixedVectors D.representation K.toSubgroup)]
    (h : IsSubquotient D A) (z : Subgroup.center G) (c : ℂ)
    (hD : ∀ v : D, D.representation z v = c • v) :
    ¬ Function.Injective
      (fixedVectorsMap (hom (centralShift A z c)) K.toSubgroup) := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  apply not_injective_fixedVectorsMap_of_subquotient_witness K hK i q hi hq
    (centralShift A z c) (centralShift C z c) (centralShift_natural z c i)
  rw [centralShift_natural, (centralShift_eq_zero_iff D z c).mpr hD]
  ext v
  rfl

/-- A nonscalar central action gives all three strict dimension inequalities
needed for the two occurrence dichotomies. Only the fixed-vector space, not
the ambient representation, is finite dimensional. -/
theorem centralShift_fixedVectors_descent
    {A D : SmoothRep.{0, uG, uV} ℂ G}
    (H : Subgroup G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)]
    [Nontrivial (fixedVectors D.representation K.toSubgroup)]
    (hgen : ∀ S : Subrepresentation (A.representation.comp H.subtype),
      fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
    (h : IsSubquotient D A) (z : Subgroup.center G) (c : ℂ)
    (hD : ∀ v : D, D.representation z v = c • v)
    (hA : ¬ ∀ v : A, A.representation z v = c • v) :
    let f := centralShift A z c
    Module.finrank ℂ (fixedVectors (kernel f).representation K.toSubgroup) <
        Module.finrank ℂ (fixedVectors A.representation K.toSubgroup) ∧
      Module.finrank ℂ (fixedVectors (image f).representation K.toSubgroup) <
        Module.finrank ℂ (fixedVectors A.representation K.toSubgroup) ∧
      Module.finrank ℂ (fixedVectors (cokernel f).representation K.toSubgroup) <
        Module.finrank ℂ (fixedVectors A.representation K.toSubgroup) := by
  let f := centralShift A z c
  have hn : fixedVectorsMap (hom f) K.toSubgroup ≠ 0 := by
    intro hf
    exact hA ((centralShift_eq_zero_iff A z c).mp
      (intertwiner_eq_zero_of_fixedVectorsMap_eq_zero K.toSubgroup
        (fixedVectors_generate_of_subgroup A H K.toSubgroup hgen) (hom f) hf))
  exact ⟨finrank_fixedVectors_kernel_lt K.toSubgroup f hn,
    finrank_fixedVectors_image_lt K hK f
      (centralShift_not_injective_fixedVectorsMap K hK h z c hD),
    finrank_fixedVectors_cokernel_lt K hK f hn⟩

end Langlands.SmoothRep
