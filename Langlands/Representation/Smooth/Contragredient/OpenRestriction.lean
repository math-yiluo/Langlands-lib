import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof
import Langlands.Representation.Smooth.Contragredient.Definitions

/-! # Smooth parts and contragredients under open subgroup restriction -/

noncomputable section

namespace Langlands

universe uR uG uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Restriction to an open subgroup commutes with taking the smooth part.
The equivalence retains the original vector. -/
def smoothPartRestrictOpenEquiv (ρ : Representation R G V) (H : OpenSubgroup G) :
    Representation.Equiv ((smoothPart ρ).comp H.toSubgroup.subtype)
      (smoothPart (ρ.comp H.toSubgroup.subtype)) where
  toLinearEquiv :=
    { toFun := fun v => ⟨v.val, (isSmoothVector_restrict_open_iff ρ H v.val).mpr v.property⟩
      invFun := fun v => ⟨v.val, (isSmoothVector_restrict_open_iff ρ H v.val).mp v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := by
    ext v
    rfl

@[simp]
theorem smoothPartRestrictOpenEquiv_coe (ρ : Representation R G V)
    (H : OpenSubgroup G) (v : smoothVectors ρ) :
    (smoothPartRestrictOpenEquiv ρ H v).val = v.val := rfl

@[simp]
theorem smoothPartRestrictOpenEquiv_symm_coe (ρ : Representation R G V)
    (H : OpenSubgroup G) (v : smoothVectors (ρ.comp H.toSubgroup.subtype)) :
    ((smoothPartRestrictOpenEquiv ρ H).symm v).val = v.val := rfl

/-- Restriction to an open subgroup commutes with the smooth contragredient,
by the identity on the full algebraic dual. -/
def smoothContragredientRestrictOpenEquiv (ρ : Representation R G V)
    (H : OpenSubgroup G) :
    Representation.Equiv ((smoothContragredient ρ).comp H.toSubgroup.subtype)
      (smoothContragredient (ρ.comp H.toSubgroup.subtype)) :=
  smoothPartRestrictOpenEquiv ρ.dual H

@[simp]
theorem smoothContragredientRestrictOpenEquiv_apply (ρ : Representation R G V)
    (H : OpenSubgroup G) (ℓ : SmoothDual ρ) (v : V) :
    (smoothContragredientRestrictOpenEquiv ρ H ℓ).val v = ℓ.val v := rfl

@[simp]
theorem smoothContragredientRestrictOpenEquiv_symm_apply (ρ : Representation R G V)
    (H : OpenSubgroup G) (ℓ : SmoothDual (ρ.comp H.toSubgroup.subtype)) (v : V) :
    ((smoothContragredientRestrictOpenEquiv ρ H).symm ℓ).val v = ℓ.val v := rfl

end Langlands
