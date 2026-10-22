import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace Langlands.Tate.OrdinaryCup

variable {R : Type u} [CommRing R]
variable (S T : ShortComplex (ModuleCat R)) (D : ModuleCat R)
variable (β : S.cycles →ₗ[R] T.cycles →ₗ[R] D)
variable (hleft : ∀ a b, β (S.toCycles a) b = 0)
variable (hright : ∀ a b, β a (T.toCycles b) = 0)

/-- First descend the second variable through the actual homology cokernel. -/
def descRight (a : S.cycles) : T.homology →ₗ[R] D :=
  (T.descHomology (ModuleCat.ofHom (β a)) (by
    ext b
    exact hright a b)).hom

@[simp]
lemma descRight_π (a : S.cycles) (b : T.cycles) :
    descRight S T D β hright a (T.homologyπ b) = β a b := by
  exact ConcreteCategory.congr_hom (T.π_descHomology (ModuleCat.ofHom (β a)) _) b

/-- Descending the second variable is linear in the first variable. -/
def descRightLinear : S.cycles →ₗ[R] T.homology →ₗ[R] D where
  toFun := descRight S T D β hright
  map_add' a a' := by
    ext b
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance b
    simp
  map_smul' r a := by
    ext b
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance b
    simp

@[simp]
lemma descRightLinear_apply (a : S.cycles) (b : T.cycles) :
    descRightLinear S T D β hright a (T.homologyπ b) = β a b :=
  descRight_π S T D β hright a b

/-- A bilinear map on cycles that kills boundaries in each variable descends to
actual homology in both variables. -/
def descBilinear : S.homology →ₗ[R] T.homology →ₗ[R] D :=
  (S.descHomology (ModuleCat.ofHom (descRightLinear S T D β hright)) (by
    ext a b
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance b
    exact (descRight_π S T D β hright (S.toCycles a) b).trans (hleft a b))).hom

@[simp]
lemma descBilinear_π_π (a : S.cycles) (b : T.cycles) :
    descBilinear S T D β hleft hright (S.homologyπ a) (T.homologyπ b) = β a b := by
  have h : descBilinear S T D β hleft hright (S.homologyπ a) =
      descRightLinear S T D β hright a := by
    exact ConcreteCategory.congr_hom
      (S.π_descHomology (ModuleCat.ofHom (descRightLinear S T D β hright)) _) a
  exact congrArg (fun f : T.homology →ₗ[R] D => f (T.homologyπ b)) h |>.trans
    (descRight_π S T D β hright a b)

section Cochains

open groupCohomology

variable {G : Type u} [Group G] (A B C : Rep R G) (p q : ℕ)

lemma cocycle_d (a : cocycles A p) :
    _root_.inhomogeneousCochains.d A p (iCocycles A p a) = 0 := by
  rw [← groupCohomology.inhomogeneousCochains.d_def]
  exact ConcreteCategory.congr_hom
    ((inhomogeneousCochains A).iCycles_d p (p + 1)) a

lemma cocycle_ext {a b : cocycles A p}
    (h : iCocycles A p a = iCocycles A p b) : a = b :=
  (ModuleCat.mono_iff_injective (iCocycles A p)).1 inferInstance h

lemma class_eq_zero_of_boundary (n i : ℕ) (z : cocycles C n)
    (a : (inhomogeneousCochains C).X i)
    (h : iCocycles C n z = (inhomogeneousCochains C).d i n a) :
    π C n z = 0 := by
  have hz : z = toCocycles C i n a := by
    apply cocycle_ext
    exact h.trans (ConcreteCategory.congr_hom
      ((inhomogeneousCochains C).toCycles_i i n) a).symm
  rw [hz]
  exact ConcreteCategory.congr_hom
    ((inhomogeneousCochains C).toCycles_comp_homologyπ i n) a

variable
  (β : (inhomogeneousCochains A).X p →ₗ[R]
    (inhomogeneousCochains B).X q →ₗ[R] (inhomogeneousCochains C).X (p + q))
  (hz : ∀ a b, _root_.inhomogeneousCochains.d A p a = 0 →
    _root_.inhomogeneousCochains.d B q b = 0 →
    _root_.inhomogeneousCochains.d C (p + q) (β a b) = 0)

/-- A cochain pairing that preserves cycles restricts to actual cocycles. -/
def onCocycles : cocycles A p →ₗ[R] cocycles B q →ₗ[R] cocycles C (p + q) where
  toFun a :=
    { toFun b := cocyclesMk (β (iCocycles A p a) (iCocycles B q b))
        (hz _ _ (cocycle_d A p a) (cocycle_d B q b))
      map_add' b b' := by
        apply cocycle_ext
        simp [iCocycles_mk (A := C)]
      map_smul' r b := by
        apply cocycle_ext
        simp [iCocycles_mk (A := C)] }
  map_add' a a' := by
    ext b
    apply cocycle_ext
    simp [iCocycles_mk (A := C)]
  map_smul' r a := by
    ext b
    apply cocycle_ext
    simp [iCocycles_mk (A := C)]

@[simp]
lemma i_onCocycles (a : cocycles A p) (b : cocycles B q) :
    iCocycles C (p + q) (onCocycles A B C p q β hz a b) =
      β (iCocycles A p a) (iCocycles B q b) :=
  iCocycles_mk _ (hz _ _ (cocycle_d A p a) (cocycle_d B q b))

/-- The cohomology class of a cycle-preserving cochain pairing. -/
def onCycleClasses : cocycles A p →ₗ[R] cocycles B q →ₗ[R] groupCohomology C (p + q) where
  toFun a := (π C (p + q)).hom.comp (onCocycles A B C p q β hz a)
  map_add' a a' := by ext b; simp
  map_smul' r a := by ext b; simp

@[simp]
lemma onCycleClasses_apply (a : cocycles A p) (b : cocycles B q) :
    onCycleClasses A B C p q β hz a b =
      π C (p + q) (onCocycles A B C p q β hz a b) := rfl

lemma i_sc_toCycles (a : ((inhomogeneousCochains A).sc p).X₁) :
    iCocycles A p (((inhomogeneousCochains A).sc p).toCycles a) =
      ((inhomogeneousCochains A).sc p).f a :=
  ConcreteCategory.congr_hom ((inhomogeneousCochains A).sc p).toCycles_i a

variable
  (hl : ∀ (a : ((inhomogeneousCochains A).sc p).X₁) (b : cocycles B q),
    ∃ (i : ℕ) (w : (inhomogeneousCochains C).X i),
      β (((inhomogeneousCochains A).sc p).f a) (iCocycles B q b) =
        (inhomogeneousCochains C).d i (p + q) w)
  (hr : ∀ (a : cocycles A p) (b : ((inhomogeneousCochains B).sc q).X₁),
    ∃ (i : ℕ) (w : (inhomogeneousCochains C).X i),
      β (iCocycles A p a) (((inhomogeneousCochains B).sc q).f b) =
        (inhomogeneousCochains C).d i (p + q) w)

include hl in
lemma onCycleClasses_boundary_left
    (a : ((inhomogeneousCochains A).sc p).X₁) (b : cocycles B q) :
    onCycleClasses A B C p q β hz (((inhomogeneousCochains A).sc p).toCycles a) b = 0 := by
  obtain ⟨i, w, hw⟩ := hl a b
  apply class_eq_zero_of_boundary C (p + q) i _ w
  rw [i_onCocycles, i_sc_toCycles]
  exact hw

include hr in
lemma onCycleClasses_boundary_right
    (a : cocycles A p) (b : ((inhomogeneousCochains B).sc q).X₁) :
    onCycleClasses A B C p q β hz a (((inhomogeneousCochains B).sc q).toCycles b) = 0 := by
  obtain ⟨i, w, hw⟩ := hr a b
  apply class_eq_zero_of_boundary C (p + q) i _ w
  rw [i_onCocycles, i_sc_toCycles]
  exact hw

/-- Descend a cycle-preserving cochain pairing with actual boundary witnesses. -/
def fromCochains : groupCohomology A p →ₗ[R]
    groupCohomology B q →ₗ[R] groupCohomology C (p + q) :=
  descBilinear ((inhomogeneousCochains A).sc p) ((inhomogeneousCochains B).sc q)
    (groupCohomology C (p + q)) (onCycleClasses A B C p q β hz)
    (onCycleClasses_boundary_left A B C p q β hz hl)
    (onCycleClasses_boundary_right A B C p q β hz hr)

@[simp]
lemma fromCochains_π_π (a : cocycles A p) (b : cocycles B q) :
    fromCochains A B C p q β hz hl hr (π A p a) (π B q b) =
      π C (p + q) (onCocycles A B C p q β hz a b) :=
  descBilinear_π_π _ _ _ _ _ _ _ _

end Cochains

end Langlands.Tate.OrdinaryCup
