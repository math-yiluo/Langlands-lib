import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof

/-! # Component API for sheaves of cocycle-compatible families

This module reuses `Picard.CocycleGluing.glued`. The construction and every
formula below require neither an open cover nor the cocycle identity.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule.CocycleSheaf

open Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}} {ι : Type u} (T : ι → X.Opens)

/-- Families of structure-sheaf sections on the pieces of `U`. -/
abbrev Family (U : X.Opens) : Type u := CocycleGluing.Fam T U

variable {T} (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)

/-- The coordinate equation on `U ⊓ T i ⊓ T j`, with convention `b i = g i j * b j`. -/
def Compatible {U : X.Opens} (b : Family T U) : Prop :=
  ∀ i j : ι,
    X.presheaf.map (homOfLE (inf_le_left : U ⊓ T i ⊓ T j ≤ U ⊓ T i)).op (b i) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U ⊓ T i ⊓ T j ≤ T i ⊓ T j)).op (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          U ⊓ T i ⊓ T j ≤ U ⊓ T j)).op (b j)

/-- Checking the equation on the overlap is equivalent to checking every subopen. -/
lemma compatible_iff {U : X.Opens} (b : Family T U) :
    Compatible g b ↔ CocycleGluing.Compat g b := by
  constructor
  · intro hb i j V hi hj
    have hV : V ≤ U ⊓ T i ⊓ T j := le_inf hi (hj.trans inf_le_right)
    have h := congrArg (fun z ↦ X.presheaf.map (homOfLE hV).op z) (hb i j)
    simpa only [map_mul, CocycleGluing.res_res] using h
  · intro hb i j
    exact hb i j (U ⊓ T i ⊓ T j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

/-- The actual module sheaf of compatible families, reusing the published construction. -/
noncomputable abbrev moduleSheaf : X.Modules := CocycleGluing.glued g

/-- The `i`-th coordinate of a section on `U`. -/
def component (U : X.Opens) (i : ι) (s : Γ(moduleSheaf g, U)) : Γ(X, U ⊓ T i) :=
  CocycleGluing.comp g s i

/-- Build a section from a family satisfying the overlap equations. -/
def mkSection (U : X.Opens) (b : Family T U) (hb : Compatible g b) :
    Γ(moduleSheaf g, U) :=
  CocycleGluing.mk g b ((compatible_iff g b).mp hb)

@[simp]
lemma component_mkSection (U : X.Opens) (i : ι) (b : Family T U) (hb : Compatible g b) :
    component g U i (mkSection g U b hb) = b i :=
  rfl

/-- Sections are determined by all their coordinates. -/
lemma section_ext (U : X.Opens) {s t : Γ(moduleSheaf g, U)}
    (h : ∀ i, component g U i s = component g U i t) : s = t :=
  CocycleGluing.eq_of_comp g h

@[simp]
lemma component_zero (U : X.Opens) (i : ι) :
    component g U i (0 : Γ(moduleSheaf g, U)) = 0 :=
  rfl

@[simp]
lemma component_add (U : X.Opens) (i : ι) (s t : Γ(moduleSheaf g, U)) :
    component g U i (s + t) = component g U i s + component g U i t :=
  rfl

/-- Scalars act after restriction from `U` to `U ⊓ T i`. -/
@[simp]
lemma component_smul (U : X.Opens) (i : ι) (r : Γ(X, U)) (s : Γ(moduleSheaf g, U)) :
    component g U i (r • s) =
      X.presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op r * component g U i s :=
  rfl

/-- Restriction in the module sheaf restricts every coordinate. -/
@[simp]
lemma component_restrict {U V : X.Opens} (h : V ≤ U) (i : ι)
    (s : Γ(moduleSheaf g, U)) :
    component g V i ((moduleSheaf g).presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE (inf_le_inf_right (T i) h)).op (component g U i s) :=
  rfl

/-- The coordinates of every section satisfy the overlap equations. -/
lemma component_compatible (U : X.Opens) (s : Γ(moduleSheaf g, U)) :
    Compatible g (fun i ↦ component g U i s) :=
  (compatible_iff g _).mpr (CocycleGluing.compat_of_mem g s)

/-- The compatibility equation on a specified overlap. -/
lemma component_overlap (U : X.Opens) (s : Γ(moduleSheaf g, U)) (i j : ι) :
    X.presheaf.map (homOfLE (inf_le_left : U ⊓ T i ⊓ T j ≤ U ⊓ T i)).op
        (component g U i s) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U ⊓ T i ⊓ T j ≤ T i ⊓ T j)).op (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          U ⊓ T i ⊓ T j ≤ U ⊓ T j)).op (component g U j s) :=
  component_compatible g U s i j

/-- Rebuilding a section from its coordinates recovers the section. -/
@[simp]
lemma mkSection_components (U : X.Opens) (s : Γ(moduleSheaf g, U)) :
    mkSection g U (fun i ↦ component g U i s) (component_compatible g U s) = s :=
  section_ext g U (fun _ ↦ rfl)

/-- Sections are exactly the subtype of compatible coordinate families. -/
def sectionsEquiv (U : X.Opens) :
    Γ(moduleSheaf g, U) ≃ {b : Family T U // Compatible g b} where
  toFun s := ⟨fun i ↦ component g U i s, component_compatible g U s⟩
  invFun b := mkSection g U b.1 b.2
  left_inv := mkSection_components g U
  right_inv _ := Subtype.ext (funext fun _ ↦ rfl)

@[simp]
lemma sectionsEquiv_apply (U : X.Opens) (s : Γ(moduleSheaf g, U)) (i : ι) :
    (sectionsEquiv g U s).1 i = component g U i s :=
  rfl

@[simp]
lemma sectionsEquiv_symm_apply (U : X.Opens) (b : {b : Family T U // Compatible g b}) :
    (sectionsEquiv g U).symm b = mkSection g U b.1 b.2 :=
  rfl

end Langlands.SchemeModule.CocycleSheaf
