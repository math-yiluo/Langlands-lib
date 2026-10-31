import Langlands.AlgebraicGeometry.ModuleLinear
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-! # Simultaneous scalar eigensubsheaves of actual module sheaves -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}} {R : Type v} [Ring R]
  {M N P : S.Modules}
  (ρ : R →+* End M) (χ : R →+* Γ(S, ⊤))

/-- Sections on which every element acts by the specified actual scalar section. -/
def scalarEigenSections (U : S.Opens) : Submodule Γ(S, U) Γ(M, U) where
  carrier := {x | ∀ a : R, (ρ a).app U x = restrictScalar U (χ a) • x}
  zero_mem' := by intro a; simp
  add_mem' := by
    intro x y hx hy a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' := by
    intro r x hx a
    rw [Scheme.Modules.Hom.app_smul, hx a]
    exact smul_comm r (restrictScalar U (χ a)) x

@[simp]
theorem mem_scalarEigenSections (U : S.Opens) (x : Γ(M, U)) :
    x ∈ scalarEigenSections ρ χ U ↔
      ∀ a : R, (ρ a).app U x = restrictScalar U (χ a) • x := Iff.rfl

/-- The simultaneous scalar eigensections are stable under actual restriction. -/
def scalarEigenPresheafSubmodule : PresheafOfModules.Submodule M.val where
  obj U := scalarEigenSections ρ χ U.unop
  map {U V} f x hx := by
    intro a
    change (ρ a).val.app V (M.val.map f x) =
      restrictScalar V.unop (χ a) • M.val.map f x
    have ha : (ρ a).val.app U x = restrictScalar U.unop (χ a) • x := hx a
    rw [PresheafOfModules.naturality_apply, ha, M.val.map_smul]
    congr 1
    exact restrictScalar_map f.unop (χ a)

/-- The eigencondition is local because equality of sections of `M` is local. -/
def scalarEigenSubmodule : SheafOfModules.Submodule M where
  toSubmodule := scalarEigenPresheafSubmodule ρ χ
  isSheaf U x hx := by
    intro a
    apply M.isSheaf.isSeparated U.unop
      ((scalarEigenPresheafSubmodule ρ χ).toSubfunctor.sieveOfSection x) hx
    intro V j hj
    change M.val.map j.op ((ρ a).val.app U x) =
      M.val.map j.op (restrictScalar U.unop (χ a) • x)
    rw [← PresheafOfModules.naturality_apply (ρ a).val j.op x, M.val.map_smul]
    change (ρ a).val.app (op V) (M.val.map j.op x) =
      S.presheaf.map j.op (restrictScalar U.unop (χ a)) • M.val.map j.op x
    rw [restrictScalar_map j]
    exact hj a

/-- The actual subsheaf of simultaneous scalar eigensections, with its inherited modules. -/
abbrev scalarEigensheaf : S.Modules := (scalarEigenSubmodule ρ χ).toSheafOfModules

/-- The actual inclusion in the original module sheaf. -/
def scalarEigensheafι : scalarEigensheaf ρ χ ⟶ M := (scalarEigenSubmodule ρ χ).ι

instance : Mono (scalarEigensheafι ρ χ) := by
  constructor
  intro Z g h w
  ext U x
  apply Subtype.ext
  exact congrArg (fun k : Z ⟶ M => k.app U x) w

@[simp]
theorem scalarEigensheafι_app (U : S.Opens) (x : Γ(scalarEigensheaf ρ χ, U)) :
    (scalarEigensheafι ρ χ).app U x = x.val := rfl

variable {ρ χ} (τ : R →+* End N) (f : M ⟶ N)
  (hf : ∀ a : R, ρ a ≫ f = f ≫ τ a)

include hf in
/-- An equivariant actual sheaf morphism preserves the same scalar eigencondition. -/
theorem map_mem_scalarEigenSections (U : S.Opens) (x : Γ(M, U))
    (hx : x ∈ scalarEigenSections ρ χ U) :
    f.app U x ∈ scalarEigenSections τ χ U := by
  intro a
  have h := congrArg (fun g : M ⟶ N => g.app U x) (hf a)
  change f.app U ((ρ a).app U x) = (τ a).app U (f.app U x) at h
  rw [← h, hx a, Scheme.Modules.Hom.app_smul]

/-- Restrict an equivariant morphism to the constructed simultaneous eigensubsheaves. -/
def scalarEigensheafMap : scalarEigensheaf ρ χ ⟶ scalarEigensheaf τ χ where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => ⟨f.app U.unop x.val,
            map_mem_scalarEigenSections τ f hf U.unop x.val x.property⟩
          map_add' := fun x y => Subtype.ext ((f.app U.unop).hom.map_add x.val y.val)
          map_smul' := fun r x => Subtype.ext (Scheme.Modules.Hom.app_smul f r x.val) }
      naturality := by
        intro U V j
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply f.val j x.val }

@[simp]
theorem scalarEigensheafMap_app (U : S.Opens) (x : Γ(scalarEigensheaf ρ χ, U)) :
    ((scalarEigensheafMap τ f hf).app U x).val = f.app U x.val := rfl

@[reassoc (attr := simp)]
theorem scalarEigensheafMap_ι :
    scalarEigensheafMap (χ := χ) τ f hf ≫ scalarEigensheafι τ χ =
      scalarEigensheafι ρ χ ≫ f := rfl

variable (ρ χ)

@[simp]
theorem scalarEigensheafMap_id :
    scalarEigensheafMap (χ := χ) ρ (𝟙 M) (fun _ => by simp) =
      𝟙 (scalarEigensheaf ρ χ) := by
  ext U x
  rfl

variable {ρ χ τ f hf}

/-- Restricting an equivariant composite is the composite of its restrictions. -/
theorem scalarEigensheafMap_comp (υ : R →+* End P) (g : N ⟶ P)
    (hg : ∀ a : R, τ a ≫ g = g ≫ υ a) :
    scalarEigensheafMap (χ := χ) υ (f ≫ g)
        (fun a => by rw [← Category.assoc, hf a, Category.assoc, hg a,
          ← Category.assoc]) =
      scalarEigensheafMap τ f hf ≫ scalarEigensheafMap υ g hg := by
  ext U x
  rfl

/-- An actual equivariant isomorphism restricts to an actual eigenmodule-sheaf isomorphism. -/
def scalarEigensheafIso (ρ : R →+* End M) (τ : R →+* End N)
    (χ : R →+* Γ(S, ⊤)) (e : M ≅ N)
    (he : ∀ a : R, ρ a ≫ e.hom = e.hom ≫ τ a) :
    scalarEigensheaf ρ χ ≅ scalarEigensheaf τ χ where
  hom := scalarEigensheafMap τ e.hom he
  inv := scalarEigensheafMap ρ e.inv (fun a => by
    have h := congrArg (fun g : M ⟶ N => e.inv ≫ g ≫ e.inv) (he a)
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using h.symm)
  hom_inv_id := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun g : M ⟶ M => g.app U x.val) e.hom_inv_id
  inv_hom_id := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun g : N ⟶ N => g.app U x.val) e.inv_hom_id

end Langlands.Scheme.Modules
