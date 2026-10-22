import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- Restrict a global regular function to an open subset. -/
def restrictScalar (U : S.Opens) : Γ(S, ⊤) →+* Γ(S, U) :=
  (S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

@[simp]
lemma restrictScalar_map {U V : S.Opens} (i : U ⟶ V) (r : Γ(S, ⊤)) :
    S.presheaf.map i.op (restrictScalar V r) = restrictScalar U r := by
  exact (ConcreteCategory.congr_hom (S.presheaf.map_comp
    (homOfLE le_top : V ⟶ ⊤).op i.op) r).symm

/-- Multiply an O_S-linear map by a global regular function, on every open. -/
def scalarHom {M N : S.Modules} (r : Γ(S, ⊤)) (f : M ⟶ N) : M ⟶ N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => restrictScalar U.unop r • (f.val.app U) x
          map_add' := by intros; simp [smul_add]
          map_smul' := by
            intro a x
            change restrictScalar U.unop r • (f.val.app U) ((a : Γ(S, U.unop)) • x) =
              a • (restrictScalar U.unop r • (f.val.app U) x)
            rw [(f.val.app U).hom.map_smul]
            exact @smul_comm Γ(S, U.unop) Γ(S, U.unop) Γ(N, U.unop)
              _ _ _ (restrictScalar U.unop r) a ((f.val.app U) x) }
      naturality := by
        intro U V i
        ext x
        change restrictScalar V.unop r • (f.val.app V) (M.val.map i x) =
          N.val.map i (restrictScalar U.unop r • (f.val.app U) x)
        rw [PresheafOfModules.naturality_apply, N.val.map_smul]
        congr 1
        exact (restrictScalar_map i.unop r).symm }

@[simp]
lemma scalarHom_app {M N : S.Modules} (r : Γ(S, ⊤)) (f : M ⟶ N)
    (U : S.Opens) (x : Γ(M, U)) :
    (scalarHom r f).app U x = restrictScalar U r • f.app U x := rfl

/-- Global regular functions act on sheaf morphisms. -/
instance globalHomSMul (M N : S.Modules) : SMul Γ(S, ⊤) (M ⟶ N) where
  smul := scalarHom

@[simp]
lemma global_smul_app {M N : S.Modules} (r : Γ(S, ⊤)) (f : M ⟶ N)
    (U : S.Opens) (x : Γ(M, U)) :
    (r • f).app U x = restrictScalar U r • f.app U x := rfl

/-- The module structure on sheaf morphisms over the ring of global functions. -/
instance globalHomModule (M N : S.Modules) : Module Γ(S, ⊤) (M ⟶ N) where
  one_smul := by intros; ext U x; simp
  mul_smul := by intros; ext U x; simp [mul_smul]
  smul_zero := by intros; ext U x; simp
  smul_add := by intros; ext U x; simp [smul_add]
  add_smul := by intros; ext U x; simp [add_smul]
  zero_smul := by intros; ext U x; simp

/-- Composition of sheaf morphisms is bilinear over global regular functions. -/
instance globalSectionsLinear : Linear Γ(S, ⊤) S.Modules where
  smul_comp := by intros; ext U x; simp
  comp_smul := by intros; ext U x; simp

/-- A homomorphism into global regular functions makes the module category linear. -/
@[instance_reducible]
def linearOfGlobalScalars {R : Type*} [CommRing R]
    (a : R →+* Γ(S, ⊤)) : Linear R S.Modules where
  homModule M N := Module.compHom (M ⟶ N) a
  smul_comp M N P r f g := by
    change (a r • f) ≫ g = a r • (f ≫ g)
    exact Linear.smul_comp M N P (a r) f g
  comp_smul M N P f r g := by
    change f ≫ (a r • g) = a r • (f ≫ g)
    exact Linear.comp_smul M N P f (a r) g

/-- Endomorphisms of an actual module sheaf form an algebra over global scalars. -/
@[instance_reducible]
def endAlgebra {R : Type*} [CommRing R] (a : R →+* Γ(S, ⊤)) (M : S.Modules) :
    Algebra R (End M) := by
  letI := linearOfGlobalScalars a
  infer_instance

/-- The scalar algebra map multiplies sections by the restricted scalar. -/
lemma endAlgebra_map_app {R : Type*} [CommRing R] (a : R →+* Γ(S, ⊤))
    (M : S.Modules) (r : R) (U : S.Opens) (x : Γ(M, U)) :
    letI := endAlgebra a M
    ((algebraMap R (End M)) r).app U x = restrictScalar U (a r) • x := by
  let := endAlgebra a M
  change ((a r • (𝟙 M : M ⟶ M)).app U x) = _
  simp

/-- The structure map of a scheme over Spec R gives its global scalar map. -/
def scalarsFromBase {R : CommRingCat.{u}} (p : S ⟶ Spec R) : R →+* Γ(S, ⊤) :=
  ((AlgebraicGeometry.Scheme.ΓSpecIso R).inv ≫ p.appTop).hom

/-- Actual module sheaves on an R-scheme form an R-linear category. -/
@[instance_reducible]
def linearOverBase {R : CommRingCat.{u}} (p : S ⟶ Spec R) : Linear R S.Modules :=
  linearOfGlobalScalars (scalarsFromBase p)

/-- Over an affine rational algebra base, actual module sheaves form a Q-linear category. -/
@[instance_reducible]
def rationalLinearOverBase {R : CommRingCat.{u}} [Algebra ℚ R]
    (p : S ⟶ Spec R) : Linear ℚ S.Modules :=
  linearOfGlobalScalars ((scalarsFromBase p).comp (algebraMap ℚ R))

end Langlands.Scheme.Modules
