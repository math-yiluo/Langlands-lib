/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Nonnegative finite torsion Tate twists on the small étale site

Source: Stacks Project, Étale Cohomology, Section 03PK and Groupoids, Example 040M
(auxiliary; not a blueprint node).

Module-valued sheaves are modules over the constant ring sheaf, via the existing
`etaleConstantModuleFunctor` and its inverse. The tensor below is the canonical
sheafification of the section tensor product in this encoding. No derived or pro-étale
Tate object is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

/-- Sections of the existing roots-of-unity sheaf are killed by `N`.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node).
Proof: the kernel inclusion into the multiplicative-group sheaf is injective on sections.
Its composite with multiplication by `N` is zero by the kernel condition. Naturality of
scalar multiplication therefore makes `N` times every kernel section zero. -/
theorem finiteEtaleMu_annihilated (T : Scheme.{u}) (N : ℕ) (U : T.Etaleᵒᵖ)
    (x : (T.rootsOfUnitySheaf N).obj.obj U) : N • x = 0 := by
  have h : N • 𝟙 (T.rootsOfUnitySheaf N) = 0 := by
    change N • 𝟙 (kernel (N • 𝟙 T.gmSheaf)) = 0
    rw [← cancel_mono (kernel.ι (N • 𝟙 T.gmSheaf)), Preadditive.nsmul_comp,
      Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι _),
      ← Preadditive.comp_nsmul, kernel.condition]
  have hx := congrArg (fun f : T.rootsOfUnitySheaf N ⟶ T.rootsOfUnitySheaf N ↦
    f.hom.app U x) h
  have e : (N • 𝟙 (T.rootsOfUnitySheaf N)).hom =
      N • 𝟙 (T.rootsOfUnitySheaf N).obj :=
    (sheafToPresheaf _ _).map_nsmul (f := 𝟙 (T.rootsOfUnitySheaf N)) (n := N)
  rw [e, NatTrans.app_nsmul, NatTrans.id_app] at hx
  exact hx

/-- The existing roots-of-unity sections with their unique `ZMod N`-module action.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node). -/
def finiteEtaleMuModuleObj (T : Scheme.{u}) (N : ℕ) (U : T.Etaleᵒᵖ) :
    ModuleCat.{u + 1} (ZMod N) :=
  letI := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N U)
  ModuleCat.of (ZMod N) ((T.rootsOfUnitySheaf N).obj.obj U)

/-- Restriction of roots of unity, with the same additive map made `ZMod N`-linear.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node). -/
def finiteEtaleMuModuleMap (T : Scheme.{u}) (N : ℕ) {U V : T.Etaleᵒᵖ} (f : U ⟶ V) :
    finiteEtaleMuModuleObj T N U ⟶ finiteEtaleMuModuleObj T N V :=
  letI := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N U)
  letI := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N V)
  ModuleCat.ofHom (((T.rootsOfUnitySheaf N).obj.map f).hom.toZModLinearMap N)

/-- Identity law for the module enhancement of roots of unity.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node).
Proof: forgetting the linear structure gives exactly the identity restriction of the
existing roots-of-unity sheaf; linear maps are equal when their functions are equal. -/
theorem finiteEtaleMuModuleMap_id (T : Scheme.{u}) (N : ℕ) (U : T.Etaleᵒᵖ) :
    finiteEtaleMuModuleMap T N (𝟙 U) = 𝟙 (finiteEtaleMuModuleObj T N U) := by
  ext x
  change (T.rootsOfUnitySheaf N).obj.obj U at x
  change (T.rootsOfUnitySheaf N).obj.map (𝟙 U) x = x
  rw [(T.rootsOfUnitySheaf N).obj.map_id]
  rfl

/-- Composition law for the module enhancement of roots of unity.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node).
Proof: both underlying maps are restrictions in the existing roots-of-unity sheaf.
Its functor composition law identifies them, and equality of underlying functions gives
equality of the linear maps. -/
theorem finiteEtaleMuModuleMap_comp (T : Scheme.{u}) (N : ℕ)
    {U V W : T.Etaleᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    finiteEtaleMuModuleMap T N (f ≫ g) =
      finiteEtaleMuModuleMap T N f ≫ finiteEtaleMuModuleMap T N g := by
  ext x
  change (T.rootsOfUnitySheaf N).obj.obj U at x
  change (T.rootsOfUnitySheaf N).obj.map (f ≫ g) x =
    (T.rootsOfUnitySheaf N).obj.map g ((T.rootsOfUnitySheaf N).obj.map f x)
  rw [(T.rootsOfUnitySheaf N).obj.map_comp]
  rfl

/-- The existing roots-of-unity presheaf with its exponent action of `ZMod N`.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node). -/
def finiteEtaleMuModulePresheaf (T : Scheme.{u}) (N : ℕ) :
    T.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod N) where
  obj := finiteEtaleMuModuleObj T N
  map := finiteEtaleMuModuleMap T N
  map_id := finiteEtaleMuModuleMap_id T N
  map_comp := finiteEtaleMuModuleMap_comp T N

/-- The canonical scalar map exists exactly when the coefficient ring is killed by `N`.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node). -/
def finiteEtaleTwistScalar (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ZMod N →+* A :=
  ZMod.castHom ((CharP.cast_eq_zero_iff A (ringChar A) N).mp hA) A

/-- The first finite torsion twist: sheafify the sectionwise extension of scalars
`A ⊗[ZMod N] μ_N`, canonically the same as `μ_N ⊗[ZMod N] A` by symmetry.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node). -/
def finiteEtaleTateLine (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (finiteEtaleMuModulePresheaf T N ⋙ ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA))

/-- The nonnegative finite torsion twists: degree zero is the constant coefficient sheaf,
degree one is extension of scalars of roots of unity, and subsequent degrees are tensor
powers using the canonical sheaf tensor product.
Source: Stacks, Section 03PK (auxiliary; not a blueprint node). -/
def finiteEtaleTateTwist (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ℕ → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)
  | 0 => (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
  | 1 => finiteEtaleTateLine T N A hA
  | r + 2 =>
    letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} A)
    finiteEtaleTateTwist T N A hA (r + 1) ⊗ finiteEtaleTateLine T N A hA

end AlgebraicGeometry.Scheme
