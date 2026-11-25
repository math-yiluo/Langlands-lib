/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison

public import WeilConjectures.Topology.OpenModuleCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Vanishing open cohomology in degree p makes the corresponding column homology zero.
Source: Stacks Project, Tag 01ET, proof using the columns of the double complex of 01EQ.
(blueprint: lem-sc-module-cech-resolution-column-positive)

Proof: for each tuple y, apply the resolution-computation isomorphism for the right
derived functor of sections on the intersection of U(y(l)). By the hypothesis its
degree-p homology is zero, so every degree-p cocycle is the differential of a degree
p-1 element. The Cech column consists of products of these section modules, with
coordinatewise resolution differential. Choose a preimage for each coordinate of a
product cocycle. Their tuple is a preimage in the column, proving exactness in degree p.
Restriction of scalars to the global section ring preserves this underlying exactness.
Exactness in degree p is equivalent to the homology object being zero. For an empty
tuple-indexing type the product is zero, so the same argument applies. -/
theorem moduleCech_resolution_column_positive {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (I : InjectiveResolution F) (n p : ℕ)
    (hp : 0 < p)
    (hvan : ∀ y : Fin (n + 1) → ι,
      Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p
        (⨅ l, U (y l))).obj F)) :
    IsZero (((moduleCechDouble U I).flip.X n).homology p) := by
  classical
  let K := (moduleCechDouble U I).flip.X n
  let V (y : Fin (n + 1) → ι) : X.Opens := ∏ᶜ fun l => U (y l)
  have hV (y : Fin (n + 1) → ι) : V y = ⨅ l, U (y l) := by
    apply le_antisymm
    · exact le_iInf fun l => leOfHom (Pi.π (fun l => U (y l)) l)
    · exact leOfHom (Pi.lift fun l => homOfLE (iInf_le (fun l => U (y l)) l))
  let A (y : Fin (n + 1) → ι) := RingedSpace.openModuleSections X.toRingedSpace (V y)
  have : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : EnoughInjectives (SheafOfModules (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have (y : Fin (n + 1) → ι) : (A y).Additive :=
    inferInstanceAs (RingedSpace.openModuleSections X.toRingedSpace (V y)).Additive
  have hcoord (y : Fin (n + 1) → ι) :
      ((A y).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex |>.ExactAt p := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ p).2
    have hv : Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p
        (V y)).obj F) := by rw [hV]; exact hvan y
    change Subsingleton (((A y).rightDerived p).obj F) at hv
    have := hv
    exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso
      (I.isoRightDerivedObj (A y) p).symm
  have hdπ (a b : ℕ) (y : Fin (n + 1) → ι) :
      K.d a b ≫ Pi.π (fun y => (I.cocomplex.X b).presheafModuleCat.obj (op (V y))) y =
        Pi.π (fun y => (I.cocomplex.X a).presheafModuleCat.obj (op (V y))) y ≫
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (I.cocomplex.d a b).val).app (op (V y)) := by
    change (Limits.Pi.map fun y =>
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (I.cocomplex.d a b).val).app (op (V y))) ≫ _ = _
    exact Limits.Pi.map_π _ y
  let M (a : ℕ) (y : Fin (n + 1) → ι) :=
    (I.cocomplex.X a).presheafModuleCat.obj (op (V y))
  let D (a b : ℕ) (y : Fin (n + 1) → ι) : M a y ⟶ M b y :=
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
      (I.cocomplex.d a b).val).app (op (V y))
  let q := p - 1
  have hq : (ComplexShape.up ℕ).prev p = q :=
    (ComplexShape.up ℕ).prev_eq' (by change p - 1 + 1 = p; omega)
  let r := (ComplexShape.up ℕ).next p
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [K.exactAt_iff' q p r hq rfl, ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hex (y : Fin (n + 1) → ι) :
      ∃ z : M q y, D q p y z = Pi.π (M p) y x := by
    have hecoord := hcoord y
    rw [HomologicalComplex.exactAt_iff' _ q p r hq rfl] at hecoord
    have he := (ShortComplex.ab_exact_iff _).1 hecoord
    change ∀ x : M p y, D p r y x = 0 → ∃ z : M q y, D q p y z = x at he
    apply he
    rw [← ConcreteCategory.comp_apply, ← hdπ p r y,
      ConcreteCategory.comp_apply]
    change Pi.π (M r) y (((K.sc' q p r).g) x) = 0
    rw [hx, map_zero]
  let z : K.X q := (ModuleCat.piIsoPi (M q)).inv (fun y => (hex y).choose)
  refine ⟨z, ?_⟩
  apply (ModuleCat.mono_iff_injective (ModuleCat.piIsoPi (M p)).hom).1 inferInstance
  funext y
  have hproj (a : ℕ) (v : K.X a) :
      ((ModuleCat.piIsoPi (M a)).hom v) y = Pi.π (M a) y v := by
    exact ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype (M a) y) v
  rw [hproj, hproj]
  change Pi.π (M p) y (K.d q p z) = _
  have hd := ConcreteCategory.congr_hom (hdπ q p y) z
  change Pi.π (M p) y (K.d q p z) = D q p y (Pi.π (M q) y z) at hd
  refine hd.trans ?_
  have hz : Pi.π (M q) y z = (hex y).choose :=
    ConcreteCategory.congr_hom (ModuleCat.piIsoPi_inv_kernel_ι (M q) y)
      (fun y => (hex y).choose)
  rw [hz]
  exact (hex y).choose_spec

end AlgebraicGeometry.Scheme.Modules
