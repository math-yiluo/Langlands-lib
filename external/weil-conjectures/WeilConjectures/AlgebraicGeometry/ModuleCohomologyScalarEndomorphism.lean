/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Scalar endomorphisms on module cohomology

Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ
(blueprint: lem-weil-pbc-module-cohomology-scalar-endomorphism).
-/

@[expose] public section

set_option autoImplicit false
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private noncomputable def scalarEnd {X : Scheme.{v}} (G : X.Modules)
    (r : (moduleRings X.toRingedSpace).obj.obj (op ⊤)) : G ⟶ G where
  val := {
    app := fun U ↦ by
      let R := (moduleRings X.toRingedSpace).obj
      letI : CommRing (R.obj U) := inferInstanceAs (CommRing (X.presheaf.obj U))
      exact ModuleCat.ofHom {
        toFun := fun t ↦ R.map (homOfLE (le_top (a := U.unop))).op r • t
        map_add' := fun _ _ ↦ smul_add _ _ _
        map_smul' := fun _ _ ↦ smul_comm _ _ _ }
    naturality := fun {U V} i ↦ by
      ext t
      change (moduleRings X.toRingedSpace).obj.map
          (homOfLE (le_top (a := V.unop))).op r • G.val.map i t =
        G.val.map i ((moduleRings X.toRingedSpace).obj.map
          (homOfLE (le_top (a := U.unop))).op r • t)
      rw [G.val.map_smul]
      congr 1
      rw [← RingCat.comp_apply, ← Functor.map_comp]
      rfl }

private theorem scalarEnd_naturality {X : Scheme.{v}} {G H : X.Modules}
    (g : G ⟶ H) (r : (moduleRings X.toRingedSpace).obj.obj (op ⊤)) :
    g ≫ scalarEnd H r = scalarEnd G r ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  change (moduleRings X.toRingedSpace).obj.map
      (homOfLE (le_top (a := U.unop))).op r • g.val.app U t =
    g.val.app U ((moduleRings X.toRingedSpace).obj.map
      (homOfLE (le_top (a := U.unop))).op r • t)
  exact ((g.val.app U).hom.map_smul _ t).symm

/-- An endomorphism given by a global scalar on sections induces the same scalar on
module cohomology.

Source: Stacks Project, Cohomology, Section 20.11, Tag 01DZ, construction by injective
resolutions; also coherent.tex, paragraph preceding Lemma 02O8.
(blueprint: lem-weil-pbc-module-cohomology-scalar-endomorphism).

Proof: Multiplication by the global section r acts on every term of an injective
resolution of G, using its restriction to each open. This commutes with differentials
and extends tau, since the section formula determines tau. The comparison theorem for
injective resolutions says this lift computes H^q(tau). Global sections turns the lift
into multiplication by r on the resolution complex. Its induced map on kernels modulo
images is multiplication by r in the module cohomology object. The argument works for
q = 0, the zero scalar, the zero module and the empty scheme without any extra hypothesis.
-/
theorem moduleCohomology_scalar_endomorphism {X : Scheme.{v}} (G : X.Modules)
    (tau : G ⟶ G) (r : (moduleRings X.toRingedSpace).obj.obj (op ⊤))
    (htau : ∀ (U : X.Opens) (t : G.val.obj (op U)),
      tau.val.app (op U) t =
        (X.presheaf.map (homOfLE (le_top (a := U))).op).hom r • t)
    (q : ℕ) (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj G) :
    ((RingedSpace.moduleCohomology X.toRingedSpace q).map tau).hom x = r • x := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op ⊤)))
  have ht : tau = scalarEnd G r := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext t
    simpa [scalarEnd, SheafedSpace.sheaf] using htau U.unop t
  let I := injectiveResolution G
  let phi : I.cocomplex ⟶ I.cocomplex := {
    f := fun n ↦ scalarEnd (I.cocomplex.X n) r
    comm' := fun i j _ ↦ (scalarEnd_naturality (I.cocomplex.d i j) r).symm }
  have hw : I.ι.f 0 ≫ phi.f 0 = tau ≫ I.ι.f 0 := by
    rw [ht]
    exact scalarEnd_naturality (I.ι.f 0) r
  let E := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have : E.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let e := I.isoRightDerivedObj E q
  have hn := InjectiveResolution.isoRightDerivedObj_hom_naturality tau I I phi hw E q
  have hm : (E.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map phi =
      r • 𝟙 (((E.mapHomologicalComplex _).obj I.cocomplex).homology q) := by
    change ShortComplex.homologyMap _ = _
    have hsc : ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) q).map
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map phi)) =
        r • 𝟙 (((E.mapHomologicalComplex _).obj I.cocomplex).sc q) := by
      ext t <;>
        simp [phi, E, RingedSpace.globalSectionsFunctor, scalarEnd,
          SheafOfModules.evaluation, PresheafOfModules.evaluation]
    rw [hsc, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  rw [hm] at hn
  have hx := CategoryTheory.congr_fun hn x
  change e.hom (((RingedSpace.moduleCohomology X.toRingedSpace q).map tau).hom x) =
    r • e.hom x at hx
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  simpa using hx


end AlgebraicGeometry
