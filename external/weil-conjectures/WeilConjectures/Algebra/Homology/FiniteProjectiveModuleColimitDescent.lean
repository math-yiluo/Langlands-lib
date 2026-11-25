/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.Algebra.Homology.FinitePresentationPreorderColimitModel
import WeilConjectures.Algebra.Homology.FinitePresentationColimitRetraction

/-! # Descent of one finite projective module

Source: Stacks Project, More on Algebra, Tag 0BC7, first paragraph of the proof.
(blueprint: lem-pc-finite-projective-module-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A single finite projective module over a directed ring colimit has a finite projective model.
Source: Stacks Project, More on Algebra, Tag 0BC7, first paragraph of the proof,
and Algebra, Tags 05N7 and 00NX.
(blueprint: lem-pc-finite-projective-module-colimit-descent).

Proof: Replace the directed preorder by its antisymmetrization, choosing representatives.
The resulting equivalence of indexing categories transports the diagram and its colimit.
A finite projective module is finitely presented. Apply the object clause of finite-presentation
colimit descent to obtain a finitely presented stage model. Choose a split surjection from a
finite free module onto the original module, using finite generation and projectivity. The
finite free module has the evident stage model with the same finite basis. Apply the map
clause to the section and retraction and pass to a common later stage. The canonical iterated
base-change isomorphisms identify these base-changed maps with the original splitting maps.
Their composite becomes the identity over the colimit. Apply the equality clause to make
this identity hold at a further stage. The stage model is then a summand of the finite free
module, hence finite and projective. Its colimit base change is the original module, by the
iterated base-change isomorphism. Finally lift the stage back along the equivalence of indexing
categories and transport the module isomorphism along the induced colimit ring isomorphism.
For a zero module one may take the zero stage module; for a singleton indexing category the
construction agrees with transport along the canonical colimit isomorphism. -/
theorem exists_finite_projective_module_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (X : ModuleCat.{u} (colimit F : CommRingCat.{u}))
    (hfinite : Module.Finite (colimit F : CommRingCat.{u}) X)
    (hprojective : Module.Projective (colimit F : CommRingCat.{u}) X) :
    ∃ (i : I) (M : ModuleCat.{u} (F.obj i)),
      Module.Finite (F.obj i) M ∧ Module.Projective (F.obj i) M ∧
      Nonempty ((extendScalars (colimit.ι F i).hom).obj M ≅ X) := by
  classical
  let A := (colimit F : CommRingCat.{u})
  have : Module.Finite A X := hfinite
  have : Module.Projective A X := hprojective
  have hfp := Module.finitePresentation_of_projective A X
  obtain ⟨i, M, hM, ⟨eM⟩⟩ :=
    exists_finitePresentation_model_of_preorder_colimit F X hfp
  obtain ⟨n, r, s, _, _, hsr⟩ := Module.Finite.exists_comp_eq_id_of_projective A X
  let N := ModuleCat.of (F.obj i) (Fin n → F.obj i)
  let ri := (colimit.ι F i).hom
  let : Algebra (F.obj i) A := ri.toAlgebra
  let b := (Pi.basisFun (F.obj i) (Fin n)).baseChange A
  let eN : (extendScalars ri).obj N ≅ ModuleCat.of A (Fin n → A) :=
    b.equivFun.toModuleIso
  let sA := eM.hom ≫ ModuleCat.ofHom s ≫ eN.inv
  let rA := eN.hom ≫ ModuleCat.ofHom r ≫ eM.inv
  have hsrA : sA ≫ rA = 𝟙 _ := by
    have hlin : ModuleCat.ofHom s ≫ ModuleCat.ofHom r = 𝟙 X := by
      exact ModuleCat.hom_ext hsr
    simp only [sA, rA, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (ModuleCat.ofHom s) (ModuleCat.ofHom r), hlin]
    simp
  have hN : Module.FinitePresentation (F.obj i) N := inferInstance
  obtain ⟨j, hij, s', r', hsplit, -, -⟩ :=
    exists_retraction_model_of_directed_colimit F i M N hM hN sA rA hsrA
  let e := (eqToIso (congrArg (fun r ↦ (extendScalars r).obj M)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hij)).symm)) ≪≫
    (extendScalarsComp (F.map (homOfLE hij)).hom (colimit.ι F j).hom).app M).symm
  let rij := (F.map (homOfLE hij)).hom
  let : Algebra (F.obj i) (F.obj j) := rij.toAlgebra
  let b' := (Pi.basisFun (F.obj i) (Fin n)).baseChange (F.obj j)
  have : Module.Free (F.obj j) ((extendScalars rij).obj N) :=
    Module.Free.of_basis b'
  have hsplit' : r'.hom.comp s'.hom = LinearMap.id :=
    congrArg ModuleCat.Hom.hom hsplit
  have hproj : Module.Projective (F.obj j) ((extendScalars rij).obj M) :=
    Module.Projective.of_split s'.hom r'.hom hsplit'
  have : Module.Finite (F.obj j) ((extendScalars rij).obj N) :=
    Module.Finite.of_basis b'
  have hfin : Module.Finite (F.obj j) ((extendScalars rij).obj M) :=
    Module.Finite.of_surjective r'.hom
      (LinearMap.surjective_of_comp_eq_id _ _ hsplit')
  exact ⟨j, (extendScalars rij).obj M, hfin, hproj, ⟨e ≪≫ eM⟩⟩

end ModuleCat
