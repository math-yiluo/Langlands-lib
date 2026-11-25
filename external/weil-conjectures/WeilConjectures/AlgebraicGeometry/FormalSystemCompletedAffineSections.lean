/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.CompletedAffineSectionsPowerTorsion
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineOpenSectionsAdic
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Termwise section comparison for a completed affine chart

Source: Stacks Project, Tags 088B and 05GG.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A coherent formal system has the same section diagram after completed affine
pullback and scalar restriction. The comparisons are natural in every formal map.
No proper morphism, coherent algebraization, or inverse limit occurs here.

Source: Stacks Project, Tag 088B, completed-base change and power-torsion paragraphs;
Tag 05GG, positive-power quotient formula; Tag 01I9, affine pullback sections.
(blueprint: lem-weil-pbc-formal-system-completed-affine-sections)

Proof: Put B = O_Y(U), K = J(U), and R = the K-adic completion of B. Coherence
makes every G_n quasi-coherent, so affine pullback sections identify sections over
Spec R with R tensor_B sections over U, naturally in sheaf maps. The original
section module at level n is annihilated by K^(n+1), by the formal support axiom
and the affine ideal-product section formula. Since K is finitely generated,
R/K^(n+1)R is B/K^(n+1), compatibly with the completion map. Therefore the tensor
unit on this module is an isomorphism: tensor first over B/K^(n+1) and use that
quotient-ring isomorphism. Compose this unit with the affine pullback section
comparison and restrict scalars from R to B. Naturality of both comparisons
makes these level isomorphisms commute with all transitions, hence gives e G as
an isomorphism of diagrams. The same naturality for a proves the displayed square.
For K=B all levels vanish and the comparison is between zero modules. For K=0
it is the identity base change. Zero rings and empty affine charts are included.
-/
theorem formalSystem_completed_affine_sections
    {Y : Scheme.{u}} [IsNoetherian Y] (J : Y.IdealSheafData) (U : Y.affineOpens) :
    let B := Γ(Y, U.1)
    let R := AdicCompletion (J.ideal U) B
    let S := Spec (CommRingCat.of R)
    let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
      U.2.isoSpec.inv ≫ U.1.ι
    let T := Scheme.Modules.tensorPullback g
    let E := moduleSpecΓFunctor (R := CommRingCat.of R)
    let L := ModuleCat.restrictScalars (algebraMap B R)
    ∃ e : ∀ G : CoherentFormalModule Y J,
      G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1) ≅
        (G.obj ⋙ T ⋙ E) ⋙ L,
      ∀ (G H : CoherentFormalModule Y J) (a : G ⟶ H),
        Functor.whiskerRight a.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≫ (e H).hom =
          (e G).hom ≫ Functor.whiskerRight
            (Functor.whiskerRight (Functor.whiskerRight a.hom T) E) L := by
  dsimp only
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  let g : Spec (CommRingCat.of R) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ U.2.isoSpec.inv ≫ U.1.ι
  let A := SheafOfModules.evaluation Y.ringCatSheaf (op U.1)
  let P := Scheme.Modules.tensorPullback g ⋙ moduleSpecΓFunctor (R := CommRingCat.of R) ⋙
    ModuleCat.restrictScalars (algebraMap B R)
  obtain ⟨c, hc⟩ := completedAffineSections_powerTorsion J U
  have hi (G : CoherentFormalModule Y J) (n : ℕ) : IsIso (c.app (G.obj.obj (op n))) := by
    have hqc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
      Y (G.obj.obj (op n))).mp (G.property.1 n)
    exact hc _ hqc.1 n ((coherentFormalModule_affine_open_sections_adic Y J G U).2.1 n)
  let e (G : CoherentFormalModule Y J) : G.obj ⋙ A ≅ G.obj ⋙ P :=
    NatIso.ofComponents (fun n ↦ @asIso _ _ _ _ (c.app (G.obj.obj n)) (hi G n.unop))
      (fun h ↦ c.naturality (G.obj.map h))
  refine ⟨e, ?_⟩
  intro G H a
  apply NatTrans.ext
  funext n
  simpa only [e, NatIso.ofComponents_hom_app, asIso_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_map] using
    c.naturality (a.hom.app n)

end AlgebraicGeometry
