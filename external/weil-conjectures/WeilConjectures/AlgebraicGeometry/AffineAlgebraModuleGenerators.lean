/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Global generators of algebra modules on an affine open

Source: Stacks Project, Morphisms, Lemma 0H88, proof, second paragraph;
EGA I, Proposition 9.6.1.
(blueprint: lem-weil-pbc-affine-algebra-module-generators).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem generatingSections_of_restrictScalars
    {C : Type u} [Category C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (α : R ⟶ R') (M : SheafOfModules.{u} R')
    (G : ((SheafOfModules.restrictScalars α).obj M).GeneratingSections) :
    Nonempty M.GeneratingSections := by
  let F := SheafOfModules.restrictScalars α
  refine ⟨{ I := G.I, s := G.s, epi := ?_ }⟩
  constructor
  intro N f g h
  have hs : ∀ i, SheafOfModules.sectionsMap f (G.s i) =
      SheafOfModules.sectionsMap g (G.s i) := by
    intro i
    have hh := congrArg (fun p ↦ N.freeHomEquiv p i) h
    simpa only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply] using hh
  have he : G.π ≫ F.map f = G.π ≫ F.map g := by
    apply ((F.obj N).freeHomEquiv).injective
    funext i
    simp only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    ext X
    exact congrArg (fun s ↦ s.val X) (hs i)
  have hf : F.map f = F.map g := (cancel_epi G.π).mp he
  ext X x
  exact congrArg (fun p ↦ p.val.app X x) hf

private theorem nonempty_generatingSections_affine (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] : Nonempty M.GeneratingSections := by
  let N := M.restrict X.isoSpec.inv
  have : N.IsQuasicoherent := inferInstance
  have : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  let P : N.Presentation :=
    (presentationTilde ((modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤))
      .univ (by simp) _ (Submodule.span_eq _)).ofIsIso N.fromTildeΓ
  have : Limits.PreservesColimitsOfSize.{u, u} (restrictFunctor X.isoSpec.hom) :=
    inferInstance
  let G := P.generators.map (restrictFunctor X.isoSpec.hom) (restrictUnitIso _).symm
  let e : (restrictFunctor X.isoSpec.hom).obj N ≅ M :=
    ((restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).app M).symm ≪≫
      (restrictFunctorCongr X.isoSpec.hom_inv_id).app M ≪≫ restrictFunctorId.app M
  exact ⟨G.ofEpi e.hom⟩

private theorem nonempty_generatingSections_affine_slice (S : Scheme.{u})
    (U : S.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u} (S.ringCatSheaf.over U)) [M.IsQuasicoherent] :
    Nonempty M.GeneratingSections := by
  have : IsAffine U.toScheme := hU
  have (V : TopologicalSpace.Opens ↥U) :
      (Over.post (X := V) U.overEquivalence.symm.functor).IsContinuous
        ((Opens.grothendieckTopology ↥U).over V)
        (((Opens.grothendieckTopology ↥S).over U).over
          (U.overEquivalence.inverse.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  have : ((overEquiv U).functor.obj M).IsQuasicoherent :=
    @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u, u, u, u, u}
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (U.sheafOfModulesEquivOverUnit S.ringCatSheaf) _ _ (fun V ↦ this V) _ _ M _
  obtain ⟨G⟩ := nonempty_generatingSections_affine U.toScheme ((overEquiv U).functor.obj M)
  let H := G.map (overEquiv U).inverse
    (U.sheafOfModulesEquivOverInverseUnit S.ringCatSheaf).symm
  exact ⟨H.ofEpi ((overEquiv U).unitIso.app M).inv⟩

/-- Global generation is the first half of the affine algebra-module presentation.
Source: Stacks Project, Morphisms, Lemma 0H88, second paragraph; EGA I, Proposition 9.6.1.
(blueprint: lem-weil-pbc-affine-algebra-module-generators)

Proof: identify the open subscheme U with Spec O_S(U), and its slice site with the
opens of that subscheme. The underlying quasi-coherent module is the tilde of its
module of global sections. Those sections generate the tilde: on each principal open
every section is a fraction of a global section, and these opens form a basis. Give
these same global sections their A(U)-module structure. The A-linear evaluation map
from the free A-module sheaf on all sections contains the image of the O-linear
evaluation map. The latter is locally surjective, so the former is locally surjective
and hence epi. Transporting back to the slice gives the required generating sections.
This asserts only generation, not generation of the kernel or a presentation. -/
theorem nonempty_affine_algebraModule_generatingSections
    (S : Scheme.{u}) (A : S.CommAlgebraSheaf) (U : S.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u}
      (((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right).over U))
    (hM : ((SheafOfModules.restrictScalars
      (((Opens.grothendieckTopology S).overPullback RingCat U).map
        ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
          A.hom))).obj M).IsQuasicoherent) :
    Nonempty M.GeneratingSections := by
  let α := ((Opens.grothendieckTopology S).overPullback RingCat U).map
    ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map A.hom)
  have : ((SheafOfModules.restrictScalars α).obj M).IsQuasicoherent := hM
  obtain ⟨G⟩ := nonempty_generatingSections_affine_slice S U hU
    ((SheafOfModules.restrictScalars α).obj M)
  exact generatingSections_of_restrictScalars α M G

end AlgebraicGeometry.Scheme.Modules
