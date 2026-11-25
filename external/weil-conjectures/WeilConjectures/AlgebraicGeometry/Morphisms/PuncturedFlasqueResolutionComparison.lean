/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedTildeSectionsComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.InjectiveModuleTildeFlasque
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.Zero

/-! The comparison maps underlying the flasque resolution computation.

## References

* Stacks Project, Tags 09T2 and 0A6T
-/

@[expose] public section

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The comparison maps from cohomology to the sections homology and back. -/
theorem punctured_flasque_resolution_comparison_maps
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (W : (Spec (.of R)).Opens)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) (n : ℕ) :
    ∃ f : Modules.H (X := W.toScheme)
        (SheafOfModules.unit W.toScheme.ringCatSheaf) n →+
        ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier,
      ∃ g : ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier →+
        Modules.H (X := W.toScheme)
          (SheafOfModules.unit W.toScheme.ringCatSheaf) n,
      (Function.LeftInverse g f) ∧ (Function.RightInverse g f) := by
  let Y := W.toScheme
  let F := (SheafOfModules.toSheaf Y.ringCatSheaf).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology Y.carrier)
    AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (Opposite.op ⊤)
  let T := puncturedRestrictedAbelianFunctor R W
  let K := (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  obtain ⟨ι, hι⟩ := punctured_tilde_resolution_exact R W I
  have : QuasiIso ι := hι
  have hac (k : ℕ) : Γ.rightAcyclic (K.X k) := by
    have : Injective (I.cocomplex.X k) := inferInstance
    have hf := injective_tilde_isFlasque R (I.cocomplex.X k)
    have : TopCat.Sheaf.IsFlasque (K.X k) := by
      constructor
      intro U V f
      apply (AddCommGrpCat.epi_iff_surjective _).mpr
      exact (ModuleCat.epi_iff_surjective
        ((modulesSpecToSheaf.obj (tilde (R := .of R) (I.cocomplex.X k))).obj.map
          (W.ι.opensFunctor.map f.unop).op)).mp inferInstance
    intro q
    have : Subsingleton (Sheaf.H (K.X k) (q + 1)) :=
      TopCat.Sheaf.IsFlasque.subsingleton_H q (K.X k)
    obtain ⟨e⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
      (Opens.grothendieckTopology Y.carrier) ⊤ Limits.isTerminalTop (K.X k) q
    have : Subsingleton ((Γ.rightDerived (q + 1)).obj (K.X k)) :=
      e.symm.injective.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  have he : Nonempty (Sheaf.H F n ≃+ (Γ.rightDerived n).obj F) := by
    cases n with
    | zero =>
      exact ⟨(Sheaf.H.equiv₀ F Limits.isTerminalTop).trans
        (Γ.rightDerivedZeroIsoSelf.app F).addCommGroupIsoToAddEquiv.symm⟩
    | succ q =>
      exact Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
        (Opens.grothendieckTopology Y.carrier) ⊤ Limits.isTerminalTop F q
  obtain ⟨e⟩ := he
  let c := Γ.rightDerivedObjIsoOfResolution ι hac n
  obtain ⟨s⟩ := punctured_tilde_sections_comparison R W I.cocomplex
  let h := (HomologicalComplex.homologyFunctor _ _ n).mapIso s
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let d := ((puncturedSectionsComplex R W I.cocomplex).sc n).mapHomologyIso U
  let a := e.trans ((c ≪≫ h ≪≫ d).addCommGroupIsoToAddEquiv)
  exact ⟨a.toAddMonoidHom, a.symm.toAddMonoidHom,
    a.symm_apply_apply, a.apply_symm_apply⟩

end AlgebraicGeometry.Scheme
