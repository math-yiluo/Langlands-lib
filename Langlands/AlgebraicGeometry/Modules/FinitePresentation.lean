import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Local finite presentations and finite affine sections

The local finite-presentation predicate is Mathlib's
`SheafOfModules.IsFinitePresentation`, based on finite free presentations
on an open cover. This file supplies its affine finite-generation consequence
without any noetherian hypothesis.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- Evaluation of a finite free module sheaf is the corresponding finite power
of the ring of sections. -/
def freeSectionsIso (X : Scheme.{u}) (I : Type u) [Finite I] (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj
        (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ModuleCat.of Γ(X, U) (I → Γ(X, U)) := by
  letI := Fintype.ofFinite I
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let : E.Additive := inferInstanceAs
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)).Additive)
  let e := Fintype.equivFin I
  exact E.mapIso (Sigma.reindex e
      (fun _ : Fin (Fintype.card I) => SheafOfModules.unit X.ringCatSheaf)) ≪≫
    PreservesCoproduct.iso E
      (fun _ : Fin (Fintype.card I) => SheafOfModules.unit X.ringCatSheaf) ≪≫
    (biproduct.isoCoproduct
      (fun _ : Fin (Fintype.card I) => E.obj (SheafOfModules.unit X.ringCatSheaf))).symm ≪≫
    ModuleCat.biproductIsoPi _ ≪≫
    (LinearEquiv.piCongrLeft Γ(X, U) (fun _ : I => Γ(X, U)) e.symm).toModuleIso

/-- Finite free module sheaves have finite sections on every affine open. -/
lemma hasFiniteAffineSections_free (X : Scheme.{u}) (I : Type u) [Finite I] :
    HasFiniteAffineSections (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  intro U
  exact Module.Finite.equiv (freeSectionsIso X I U.1).symm.toLinearEquiv

/-- Generators on an over-site give actual generators on the open subscheme. -/
def generatingSectionsRestrict (M : X.Modules) (U : X.Opens)
    (g : (M.over U).GeneratingSections) : (M.restrict U.ι).GeneratingSections :=
  (g.map (Scheme.Modules.overEquiv U).functor
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).ofEpi
      ((Scheme.Modules.overFunctorEquiv U).app M).hom

instance (M : X.Modules) (U : X.Opens)
    (g : (M.over U).GeneratingSections) [g.IsFiniteType] :
    (generatingSectionsRestrict M U g).IsFiniteType := by
  dsimp [generatingSectionsRestrict]
  infer_instance

/-- A quasi-coherent module sheaf of finite type has finitely generated
sections on every affine open, over an arbitrary scheme. -/
lemma hasFiniteAffineSections_of_isFiniteType (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    HasFiniteAffineSections M := by
  obtain ⟨g, hg⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  apply HasLocallyFiniteSections.finiteAffineSections
  apply HasLocallyFiniteSections.of_locally_finiteAffineSections
  intro x
  have hx : x ∈ ⨆ i, g.X i :=
    (_root_.Opens.coversTop_iff X g.X).mp g.coversTop ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have : (g.generators i).IsFiniteType := hg.isFiniteType i
  let O : X.Opens := g.X i
  let G := generatingSectionsRestrict M O (g.generators i)
  have : Epi G.π := G.epi
  exact ⟨O, hxi, HasFiniteAffineSections.of_epi G.π
    (hasFiniteAffineSections_free O.toScheme G.I)⟩

/-- Local finite presentation implies finite affine sections without a
noetherian assumption on the scheme or the test base. -/
lemma hasFiniteAffineSections_of_isFinitePresentation (M : X.Modules)
    [M.IsFinitePresentation] : HasFiniteAffineSections M :=
  hasFiniteAffineSections_of_isFiniteType M

end Langlands.AlgebraicGeometry.Modules
