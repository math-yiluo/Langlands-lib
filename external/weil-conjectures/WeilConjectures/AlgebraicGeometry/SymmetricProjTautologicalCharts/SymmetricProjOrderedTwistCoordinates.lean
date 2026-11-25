/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData

/-! # Coordinate compatibility for the ordered twist line

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-coordinates).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

private theorem hom_ext_on_affine_base {S X : Scheme.{u}} (p : X ⟶ S)
    {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ V : S.affineOpens,
      (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ V.1).ι).map f =
        (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ V.1).ι).map g) : f = g := by
  apply Scheme.Modules.hom_ext_of_restrictAdjunction_unit
    (fun V : S.affineOpens ↦ p ⁻¹ᵁ V.1)
  · intro x
    obtain ⟨V, hV, hx, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      S.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (p x))
    exact ⟨⟨V, hV⟩, hx⟩
  · intro V
    let adj := Scheme.Modules.restrictAdjunction (p ⁻¹ᵁ V.1).ι
    calc
      f ≫ adj.unit.app N = adj.unit.app M ≫
          (Scheme.Modules.pushforward (p ⁻¹ᵁ V.1).ι).map
            ((Scheme.Modules.restrictFunctor (p ⁻¹ᵁ V.1).ι).map f) := adj.unit.naturality f
      _ = adj.unit.app M ≫ (Scheme.Modules.pushforward (p ⁻¹ᵁ V.1).ι).map
            ((Scheme.Modules.restrictFunctor (p ⁻¹ᵁ V.1).ι).map g) :=
        congrArg (fun k ↦ adj.unit.app M ≫ (Scheme.Modules.pushforward (p ⁻¹ᵁ V.1).ι).map k) (h V)
      _ = g ≫ adj.unit.app N := (adj.unit.naturality g).symm

/-- An affinely normalized ordered twist comparison preserves coordinates globally.

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-coordinates).

Proof: inverse images of affine base opens cover the relative Proj. The supplied
normalization says that the two maps agree after restricting to each member of
this cover. Naturality of the restriction adjunction unit transports these local
equalities to maps into the pushforward restrictions. Sheaf separatedness, in
`hom_ext_of_restrictAdjunction_unit`, then gives equality globally. This uses no
nonemptiness or positive-dimensional assumption.

The normalization hypothesis is essential: multiplying an arbitrary line
isomorphism by a nontrivial unit changes its coordinate sections.
-/
theorem ordered_twist_coordinate_compatibility (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line)
    (hNormalized :
      ∀ V : S.affineOpens, ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        ((Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient) =
      (Scheme.Modules.restrictFunctor
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1).ι).map
        (((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom)) :
    ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
      ((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom := by
  intro i
  exact hom_ext_on_affine_base
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom _ _ (fun V ↦ hNormalized V i)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
