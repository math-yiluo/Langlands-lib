/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import WeilConjectures.AlgebraicGeometry.LocalStrictPerfectStalkProjectiveModel
import WeilConjectures.AlgebraicGeometry.AbelianVariety.StalkFreeResidueCohomologyComparison
import Mathlib.RingTheory.LocalRing.Module

/-! # Strictly perfect stalks and derived residue cohomology

Source: Stacks Project, Tags 0BCD, 08EB and 06YB.
(blueprint: lem-sc-strict-perfect-stalk-fiber-data).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- The stalk of a locally strictly perfect object is pseudo-coherent, and any finite-free
representative of it computes the derived residue fibre.

Source: Stacks Project, Tag 0BCD, local-ring paragraph; Tags 08EB and 06YB.
(blueprint: lem-sc-strict-perfect-stalk-fiber-data).

Proof:
1. Choose the strictly perfect representative P on V from hlocal. Restriction to V
   followed by its stalk at x agrees with taking the stalk on X, since neighbourhoods
   contained in V are cofinal. Stalks are exact, hence preserve quasi-isomorphisms and
   derived isomorphisms. Apply this to eG and the comparison of P with E restricted to V.
2. The stalk of a rank-m free sheaf is the free stalk module of rank m. Apply stalks to
   the retractions in IsStrictlyPerfect: the terms of the resulting bounded complex
   are finite projective over the local ring O_X,x, hence finite free. Its bounds are
   preserved because stalks preserve zero objects. This gives hK.
3. The finite-free representative chosen by hK is bounded above, hence K-flat. Termwise
   extension along O_X,x -> kappa(x) computes its derived residue tensor product.
   Resolve G by a K-flat sheaf complex. Its stalk is K-flat, and the tensor-pullback
   stalk formula identifies its residue pullback with residue extension of its stalk.
   Sections on the one-point residue spectrum are exact. Derived invariance of
   residue tensor therefore identifies the chosen model's degree-i homology with
   derivedFiberCohomology X E i x. This identification is linear over
   kappa(x) = IsLocalRing.ResidueField O_X,x. Transport hfin across the linear
   isomorphism, and use invariance of finrank to obtain the displayed equality.
The computation concerns every bounded-above finite-free representative of the same
derived object: K-flatness makes residue cohomology invariant under its derived comparison.
It therefore applies to Classical.choose hK. No rank-minimal model is constructed here.
-/
theorem strictPerfect_stalk_fiberData
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P))
    (hfin : ∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x)) :
    ∃ hK : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)),
      (∀ i : ℤ, Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i)) ∧
      (∀ i : ℤ, derivedFiberBetti X E i x =
        Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
          ((((ModuleCat.extendScalars
            (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i)) := by
  classical
  obtain ⟨L, a, b, hbound, hterms, eL⟩ :=
    exists_localStrictPerfect_stalk_projective_model X E x G eG hlocal
  have hb : L.IsStrictlyLE b := (L.isStrictlyLE_iff b).2
    (fun j hj ↦ hbound j (Or.inr hj))
  have hfree (j : ℤ) : Module.Free (X.presheaf.stalk x) (L.X j) := by
    have := (hterms j).1
    have := (hterms j).2
    exact Module.free_of_flat_of_isLocalRing
  have hK : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)) :=
    ⟨L, b, hb, fun j ↦ ⟨hfree j, (hterms j).1⟩, eL⟩
  obtain ⟨c, hc, hcterms, ⟨ec⟩⟩ := Classical.choose_spec hK
  have hcomparison (i : ℤ) :=
    nonempty_stalkFree_residueCohomology_linearEquiv X E x G eG
      (Classical.choose hK) c hc (fun j ↦ (hcterms j).1) ec i
  refine ⟨hK, ?_, ?_⟩
  · intro i
    have : Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (derivedFiberCohomology X E i x) := hfin i
    exact Module.Finite.equiv (Classical.choice (hcomparison i))
  · intro i
    exact (Classical.choice (hcomparison i)).finrank_eq

end
end AlgebraicGeometry.Scheme
