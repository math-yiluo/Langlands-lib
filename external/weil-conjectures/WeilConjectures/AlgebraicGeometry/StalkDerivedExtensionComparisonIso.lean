/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso

/-! Intermediate comparison isomorphism for the derived stalk extension.
(blueprint: lem-pc-stalk-derived-extension-comparison-intermediate) -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

-- Keep the existing quantified proof-binder names unchanged.
set_option linter.unusedVariables false in
/-- Derived pullback commutes with exact stalks, with its comparison specified before
applying homology. This statement assumes a universal scalar-extension pair; it does
not construct that pair or assert invertibility of its counit on stalk complexes.

Proof: write ρ for the actual composite A → A ⊗[R] B → C. Its restriction
equation identifies ρ with the stalk map of g'. On complexes, the natural
pullback-stalk isomorphism gives extension along ρ followed by localization ≅
ordinary pullback followed by the exact derived stalk. The component of this
isomorphism is the specified tensorStalkIso: equality follows degreewise from
its defining components, so it is compatible with differentials and homotopies.
Resolve sheaf complexes by K-flat complexes. Their stalks are K-flat by the
stalk criterion. The universal scalar-extension counit and the recorded sheaf
pullback counit are invertible on these representatives. On such a representative,
define the comparison by the scalar-extension counit, the localized tensorStalkIso,
the inverse exact-stalk factor, and the inverse image of the pullback counit, in
that order. Include the quotientCompQhIso factors to pass between Q and Qh.
For a quasi-isomorphism between resolving complexes, naturality of both counits,
of the stalk factors and of the tensor-stalk identification makes this comparison
commute with its localized image. Every derived morphism can be represented by a
roof of complexes; replace its middle complex by a K-flat resolution. A common
K-flat refinement of two roofs makes their induced comparisons equal, so the
construction descends to a natural transformation. Apply the same construction
with the inverse tensor-stalk identification and reversed invertible counits.
The two composites are identities on K-flat representatives and therefore on
every derived object. This gives j. At a K-flat P, use the identity resolution;
the definition just given is precisely the displayed equation. No homology
calculation or base-flatness is used. Zero complexes, zero stalk rings and the
identity morphism satisfy the same construction without exceptions.
Source: Stacks Project, Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6;
perfect.tex, equation-bc preceding Tag 0DJ8 (Tag 0DJ7).
(blueprint: lem-pc-stalk-derived-extension-comparison-intermediate). -/
theorem exists_stalkDerivedExtensionComparisonIso (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (C z))
    ∀ (L : DerivedCategory (ModuleCat.{u} (A g' z)) ⥤
      DerivedCategory (ModuleCat.{u} (C z)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars.{u, u, u}
          ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategory
              (.up ℤ) ⋙ DerivedCategory.Qh)
      (hL : L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} (A g' z)) (.up ℤ))),
    ∃ j : comparisonDerivedStalk X (g' z) ⋙ L ≅
        derivedPullback g' ⋙ comparisonDerivedStalk X' z,
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor)
        (hcP : IsIso ((counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
        L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
            j.hom.app (DerivedCategory.Q.obj P) =
          L.map ((DerivedCategory.quotientCompQhIso _).inv.app (stalkComplex g' z P)) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P)) ≫
            DerivedCategory.Qh.map
              (((ModuleCat.extendScalars.{u, u, u}
                ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
                  (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategoryFactors
                  (.up ℤ)).hom.app
                (stalkComplex g' z P)) ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (C z))).hom.app
              (tensorComplex f f' g g' sq z P) ≫
            DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom ≫
            (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapDerivedCategoryFactors.inv.app
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ≫
            (comparisonDerivedStalk X' z).map
              (cast (by rfl)
                (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (C z))
  intro L ε hL
  obtain ⟨j, hj⟩ := exists_stalkDerivedExtensionComparisonTransformation f f' g g' sq z L ε hL
  have : IsIso j := stalkDerivedExtensionComparison_isIso f f' g g' sq z L ε hL j hj
  exact ⟨asIso j, hj⟩


end AlgebraicGeometry.SingleComplexBaseChange
