/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorPureGermCoordinatesCanonical

/-! # The pinned open restriction equation on pure germ tensors

Source: Stacks Project, Tags 0098 and 0096.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
set_option linter.style.longLine false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange
/-- The pinned restriction comparison agrees with canonical stalk coordinates on pure tensors.

Proof: expand tensorStalkIso using its specified tensor-pullback stalk components.
Expand openPinnedTensorRestrictionIso into its four pinned adjunction factors.
The tensor-pullback unit takes a section s to 1 tensor s. The unit compatibility
for the pullback-composition mate, and then the restriction adjunction, identify
its inverse comparison on these generators with restriction of the same section.
The hom of restrictStalkNatIso takes a restricted section germ to the ambient
section germ. Its input component followed by stalkCongr is precisely the input
coordinate written below, and stalkIso is the corresponding output ring coordinate.
Thus the displayed equation holds for c = 1 and a section germ q. Every stalk
module element is a section germ, so this covers all q. For arbitrary c, linearity
of the tensor-stalk and pinned comparison maps, and semilinearity of the output
restriction coordinate with its inverse inclusion ring map, multiply this identity
by the scalar c to obtain the displayed equation. Point transport by hj is handled
by equality induction. This is a generator calculation only: it neither constructs
ring equivalences nor input or tensor-complex isomorphisms. Empty opens have no z;
zero rings, zero complexes and negative degrees require no additional hypothesis.
Source: Stacks Project, Tags 0098 and 0096; the pinned pullback composition mate
and Mathlib's germ_restrictStalkNatIso_hom_app formula.
(blueprint: lem-pc-open-ordinary-tensor-pure-germ-coordinates). -/
theorem exists_openOrdinaryTensor_pure_germ_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let R₀ := R (f ∣_ V) j z
    let A₀ := A j z
    let B₀ := B (f' ∣_ V') z
    let C₀ := C z
    let R₁ := R f g' z.val
    let A₁ := A g' z.val
    let B₁ := B f' z.val
    let C₁ := C z.val
    letI := leftAlgebra (f ∣_ V) j z
    letI := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
    letI := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
    letI := leftAlgebra f g' z.val
    letI := rightAlgebra f f' g g' sq z.val
    letI := (tensorMap f f' g g' sq z.val).toAlgebra
    let K₀ := stalkComplex j z Q₀
    let K := stalkComplex g' z.val P
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    let Lᵢ := RingedSpace.moduleStalkFunctor (f ⁻¹ᵁ V).toScheme.toRingedSpace (j z)
    let Fᵢ := forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}
    let γᵢ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V))
        (Lᵢ ⋙ Fᵢ) ≪≫ Scheme.Modules.restrictStalkNatIso (f ⁻¹ᵁ V).ι (j z)
    let hx := congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ X => k z) hj
    ∀ (eC : C₀ ≃+* C₁),
      eC.toRingHom = ((f' ⁻¹ᵁ V').stalkIso z).hom.hom →
        ∀ (n : ℤ) (c : C₀) (q : K₀.X n),
          F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n)
              (eC c ⊗ₜ[A₁,(algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
                (algebraMap A₁ (A₁ ⊗[R₁] B₁))] (show K.X n from
                  (γᵢ.hom.app (P.X n) ≫
                    ((show X.Modules from P.X n).presheaf.stalkCongr (.of_eq hx)).hom) q)) =
            (F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
                (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
              F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
                (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
              γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n)))
                (c ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
                  (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) := by
  dsimp
  intros eC heC n c q
  have heq : eC = ((f' ⁻¹ᵁ V').stalkIso z).commRingCatIsoToRingEquiv := by
    apply RingEquiv.ext
    intro x
    exact congrArg (fun h => h x) heC
  subst eC
  exact openOrdinaryTensor_pure_germ_coordinates_linear_extension f f' g g' sq
    V V' hV' j hj sq₀ P z n c q

end AlgebraicGeometry
