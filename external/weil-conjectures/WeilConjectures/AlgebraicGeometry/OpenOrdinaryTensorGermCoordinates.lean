/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorStalkRingCoordinates
import WeilConjectures.AlgebraicGeometry.SemilinearTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorPureGermCoordinates
import WeilConjectures.AlgebraicGeometry.OpenSemilinearInputComplexIso

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange

-- Extensionality on pure tensors keeps tensor induction independent of the stalk constructions.
private theorem tensor_germ_hom_ext
    {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {Z : AddCommGrpCat.{u}}
    (a b : AddCommGrpCat.of (M ⊗[R] N) ⟶ Z)
    (h : ∀ m n, a (m ⊗ₜ[R] n) = b (m ⊗ₜ[R] n)) : a = b := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Compatible ordinary tensor coordinates, pinned to the actual open restriction map.

Proof: use the inverse stalk maps of the four open inclusions, transporting
endpoints by the point equalities coming from hj and the restriction squares.
The stalkMap_comp and stalkMap_congr_hom identities prove the four ring-map
compatibilities. For alpha use the additive restriction-stalk natural isomorphism,
composed with overFunctorEquiv, in every degree. Represent a scalar and a module
element by germs on a common open. The inverse stalk ring map sends a ring germ
to the germ of the inverse section-ring map. The germ_smul and
germ_restrictStalkNatIso_hom_app formulas then give alpha's semilinearity.
Naturality for P.d proves that alpha is a chain isomorphism.
Define tau on pure tensors by c tensor q mapping to eC(c) tensor alpha(q).
Semilinearity and the A-to-C ring-map compatibility prove balancedness. Its
inverse uses the inverse ring equivalence and alpha inverse; tensor induction
proves the inverse equations. Naturality for the differential gives a chain iso.
For the last equation, use the defining degreewise formula of tensorStalkIso.
Expand openPinnedTensorRestrictionIso into its four adjunction comparisons.
Their units are pinned to the pulled-back section 1 tensor s. The mate equation
for pushforward composition and the open restriction adjunction therefore sends
a restricted pure germ tensor to its ambient germ tensor. Compose with
restrictStalkNatIso, whose germ formula is the same-germ map. Both sides of the
last equation are thus equal on c tensor q, and tensor induction gives equality
on the whole module in every degree. This is a chain-level construction; it
asserts no compatibility with derived homology factors.
Empty opens have no z; top opens give the identity germ maps. Zero complexes
and zero rings obey the same formulas, without a nonzero or flatness assumption.
Source: Stacks Project, Tags 0098 and 0096; Mathlib restrictStalkNatIso and its
same-germ formulas; the pinned tensor pullback unit and composition comparisons.
(blueprint: lem-pc-open-ordinary-tensor-germ-coordinates). -/
theorem exists_openOrdinaryTensor_germ_coordinates
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
    ∃ (eR : R₀ ≃+* R₁) (eA : A₀ ≃+* A₁) (eB : B₀ ≃+* B₁) (eC : C₀ ≃+* C₁),
      eA.toRingHom.comp (algebraMap R₀ A₀) = (algebraMap R₁ A₁).comp eR.toRingHom ∧
      eB.toRingHom.comp (algebraMap R₀ B₀) = (algebraMap R₁ B₁).comp eR.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        (algebraMap A₀ (A₀ ⊗[R₀] B₀))) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          (algebraMap A₁ (A₁ ⊗[R₁] B₁))).comp eA.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        Algebra.TensorProduct.includeRight.toRingHom) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom ∧
      ∃ α : ((forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).obj K₀ ≅
          ((forget₂ (ModuleCat.{u} A₁) AddCommGrpCat.{u}).mapHomologicalComplex
            (.up ℤ)).obj K,
        (∀ (n : ℤ) (a : A₀) (q : K₀.X n),
          α.hom.f n (a • q) = eA a • (show K.X n from α.hom.f n q)) ∧
        ∃ τ : (F₀.mapHomologicalComplex (.up ℤ)).obj T₀ ≅
            (F.mapHomologicalComplex (.up ℤ)).obj T,
          (∀ (n : ℤ) (c : C₀) (q : K₀.X n),
            τ.hom.f n (c ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
                (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) =
              eC c ⊗ₜ[A₁,(algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
                (algebraMap A₁ (A₁ ⊗[R₁] B₁))] (show K.X n from α.hom.f n q)) ∧
          (∀ n : ℤ,
            τ.hom.f n ≫ F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n) =
              F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
                (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
                F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
                  (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
                γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))) := by
  intro Q₀ R₀ A₀ B₀ C₀ R₁ A₁ B₁ C₁ K₀ K T₀ T F₀ F L₀ γ
  let := leftAlgebra (f ∣_ V) j z
  let := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
  let := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
  let := leftAlgebra f g' z.val
  let := rightAlgebra f f' g g' sq z.val
  let := (tensorMap f f' g g' sq z.val).toAlgebra
  obtain ⟨eR, eA, eB, eC, hRA, hRB, hCA, hCB, heA, heC⟩ :=
    exists_openOrdinaryTensor_stalk_ring_coordinates f f' g g' sq V V' hV' j hj sq₀ z
  let hx := congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ X => k z) hj
  obtain ⟨α, hα₀, hαcoord⟩ :=
    exists_openSemilinearInputComplexIso X (f ⁻¹ᵁ V) (j z) (g' z.val) hx P
  have heA' : eA = (((f ⁻¹ᵁ V).stalkIso (j z)) ≪≫
      X.presheaf.stalkCongr (.of_eq hx)).commRingCatIsoToRingEquiv :=
    RingEquiv.toRingHom_injective heA
  subst eA
  have hα := hα₀
  have hpure := exists_openOrdinaryTensor_pure_germ_coordinates
    f f' g g' sq V V' hV' j hj sq₀ P z eC heC
  obtain ⟨τ, hτ⟩ := exists_semilinearTensorComplexIso _ _ _ eC hCA _ _ α hα
  refine ⟨eR, _, eB, eC, hRA, hRB, hCA, hCB, α, hα, τ, hτ, ?_⟩
  intro n
  apply tensor_germ_hom_ext
  intro c q
  let φ₁ := (algebraMap (A₁ ⊗[R₁] B₁) C₁).comp (algebraMap A₁ (A₁ ⊗[R₁] B₁))
  let t := F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n)
  have hq := ConcreteCategory.congr_hom (hαcoord n) q
  exact (congrArg t (hτ n c q)).trans
    ((congrArg (fun q : K.X n ↦ t (eC c ⊗ₜ[A₁,φ₁] q)) hq).trans (hpure n c q))

end AlgebraicGeometry
