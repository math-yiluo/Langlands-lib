/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData

/-!
# Construct an ordered affine comparison from its chart witnesses

This constructor isolates the conversion to the existing comparison predicate.
Source: Stacks Project, Constructions, Tags 01OE and 01OB.
(blueprint: lem-trf-affine-free-comparison-constructor).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison Proj.twist Proj.unitToTwist Proj.map
  RelativeProjectiveSpace.algebra

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem comparisonLogic {α δ ε θ : Type u}
    (P Q R H : α → Prop)
    (C T : (a : α) → H a → δ → Prop)
    (K N : ε → Prop) (D : (d : ε) → K d → θ → Prop) (J : δ → θ → Prop)
    (a : α) (hp : P a) (hq : Q a) (hr : R a) (h : H a) (c : δ)
    (hc : C a h c) (ht : T a h c) (d : ε) (k : K d) (f : θ)
    (hn : N d) (hd : D d k f) (hj : J c f) :
    ∃ a, P a ∧ Q a ∧ R a ∧ ∃ (h : H a) (c : δ), C a h c ∧ T a h c ∧
      ∃ (d : ε) (k : K d) (f : θ), N d ∧ D d k f ∧ J c f :=
  ⟨a, hp, hq, hr, h, c, hc, ht, d, k, f, hn, hd, hj⟩

/-- The explicit ordered polynomial, twist and relative-chart witnesses give the affine
comparison predicate with precisely those witnesses.

Source: Stacks Project, Constructions, Tags 01OE and 01OB; the explicit interface is
`ProjectiveBundleQuotientGeometry.AffineFreeComparison`.
(blueprint: lem-trf-affine-free-comparison-constructor).

Proof: Unfold AffineFreeComparison, choose beta, its irrelevant-ideal witness and eC,
then gamma, its irrelevant-ideal witness and eR. Insert the supplied bijectivity,
coefficient, ordered-variable, Proj-map, twist and relative-chart identities in the
order of the conjunctions. The polynomial grading is the specified Mathlib grading.
No nonemptiness or nonzero-ring hypothesis is used. -/
theorem affineFreeComparison_mk {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] {r : ℕ} (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r) (V : S.affineOpens)
    (β : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
    (hbij : Function.Bijective β)
    (hC : ∀ x : Γ(S, V.1), β (MvPolynomial.C x) = algebraMap Γ(S, V.1)
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) x)
    (hX : ∀ i : ULift.{u} (Fin (r + 1)), β (MvPolynomial.X i) =
      SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))
        (b.hom.app V.1 ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app
          (op V.1) (1 : Γ(S, V.1)))))
    (hβ : HomogeneousIdeal.irrelevant
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map β)
    (eC : Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≅
      Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
    (heC : eC.hom = Proj.map β hβ)
    (ht : ∃ t : (Scheme.Modules.tensorPullback eC.hom).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) 1) ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1,
        ∀ (s : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
          (hs : s ∈ MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1) 1),
          (Scheme.Modules.tensorPullback eC.hom).map (Proj.unitToTwist
            (𝒜 := MvPolynomial.homogeneousSubmodule
              (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) hs) ≫ t.hom =
            ((Scheme.Modules.boundaryPullbackComparison eC.hom).app
                (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eC.hom).hom ≫
              Proj.unitToTwist
                (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
                (β.map_mem hs))
    (γ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (RelativeProjectiveSpace.algebra S r).sectionGrade V)
    (hγ : HomogeneousIdeal.irrelevant
        ((RelativeProjectiveSpace.algebra S r).sectionGrade V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map γ)
    (eR : (RelativeProjectiveSpace.algebra S r).localProj V ≅
      Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
    (hnorm : ∀ x, γ x = RelativeProjectiveSpace.affinePolynomialEquiv S r V
      (MvPolynomial.rename (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down) x))
    (heR : eR.hom = Proj.map γ hγ)
    (hchart : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ≫ eRel.hom =
      eC.hom ≫ eR.inv ≫ ((RelativeProjectiveSpace.construction S r).restrictionIso V).inv ≫
        (RelativeProjectiveSpace.π S r ⁻¹ᵁ V.1).ι) :
    ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V := by
  let : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) :=
    MvPolynomial.gradedAlgebra
  exact comparisonLogic
    (α := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
          (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
    (δ := Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≅
          Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
    (ε := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
          (RelativeProjectiveSpace.algebra S r).sectionGrade V)
    (θ := (RelativeProjectiveSpace.algebra S r).localProj V ≅
          Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
    (fun β ↦ Function.Bijective β)
    (fun β ↦ ∀ x : Γ(S, V.1), β (MvPolynomial.C x) = algebraMap Γ(S, V.1)
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) x)
    (fun β ↦ ∀ i : ULift.{u} (Fin (r + 1)), β (MvPolynomial.X i) =
          SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))
            (b.hom.app V.1 ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app
              (op V.1) (1 : Γ(S, V.1)))))
    (fun β ↦ HomogeneousIdeal.irrelevant
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map β)
    (fun β hβ eC ↦ eC.hom = Proj.map β hβ)
    (fun β _ eC ↦ ∃ t : (Scheme.Modules.tensorPullback eC.hom).obj
              (Proj.twist (MvPolynomial.homogeneousSubmodule
                (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) 1) ≅
              Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1,
            ∀ (s : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
              (hs : s ∈ MvPolynomial.homogeneousSubmodule
                (ULift.{u} (Fin (r + 1))) Γ(S, V.1) 1),
              (Scheme.Modules.tensorPullback eC.hom).map (Proj.unitToTwist
                (𝒜 := MvPolynomial.homogeneousSubmodule
                  (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) hs) ≫ t.hom =
                ((Scheme.Modules.boundaryPullbackComparison eC.hom).app
                    (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eC.hom).hom ≫
                  Proj.unitToTwist
                    (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
                    (β.map_mem hs))
    (fun γ ↦ HomogeneousIdeal.irrelevant
            ((RelativeProjectiveSpace.algebra S r).sectionGrade V) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map γ)
    (fun γ ↦ ∀ x, γ x = RelativeProjectiveSpace.affinePolynomialEquiv S r V
          (MvPolynomial.rename (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down) x))
    (fun γ hγ eR ↦ eR.hom = Proj.map γ hγ)
    (fun eC eR ↦ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ≫ eRel.hom =
          eC.hom ≫ eR.inv ≫ ((RelativeProjectiveSpace.construction S r).restrictionIso V).inv ≫
            (RelativeProjectiveSpace.π S r ⁻¹ᵁ V.1).ι)
    β hbij hC hX hβ eC heC ht γ hγ eR hnorm heR hchart

end AlgebraicGeometry.SymmetricProjTautologicalCharts
