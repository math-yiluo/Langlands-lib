/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtale
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-! # Ordinary cohomology of the affine line with condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-lem-wft-character-integral/lem-fd-affine-line-constant-cohomology.md and its proof.
(blueprint: lemma-integral-linear-character--2).

The coefficients are the recorded finite-subextension-valued condensed ring pulled
back from the point. Cohomology means the right derived functors of evaluation at
`X`, the terminal object of the small pro-etale site, on abelian sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The constant section with value `a` of the pulled-back condensed Qbar coefficient.
This applies the existing monoidal inverse image to the existing constant global
section and evaluates the resulting tensor-unit morphism at the integer generator.
Source: the degree-zero normalization of the affine-line cohomology lemma
(blueprint: lemma-integral-linear-character--2). -/
def condensedQbarConstantSection (X : Scheme.{v}) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : PadicAlgCl ℓ) :
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X).obj.obj
      (op (Scheme.ProEt.mk (𝟙 X))) :=
  AddCommGrpCat.uliftZMultiplesAddEquiv _
    (((constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{v + 1}
      (Scheme.ProEt.isTerminalMkId X)).homAddEquiv
        (AddCommGrpCat.of (ULift.{v + 1} ℤ))
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X)
        (Profinite.PadicAlgCl.constRingHom ℓ a)).hom)

private theorem finiteAdicH_line_subsingleton
    (K : Type v) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) (m q : ℕ) (hq : 0 < q) :
    Subsingleton (FiniteAdicH
      (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))) ℓ m q) := by
  let X := AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))
  let A := ℤ_[ℓ] ⧸ (PadicInt.powOpenAddSubgroup ℓ m : AddSubgroup ℤ_[ℓ])
  obtain ⟨e⟩ := nonempty_addEquiv_H_continuousSheaf X A q
  let eA : AddCommGrpCat.of (ULift.{v + 1} (ZMod (ℓ ^ m))) ≅
      AddCommGrpCat.of (ULift.{v + 1} A) :=
    (AddEquiv.ulift.trans ((zmodAddEquivQuotientPowOpenAddSubgroup ℓ m).trans
      AddEquiv.ulift.symm)).toAddCommGrpIso
  let e' := (Sheaf.functorH X.smallEtaleTopology q).mapIso
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).mapIso eA)
  have : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hA (a : ULift.{v + 1} (ZMod (ℓ ^ m))) : (ℓ ^ m) • a = 0 := by
    apply ULift.ext
    simp [nsmul_eq_mul]
  have hzero := AffineSpace.subsingleton_sheafH_constantSheaf_line
    (k := K) (AddCommGrpCat.of (ULift.{v + 1} (ZMod (ℓ ^ m))))
    (by simpa using pow_ne_zero m hℓ) hA q hq
  exact @Equiv.subsingleton _ _
    (e.trans e'.addCommGroupIsoToAddEquiv.symm).toEquiv hzero

private theorem finiteAdicH_line_finite
    (K : Type v) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) (m q : ℕ) :
    Finite (FiniteAdicH
      (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))) ℓ m q) := by
  cases q with
  | succ q =>
    have := finiteAdicH_line_subsingleton K ℓ hℓ m (q + 1) (by omega)
    infer_instance
  | zero =>
    let X := AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))
    have : Nonempty X :=
      ⟨(AffineSpace.zeroSection _ _).base (Classical.arbitrary (Spec (.of K)))⟩
    have := isIntegral_of_isAffine_of_isDomain X
    have : ConnectedSpace X := inferInstance
    let A := ℤ_[ℓ] ⧸ (PadicInt.powOpenAddSubgroup ℓ m : AddSubgroup ℤ_[ℓ])
    obtain ⟨e⟩ := nonempty_addEquiv_H_continuousSheaf X A 0
    have : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
    let eA : AddCommGrpCat.of (ULift.{v + 1} (ZMod (ℓ ^ m))) ≅
        AddCommGrpCat.of (ULift.{v + 1} A) :=
      (AddEquiv.ulift.trans ((zmodAddEquivQuotientPowOpenAddSubgroup ℓ m).trans
        AddEquiv.ulift.symm)).toAddCommGrpIso
    let e' := (Sheaf.functorH X.smallEtaleTopology 0).mapIso
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).mapIso eA)
    obtain ⟨e₀⟩ := X.nonempty_addEquiv_sheafH_zero_constantZMod (ℓ ^ m)
    exact Finite.of_equiv (ZMod (ℓ ^ m))
      (e.trans (e'.addCommGroupIsoToAddEquiv.symm.trans e₀)).toEquiv.symm

private theorem integralAdicH_line_subsingleton
    (K : Type v) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) (q : ℕ) (hq : 0 < q) :
    Subsingleton (IntegralAdicH
      (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))) ℓ q) := by
  let X := AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))
  apply subsingleton_of_forall_eq 0
  intro x
  apply eq_zero_of_forall_reduction_eq_zero X ℓ q
    (fun m j _ ↦ finiteAdicH_line_finite K ℓ hℓ m j) x
  intro m
  have := finiteAdicH_line_subsingleton K ℓ hℓ m q hq
  exact Subsingleton.elim _ _

private theorem adicConstantH_line_subsingleton
    (K : Type v) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) (q : ℕ) (hq : 0 < q) :
    Subsingleton (AdicConstantH ℓ
      (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))) q) := by
  let X := AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))
  have := integralAdicH_line_subsingleton K ℓ hℓ q hq
  exact (isBaseChange_integralToAdicConstantH ℓ X q).equiv.toEquiv.symm.subsingleton

private instance pointAdditive (X : Scheme.{v}) : (upperStarFromPoint X).Additive := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (upperStarFromPointAdjunction X).isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (upperStarFromPointAdjunction X).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

-- The monoidal adjunction comparison unfolds both point and scheme inverse images.
private theorem continuousMapComparison_constants
    (X : Scheme.{v}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (t : T) :
    MonObj.Γ.map (continuousMapComparison X T)
      (MonObj.Γ.mapFunctor (upperStarFromPoint X) (Profinite.continuousMapConstRingHom T t)) =
        continuousMapSectionRingHom X T (ContinuousMap.const X t) := by
  open MonObj Functor.LaxMonoidal in
    refine Γ.ext ?_
    rw [Γ.map_hom, Γ.mapFunctor_hom, Category.assoc]
    refine (upperStarFromPointAdjunction X).ε_comp_map_comp_homEquiv_symm_eq _ _ _ ?_
    refine Sheaf.unitHomEval_injective (J := coherentTopology Profinite.{v})
      Profinite.isTerminalPUnit _ ?_
    have hs : Sheaf.unitHomEval (J := coherentTopology Profinite.{v})
        (Profinite.of PUnit.{v + 1}) (Profinite.continuousMapConstRingHom T t).hom =
          ULift.up (ContinuousMap.const (Profinite.of PUnit.{v + 1}) t) :=
      Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{v})
        (Profinite.of PUnit.{v + 1}) (Profinite.continuousMapRingSheaf.{v} T)
        (Profinite.continuousMapConstSectionRingHom.{v} T) (fun _ _ ↦ rfl) t
    rw [Sheaf.unitHomEval_comp (J := coherentTopology Profinite.{v}), hs]
    rw [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Category.assoc, ← Functor.map_comp]
    erw [Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map
      (J := coherentTopology Profinite.{v}) (K := Scheme.ProEt.topology specZ.{v})
      (T := Profinite.of PUnit.{v + 1}) profiniteToProEt.{v}
      (Scheme.ProEt.isTerminalMkId specZ.{v})]
    rw [unitHomEval_ε_comp_lowerStar_map (toSpecZ X),
      unitHomEval_continuousMapSectionRingHom]
    rfl

private theorem subfieldSection_constants
    (X : Scheme.{v}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (a : E) :
    MonObj.Γ.mapFunctor (upperStarFromPoint X) (Profinite.continuousMapConstRingHom E a) =
      subfieldSectionRingHom ℓ X E (ContinuousMap.const X a) := by
  apply MonObj.Γ.ext
  apply (cancel_mono (continuousMapComparison X E)).1
  have h := congrArg MonObj.Γ.hom (continuousMapComparison_constants X E a)
  simpa [subfieldSectionRingHom, MonObj.Γ.map_hom, Category.assoc] using h

private theorem condensedQbar_constants_subfield
    (X : Scheme.{v}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (a : E) :
    MonObj.Γ.mapFunctor (upperStarFromPoint X)
        (Profinite.PadicAlgCl.constRingHom ℓ (a : PadicAlgCl ℓ)) =
      subfieldToPadicAlgClSection ℓ X E
        (subfieldSectionRingHom ℓ X E (ContinuousMap.const X a)) := by
  have hc : MonObj.Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      (Profinite.continuousMapConstRingHom E a) =
        Profinite.PadicAlgCl.constRingHom ℓ (a : PadicAlgCl ℓ) :=
    Sheaf.Γ_map_ringHomΓSheafCompose _
      (Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E) _
      (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  rw [← hc, MonObj.Γ.mapFunctor_map, subfieldSection_constants]

private theorem condensedQbar_constants_bijective
    (X : Scheme.{v}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective ((MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
      (Profinite.PadicAlgCl.constRingHom ℓ)) := by
  let c := (MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
    (Profinite.PadicAlgCl.constRingHom ℓ)
  have : Nontrivial (MonObj.Γ (padicAlgClRingObj X ℓ)) :=
    (padicAlgClSectionRingEquiv ℓ X).symm.toEquiv.nontrivial
  refine ⟨c.injective, ?_⟩
  intro s
  obtain ⟨E, f, rfl⟩ := exists_subfieldToPadicAlgClSection_eq s
  let x := Classical.arbitrary X
  refine ⟨(f x : PadicAlgCl ℓ), ?_⟩
  simp only [RingHom.comp_apply]
  rw [condensedQbar_constants_subfield]
  congr 2
  exact ContinuousMap.ext (fun y ↦
    (TotallyDisconnectedSpace.eq_of_continuous f f.continuous y x).symm)

private def condensedQbarIsoAdic (X : Scheme.{v}) (ℓ : ℕ) [Fact ℓ.Prime] :
    condensedRingObj (Profinite.padicAlgClRingObj ℓ) X ≅ adicConstantSheafAb ℓ X := by
  let e : Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X ≅
      padicSubfieldSheafFunctor X ℓ ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{v + 1} Ab.{v + 1}) :=
    NatIso.ofComponents (fun E ↦ asIso (continuousMapComparison X E)) (fun f ↦ by
      exact continuousMapComparison_naturality X
        (IntermediateField.inclusion (leOfHom f)).toRingHom
        (continuous_subtype_val.subtype_mk _))
  exact (isColimitPadicAlgClRingObjCocone X ℓ).coconePointsIsoOfNatIso
    (isColimitPadicAlgClSheafCocone X ℓ) e ≪≫ padicAlgClSheafIsoAdicConstantSheaf X ℓ

private theorem condensedQbar_line_isZero
    (K : Type v) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) (q : ℕ) (hq : 0 < q) :
    IsZero (((Sheaf.sectionsFunctorAt
      (Scheme.ProEt.topology (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))
      (Scheme.ProEt.mk (𝟙 (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))).rightDerived
        q).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))) := by
  let X := AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))
  have hz := adicConstantH_line_subsingleton K ℓ hℓ q hq
  let e := (Sheaf.functorH (Scheme.ProEt.topology X) q).mapIso (condensedQbarIsoAdic X ℓ)
  apply (Sheaf.subsingleton_H_iff_isZero_rightDerived (Scheme.ProEt.topology X)
    (Scheme.ProEt.isTerminalMkId X) q
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).1
  exact @Equiv.subsingleton _ _ e.addCommGroupIsoToAddEquiv.toEquiv hz

/-- Ordinary constant cohomology of the geometric affine line, including normalization
by constant sections in degree zero.

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-lem-wft-character-integral/lem-fd-affine-line-constant-cohomology.md and its proof.
(blueprint: lemma-integral-linear-character--2).

Proof: Put X = Spec K[t]. The source-library affine-line Kummer theorem gives
vanishing for every finite constant group killed by a power of ell. Compare the
finite quotients of Z_ell with Z/ell^m and transfer their cohomology from the
etale site to the pro-etale site. In degree zero these groups are finite because
X is connected; in positive degree they vanish. Integral cohomology classes are
detected by these finite reductions, since the preceding finite-level groups
are finite. Thus positive-degree Z_ell cohomology vanishes. The qcqs constant
cohomology base-change theorem then gives the same vanishing with Qbar_ell.
This argument works in every characteristic in which ell is invertible.

To identify the coefficient models, apply the continuous-function comparison
to each finite intermediate field. Its naturality and the two colimit universal
properties identify the pulled-back condensed coefficient with the sheafification
of finite-subextension-valued functions; the existing locally finite comparison
identifies the latter with the adic constant sheaf. Transport cohomology along
this isomorphism and use cohomology as right-derived terminal evaluation.

For degree zero, global sections of the pulled-back condensed coefficient on
qcqs X are continuous functions valued in a finite intermediate field. Every
such function is constant on connected X. The monoidal point adjunction sends
the given condensed constant to the corresponding continuous constant: evaluate
the adjunction identity at the terminal profinite set. Naturality under finite
field inclusions then gives precisely the constant map in the statement.
This map is a bijection, hence an additive equivalence; compose its inverse with
the inverse of the canonical map to the zeroth right derived functor. The
normalization is the inverse-equivalence identity. -/
theorem affineLine_condensedQbar_cohomology
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (K : Type v) [Field K] [Algebra k K] [IsAlgClosure k K] :
    (∃ e :
      (((Sheaf.sectionsFunctorAt
        (Scheme.ProEt.topology (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))
        (Scheme.ProEt.mk (𝟙 (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))).rightDerived
          0).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))) ≃+ PadicAlgCl ℓ,
      ∀ a : PadicAlgCl ℓ,
        e (((Sheaf.sectionsFunctorAt
          (Scheme.ProEt.topology (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))
          (Scheme.ProEt.mk
            (𝟙 (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))).toRightDerivedZero.app
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
                (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))
                  (condensedQbarConstantSection
                    (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))) ℓ a)) = a) ∧
    ∀ (q : ℕ), 0 < q →
      IsZero (((Sheaf.sectionsFunctorAt
        (Scheme.ProEt.topology (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))
        (Scheme.ProEt.mk (𝟙 (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))).rightDerived
          q).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))) := by
  have _ := hk
  let X := AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Nonempty X :=
    ⟨(AffineSpace.zeroSection _ _).base (Classical.arbitrary (Spec (.of K)))⟩
  have := isIntegral_of_isAffine_of_isDomain X
  have : ConnectedSpace X := inferInstance
  have hℓK : (ℓ : K) ≠ 0 := by
    exact_mod_cast ((map_ne_zero (algebraMap k K)).2 hℓ.ne_zero)
  constructor
  · let R := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
    let c : PadicAlgCl ℓ ≃+ MonObj.Γ R :=
      (RingEquiv.ofBijective
        ((MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
          (Profinite.PadicAlgCl.constRingHom ℓ))
        (condensedQbar_constants_bijective X ℓ)).toAddEquiv
    let s : MonObj.Γ R ≃+ R.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
      ((constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{v + 1}
        (Scheme.ProEt.isTerminalMkId X)).homAddEquiv _ R).trans
          (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    let d := (asIso ((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X)
      (Scheme.ProEt.mk (𝟙 X))).toRightDerivedZero.app R)).addCommGroupIsoToAddEquiv
    refine ⟨((c.trans s).trans d).symm, fun a ↦ ?_⟩
    exact ((c.trans s).trans d).symm_apply_apply a
  · exact condensedQbar_line_isZero K ℓ hℓK

end AlgebraicGeometry.ProEtale
