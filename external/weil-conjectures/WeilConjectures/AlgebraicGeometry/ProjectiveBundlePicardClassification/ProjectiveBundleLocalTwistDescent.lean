/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleIntegerTwistSeparation
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleRelativelyTrivialLineDescent
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundlePullbackLineReflection
import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwistIdentities
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-!
# Descent of local twists on projective bundles

## References

* EGA II, Remark 4.2.7
* Stacks Project, Tags 00AL, 00AM, 01XS, 04TN, 0BXJ
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- Compare the two pullback functors by their common right adjoint. -/
private noncomputable def pullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ Scheme.Modules.pullback f :=
  (tensorPullbackSectionAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

/-- The explicit pullback preserves the tensor unit. -/
private noncomputable def pullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (tensorPullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (pullbackComparison f).app _ ≪≫ pullbackObjUnitIso f

/-- Restrict an isomorphism of restricted global modules to a smaller open. -/
private noncomputable def restrictIso {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    {M N : X.Modules}
    (e : (tensorPullback U.ι).obj M ≅ (tensorPullback U.ι).obj N) :
    (tensorPullback V.ι).obj M ≅ (tensorPullback V.ι).obj N :=
  let c (F : X.Modules) : (tensorPullback V.ι).obj F ≅
      (tensorPullback (X.homOfLE h)).obj ((tensorPullback U.ι).obj F) :=
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj F) (X.homOfLE_ι h).symm) ≪≫
      (tensorPullbackSectionComp (X.homOfLE h) U.ι).app F
  c M ≪≫ (tensorPullback (X.homOfLE h)).mapIso e ≪≫ (c N).symm

/-- Invertibility transports across isomorphisms on pointwise open neighbourhoods. -/
private theorem invertible_of_local_iso {X : Scheme.{u}} (M N : X.Modules)
    (hN : N.IsInvertible) (U : X → X.Opens) (hU : ∀ x : X, x ∈ U x)
    (e : ∀ x : X, Nonempty ((tensorPullback (U x).ι).obj M ≅
      (tensorPullback (U x).ι).obj N)) : M.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨V, hxV, ⟨ev⟩⟩ := hN.exists_isoUnit x
    let W := V ⊓ U x
    let nunit : (tensorPullback W.ι).obj N ≅ 𝟙_ W.toScheme.Modules :=
      restrictIso (show W ≤ V from inf_le_left)
        ((pullbackComparison V.ι).app N ≪≫ ev ≪≫ (pullbackUnit V.ι).symm) ≪≫
          pullbackUnit W.ι
    exact ⟨W, ⟨hxV, hU x⟩, ⟨(pullbackComparison W.ι).symm.app M ≪≫
      restrictIso (show W ≤ U x from inf_le_right) (e x).some ≪≫ nunit⟩⟩

/-- Trivialize the base coefficient and make the degree constant simultaneously. -/
private theorem decomposition_local_integer {S P : Scheme.{u}} (p : P ⟶ S)
    (A : P.Modules) (hA : A.IsInvertible) (L : P.Modules)
    (d : LocallyConstant S ℤ) (N : S.Modules) (hN : N.IsInvertible)
    (e : L ≅ locallyConstantLineTwist A hA (d.comap p.base.hom) ⊗
      (tensorPullback p).obj N) (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((tensorPullback (p ⁻¹ᵁ U).ι).obj L ≅
        (tensorPullback (p ⁻¹ᵁ U).ι).obj (integerLinePower A hA (d s))) := by
  have : N.IsInvertible := hN
  obtain ⟨V, hsV, ⟨eV⟩⟩ := IsInvertible.exists_isoUnit (M := N) s
  let U := lineDegreeOpen d (d s) ⊓ V
  let j := (p ⁻¹ᵁ U).ι
  let eN : (tensorPullback U.ι).obj N ≅ 𝟙_ U.toScheme.Modules :=
    restrictIso (show U ≤ V from inf_le_right)
      ((pullbackComparison V.ι).app N ≪≫ eV ≪≫ (pullbackUnit V.ι).symm) ≪≫
        pullbackUnit U.ι
  let c : (tensorPullback j).obj ((tensorPullback p).obj N) ≅
      (tensorPullback (p ∣_ U)).obj ((tensorPullback U.ι).obj N) :=
    (tensorPullbackSectionComp j p).symm.app N ≪≫
      eqToIso (congrArg (fun f ↦ (tensorPullback f).obj N)
        (morphismRestrict_ι p U).symm) ≪≫
      (tensorPullbackSectionComp (p ∣_ U) U.ι).app N
  let coeff : (tensorPullback j).obj ((tensorPullback p).obj N) ≅
      𝟙_ (p ⁻¹ᵁ U).toScheme.Modules :=
    c ≪≫ (tensorPullback (p ∣_ U)).mapIso eN ≪≫ pullbackUnit (p ∣_ U)
  let tw := locallyConstantLineTwistRestrictIso A hA
    (d.comap p.base.hom) (d s) (p ⁻¹ᵁ U) (fun x hx ↦ hx.1)
  obtain ⟨tensor, _, _⟩ := module_pullback_tensor j
  exact ⟨U, ⟨rfl, hsV⟩, ⟨(tensorPullback j).mapIso e ≪≫ tensor _ _ ≪≫
    (tw ⊗ᵢ coeff) ≪≫ ρ_ _⟩⟩

/-- An invertible module that is locally on the base an integer twist of the tautological line
is a locally constant twist tensored with a pullback line, with unique degree and coefficient. -/
theorem projective_bundle_local_twist_descent (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (D : TautologicalQuotient E)
    (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (hL : L.IsInvertible)
    (hlocal : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ m : ℤ,
      Nonempty ((tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj L ≅
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj
          (integerLinePower D.line D.invertible m))) :
    ∃ (d : LocallyConstant S ℤ) (N : S.Modules),
      (N.IsInvertible ∧ Nonempty (L ≅
        locallyConstantLineTwist D.line D.invertible
          (d.comap (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.base.hom) ⊗
            (tensorPullback (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj N)) ∧
      ∀ (d' : LocallyConstant S ℤ) (N' : S.Modules),
        (N'.IsInvertible ∧ Nonempty (L ≅
          locallyConstantLineTwist D.line D.invertible
            (d'.comap (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.base.hom) ⊗
              (tensorPullback (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj N')) →
          d' = d ∧ Nonempty (N' ≅ N) := by
  classical
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  choose U hU m e using hlocal
  have agree (s t : S) (ht : t ∈ U s) : m t = m s := by
    let W := U t ⊓ U s
    let a := restrictIso (p.preimage_mono (show W ≤ U t from inf_le_left)) (e t).some
    let b := restrictIso (p.preimage_mono (show W ≤ U s from inf_le_right)) (e s).some
    exact projective_bundle_integer_twist_separation S E r hr D W t ⟨hU t, ht⟩
      (m t) (m s) ⟨a.symm ≪≫ b⟩
  let d : LocallyConstant S ℤ := ⟨m, (IsLocallyConstant.iff_exists_open m).2
    (fun s ↦ ⟨U s, (U s).isOpen, hU s, fun t ht ↦ agree s t ht⟩)⟩
  let T := locallyConstantLineTwist D.line D.invertible (d.comap p.base.hom)
  have localTwist (s : S) : Nonempty ((tensorPullback (p ⁻¹ᵁ U s).ι).obj L ≅
      (tensorPullback (p ⁻¹ᵁ U s).ι).obj T) := by
    let tw := locallyConstantLineTwistRestrictIso D.line D.invertible
      (d.comap p.base.hom) (m s) (p ⁻¹ᵁ U s)
      (fun x hx ↦ agree s (p.base x) hx)
    exact ⟨(e s).some ≪≫ tw.symm⟩
  have hT : T.IsInvertible := invertible_of_local_iso T L hL
    (fun x ↦ p ⁻¹ᵁ U (p.base x)) (fun x ↦ hU (p.base x))
    (fun x ↦ ⟨(localTwist (p.base x)).some.symm⟩)
  let inv := lineTensorInverse T hT
  let F := inv.obj ⊗ L
  have hF : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      Nonempty ((tensorPullback (p ⁻¹ᵁ V).ι).obj F ≅
        𝟙_ (p ⁻¹ᵁ V).toScheme.Modules) := by
    intro s
    let j := (p ⁻¹ᵁ U s).ι
    obtain ⟨tensor, _, _⟩ := module_pullback_tensor j
    exact ⟨U s, hU s, ⟨tensor inv.obj L ≪≫
      (Iso.refl _ ⊗ᵢ (localTwist s).some) ≪≫ (tensor inv.obj T).symm ≪≫
      (tensorPullback j).mapIso inv.leftIso ≪≫ pullbackUnit j⟩⟩
  obtain ⟨N, hN, ⟨eF⟩⟩ :=
    projective_bundle_relatively_trivial_line_descent S E r (by omega) F hF
  let presentation : L ≅ T ⊗ (tensorPullback p).obj N :=
    (λ_ L).symm ≪≫ (inv.rightIso.symm ⊗ᵢ Iso.refl L) ≪≫ α_ _ _ _ ≪≫
      (Iso.refl T ⊗ᵢ eF)
  refine ⟨d, N, ⟨hN, ⟨presentation⟩⟩, ?_⟩
  rintro d' N' ⟨hN', ⟨presentation'⟩⟩
  have hd : d' = d := by
    ext s
    obtain ⟨V, hsV, ⟨ev⟩⟩ :=
      decomposition_local_integer p D.line D.invertible L d' N' hN' presentation' s
    let W := V ⊓ U s
    let a := restrictIso (p.preimage_mono (show W ≤ V from inf_le_left)) ev
    let b := restrictIso (p.preimage_mono (show W ≤ U s from inf_le_right)) (e s).some
    exact projective_bundle_integer_twist_separation S E r hr D W s ⟨hsV, hU s⟩
      (d' s) (m s) ⟨a.symm ≪≫ b⟩
  refine ⟨hd, ?_⟩
  subst d'
  exact projective_bundle_pullback_line_reflection S E r (by omega) N' N hN' hN
    ⟨inv.fullyFaithfulTensorLeft.preimageIso (presentation'.symm ≪≫ presentation)⟩

end AlgebraicGeometry.ProjectiveBundlePicardClassification
