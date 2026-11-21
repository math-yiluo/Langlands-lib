import Langlands.Shimura.PEL.HarrisTaylorCMDvrPolarizationBundle
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordProof
import Langlands.AlgebraicGeometry.Picard.AffineMumfordBaseChange
import Langlands.AlgebraicGeometry.Picard.MumfordMapPicardClass
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordMapIsogeny
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AbelianScheme.FiberwiseIsogeny
import Langlands.GroupScheme.Reductive.DvrFpqcIsogenyReduction

/-! # Extending a generic polarization after doubling over a DVR -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

private theorem rosatiPrerequisites (P : Prerequisites.{0}) : Rosati.Prerequisites.{0} :=
  ⟨P.preservation, P.composition, P.unitCoherence, P.associativity, P.comparison,
    P.symmetry, P.stability, P.square, P.universality⟩

private def rosatiDual {S : Scheme.{0}} {A : AbelianScheme S} (W : DualWitness A) :
    Rosati.DualData A :=
  ⟨W.hasDual, W.geometry, W.inverseBundle, W.evaluation⟩

private theorem dualPullback_nsmul (P : Prerequisites.{0}) {S T : Scheme.{0}}
    (b : T ⟶ S) {A : AbelianScheme S} (W : DualWitness A)
    (W' : DualWitness ((baseChange b).obj A)) (n : ℕ) (f : A ⟶ W.dual P) :
    W.pullbackMap P b W' (n • f) = n • W.pullbackMap P b W' f := by
  unfold DualWitness.pullbackMap
  rw [Functor.map_nsmul, Preadditive.nsmul_comp]

section Mumford

variable (P : Prerequisites.{0}) {S T : Scheme.{0}} (b : T ⟶ S)
  (A : AbelianScheme S) (W : DualWitness A) (L : LineBundle A.X.left) (N : LineBundle S)
  (eN : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) N.obj ≅
    structureSheaf S)
  (M : LineBundle A.X.left)
  (eM : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
    (unitSection_comp A) L N eN).obj.carrier M.obj ≅ structureSheaf A.X.left)

local notation "AK" => Functor.obj (baseChange b) A
local notation "p" => pullback.fst A.X.hom b
local notation "μ" => mumfordSchemeMapOfLineBundle P.preservation A L N eN M eM P.square W.hasDual

set_option maxHeartbeats 1600000 in
private theorem dualBaseChangeMap_mumford :
    dualBaseChangeMap A W.hasDual P.universality b μ =
      mumfordSchemeMapOfLineBundle P.preservation AK ((LineBundle.pullback p).obj L)
        ((LineBundle.pullback b).obj N) (baseChangeUnitEvaluation b A P.preservation L N eN)
        ((LineBundle.pullback p).obj M)
        (baseChangeNormalizedEvaluation b A P.preservation L N eN M eM) P.square
        (hasDualScheme_baseChange P.universality b A W.hasDual) := by
  rw [eq_mumfordSchemeMapOfLineBundle_iff]
  let q := baseChangeFamilySpaceMap b A A.X
  let e := dualBaseChangeMapPoincareForgetIso b P.universality A W.hasDual μ
  let eN' := baseChangeUnitEvaluation b A P.preservation L N eN
  let eM' := baseChangeNormalizedEvaluation b A P.preservation L N eN M eM
  exact RigidifiedLineBundle.nonempty_iso_of_forget_iso P.preservation
    ((relativeProjection (AK).X.hom).app (AK).X)
    (relativeSection_projection (AK).X.hom (unitSection AK) (unitSection_comp AK) (AK).X)
    (e ≪≫ (LineBundle.pullback q).mapIso
      ((RigidifiedLineBundle.forget _).mapIso
        (mumfordSchemeMapOfLineBundlePullbackIso P.preservation A L N eN M eM
          P.square W.hasDual) ≪≫
        eqToIso (mumfordFamilyOfLineBundle_forget P.preservation A L N eN M eM)) ≪≫
      baseChangeMumfordBundleIso b A P.preservation L N M ≪≫
      eqToIso (mumfordFamilyOfLineBundle_forget P.preservation AK _ _ eN' _ eM').symm)

end Mumford

set_option maxHeartbeats 1800000 in
private theorem fieldMumford_eq_of_bundle_iso (P : Prerequisites.{0}) (K : Type) [Field K]
    (A : AbelianScheme (Spec (.of K))) (W : DualWitness A) {L L' : LineBundle A.X.left}
    (e : L ≅ L')
    (N : LineBundle (Spec (.of K)))
    (eN : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) N.obj ≅
      structureSheaf (Spec (.of K)))
    (M : LineBundle A.X.left)
    (eM : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L N eN).obj.carrier M.obj ≅ structureSheaf A.X.left)
    (N' : LineBundle (Spec (.of K)))
    (eN' : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L'.obj) N'.obj ≅
      structureSheaf (Spec (.of K)))
    (M' : LineBundle A.X.left)
    (eM' : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L' N' eN').obj.carrier M'.obj ≅ structureSheaf A.X.left) :
    mumfordSchemeMapOfLineBundle P.preservation A L N eN M eM P.square W.hasDual =
      mumfordSchemeMapOfLineBundle P.preservation A L' N' eN' M' eM' P.square W.hasDual := by
  let R := rosatiPrerequisites P
  let D := rosatiDual W
  apply MumfordPicardClass.pointClass_injective R A D A.X
  rw [MumfordPicardClass.pointClass_mumfordSchemeMapOfLineBundle R A D L N eN M eM,
    MumfordPicardClass.pointClass_mumfordSchemeMapOfLineBundle R A D L' N' eN' M' eM',
    MumfordPicardClass.classOf_mumfordFamily R K A L N eN M eM,
    MumfordPicardClass.classOf_mumfordFamily R K A L' N' eN' M' eM',
    (LineBundle.classOf_eq_iff_iso L L').mpr ⟨e⟩]

section Isogeny

variable (P : Prerequisites.{0})

private theorem isIsogeny_of_ample_mumford_algClosed (K : Type) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (.of K))) (W : DualWitness A) (f : A ⟶ W.dual P)
    (h : HasAmpleMumfordPresentation P.preservation P.square A W.hasDual (W.parameterMap P f)) :
    IsIsogeny f := by
  obtain ⟨L, N, eN, M, eM, hL, he⟩ := h
  exact AmpleMumfordIsogeny.isIsogeny (rosatiPrerequisites P) K A (rosatiDual W) f
    L N eN M eM hL he

private theorem isIsogeny_of_ample_mumford_field (K : Type) [Field K]
    (A : AbelianScheme (Spec (.of K))) (W : DualWitness A) (f : A ⟶ W.dual P)
    (h : HasAmpleMumfordPresentation P.preservation P.square A W.hasDual (W.parameterMap P f)) :
    IsIsogeny f := by
  let Ω := AlgebraicClosure K
  let t : Spec (.of Ω) ⟶ Spec (.of K) := Spec.algebraMap K Ω
  let WΩ := W.pullback P t
  let bt := W.baseChangeIso P t WΩ
  have ht := hasAmpleMumfordPresentation_baseChange t A P.preservation P.square P.universality
    W.hasDual (W.parameterMap P f) h
  unfold HasAmpleMumfordAfterBaseChange at ht
  rw [← W.parameterMap_pullbackMap P t WΩ f] at ht
  have hΩ := isIsogeny_of_ample_mumford_algClosed P Ω ((baseChange t).obj A) WΩ
    (W.pullbackMap P t WΩ f) ht
  have hbc := hΩ.comp (isIsogeny_of_iso bt.symm)
  change IsIsogeny (((baseChange t).map f ≫ bt.hom) ≫ bt.inv) at hbc
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hbc
  exact Langlands.GroupScheme.isogeny_of_faithfullyFlat_baseChange (A := Ω) (groupHom f) hbc

set_option maxHeartbeats 1200000 in
private theorem isPolarization_of_total_ample_mumford {S : Scheme.{0}} [IsAffine S]
    (A : AbelianScheme S) (W : DualWitness A) (f : A ⟶ W.dual P)
    (h : HasAmpleMumfordPresentation P.preservation P.square A W.hasDual (W.parameterMap P f)) :
    W.IsPolarization P f := by
  refine ⟨?_, ?_⟩
  · apply Langlands.GroupScheme.fiberwiseIsogeny S A.toGrp (W.dual P).toGrp
      A.smooth (W.dual P).smooth A.proper (W.dual P).proper (groupHom f)
    intro x
    let s := S.fromSpecResidueField x
    let Ws := W.pullback P s
    let bs := W.baseChangeIso P s Ws
    have hs := hasAmpleMumfordPresentation_baseChange s A P.preservation P.square P.universality
      W.hasDual (W.parameterMap P f) h
    unfold HasAmpleMumfordAfterBaseChange at hs
    rw [← W.parameterMap_pullbackMap P s Ws f] at hs
    have hfs := isIsogeny_of_ample_mumford_field P (S.residueField x) ((baseChange s).obj A) Ws
      (W.pullbackMap P s Ws f) hs
    have hz := hfs.comp (isIsogeny_of_iso bs.symm)
    change IsIsogeny (((baseChange s).map f ≫ bs.hom) ≫ bs.inv) at hz
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hz
    exact hz
  · intro K _ _ s
    have hs := hasAmpleMumfordPresentation_baseChange s A P.preservation P.square P.universality
      W.hasDual (W.parameterMap P f) h
    refine ⟨K, inferInstance, RingHom.id K, ?_⟩
    exact hasAmpleMumfordPresentation_baseChange _ ((baseChange s).obj A) P.preservation P.square
      P.universality (hasDualScheme_baseChange P.universality s A W.hasDual) _ hs

end Isogeny

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]

local notation "j" => Spec.algebraMap V K

set_option maxHeartbeats 2400000 in
/-- If the generic dual-valued map is a polarization, twice the extended map
is presented by its ample diagonal Poincaré bundle on the original DVR. -/
theorem dvrAmpleMumfordPresentation_double (P : Prerequisites.{0})
    (A : AbelianScheme (Spec (.of V))) (W : DualWitness A) (lam : A ⟶ W.dual P)
    (h : (W.pullback P j).IsPolarization P (W.pullbackMap P j (W.pullback P j) lam)) :
    HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
      (W.parameterMap P (2 • lam)) := by
  let b : Spec (.of K) ⟶ Spec (.of V) := j
  let A' := (baseChange b).obj A
  let W' := W.pullback P b
  let lam' := W.pullbackMap P b W' lam
  let L := poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)
  have hL : L.IsAmple := dvrIsAmpleDiagonal_of_genericPolarization (V := V) K P A W lam h
  obtain ⟨N, ⟨eN⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback (unitSection A)).obj L)
  obtain ⟨M, ⟨eM⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((RigidifiedLineBundle.forget _).obj (LineBundle.normalize P.preservation A.X.hom
      (unitSection A) (unitSection_comp A) L N eN))
  let mu := mumfordSchemeMapOfLineBundle P.preservation A L N eN M eM P.square W.hasDual
  refine ⟨L, N, eN, M, eM, hL, ?_⟩
  have : IsSeparated (dualScheme A W.hasDual).hom :=
    inferInstanceAs (IsSeparated (W.dual P).X.hom)
  apply genericFibre_map_injective (V := V) K
  apply (cancel_mono (dualSchemeBaseChangeIso P.universality b A W.hasDual W'.hasDual).hom).mp
  change dualBaseChangeMap A W.hasDual P.universality b (W.parameterMap P (2 • lam)) =
    dualBaseChangeMap A W.hasDual P.universality b mu
  rw [← W.parameterMap_pullbackMap P b W' (2 • lam), dualPullback_nsmul P b W W' 2 lam]
  obtain ⟨N', eN', M', eM', hmu'⟩ := polarizationDiagonalMumford P.preservation P.square
    P.universality P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability (Spec (.of K)) A' W'.hasDual W'.geometry W'.inverseBundle W'.evaluation lam' h
  change _ = W'.parameterMap P (2 • lam') at hmu'
  rw [← hmu', dualBaseChangeMap_mumford P b A W L N eN M eM]
  have e := poincareDiagonalBaseChangeIso P.universality b A W.hasDual (W.parameterMap P lam)
  rw [← W.parameterMap_pullbackMap P b W' lam] at e
  exact fieldMumford_eq_of_bundle_iso P K A' W' e _ eN' _ eM' _ _ _ _

set_option maxHeartbeats 1000000 in
/-- Twice the actual integral extension of a generic polarization is a
polarization on the original good model. -/
def extendDvrPolarizationDouble (P : Prerequisites.{0}) (A : AbelianScheme (Spec (.of V)))
    (W : DualWitness A) (lam : (baseChange j).obj A ⟶ (W.pullback P j).dual P)
    (h : (W.pullback P j).IsPolarization P lam) : {f : A ⟶ W.dual P // W.IsPolarization P f} := by
  let lam₀ := extendDvrDualHom (V := V) K P A W (W.pullback P j) lam
  have he := pullbackMap_extendDvrDualHom (V := V) K P A W (W.pullback P j) lam
  have hp := dvrAmpleMumfordPresentation_double (V := V) K P A W lam₀ (he.symm ▸ h)
  exact ⟨2 • lam₀, isPolarization_of_total_ample_mumford P A W (2 • lam₀) hp⟩

set_option maxHeartbeats 1000000 in
/-- The extended polarization restricts to twice the specified generic
polarization under the canonical dual comparison. -/
@[simp]
theorem pullbackMap_extendDvrPolarizationDouble (P : Prerequisites.{0})
    (A : AbelianScheme (Spec (.of V))) (W : DualWitness A)
    (lam : (baseChange j).obj A ⟶ (W.pullback P j).dual P)
    (h : (W.pullback P j).IsPolarization P lam) :
    W.pullbackMap P j (W.pullback P j)
      (extendDvrPolarizationDouble (V := V) K P A W lam h).val = 2 • lam := by
  let f := extendDvrDualHom (V := V) K P A W (W.pullback P j) lam
  change W.pullbackMap P j (W.pullback P j) (2 • f) = 2 • lam
  rw [dualPullback_nsmul P j W (W.pullback P j) 2 f,
    show W.pullbackMap P j (W.pullback P j) f = lam from
      pullbackMap_extendDvrDualHom (V := V) K P A W (W.pullback P j) lam]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
