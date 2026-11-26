import Langlands.Global.AdelicIntertwiningNormalizedLevi
import Langlands.Global.AdelicIntertwiningStabilizerInParabolic
import Langlands.Global.AdelicLeviDynamicModulus
import Langlands.Representation.Aubert.General.CentralizingUnipotentHaarDeterminant
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.Global.AdelicPositiveRootCharacterRelation
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # Haar balance for the adelic intertwining quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology TensorProduct
open scoped CategoryTheory.MonObj NNReal TensorProduct

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.QuotientIntegration

private theorem parameterPower_halfModulus_eq_sqrt {F : Type u} [Field F] [NumberField F]
    (S : GroupScheme (Spec (CommRingCat.of F))) [IsAffine S.X.left] [LocallyOfFiniteType S.X.hom]
    (x : AdelicGroupPoints F S) :
    parameterPower F S (halfModulusParameter F S) x =
      (Real.sqrt (characterNorm F S (Lie.adjointDeterminantCharacter S).toMul x : ℝ≥0) : ℂ) := by
  set n : ℝ := ((characterNorm F S (Lie.adjointDeterminantCharacter S).toMul x : ℝ≥0) : ℝ)
  have hn : 0 < n := by
    exact_mod_cast pos_iff_ne_zero.mpr
      (characterNorm F S (Lie.adjointDeterminantCharacter S).toMul x).ne_zero
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn, Complex.ofReal_exp]
  change Complex.exp ((1 / 2 : ℂ) * (Real.log n : ℂ)) = _
  congr 1
  push_cast
  ring

section Scales

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} {iU : U ⟶ P}
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {l' : M' ⟶ Q} {iV : V ⟶ Q}
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {c : M' ⟶ M} {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))
local notation "H" => intertwiningAdelicStabilizer p iU (iV ≫ q) w
local notation "C" => IntertwiningStabilizer p iU (iV ≫ q) w
local notation "ιC" => intertwiningStabilizerToParabolic iU iV q p w
local notation "jC" => intertwiningStabilizerHom p iU (iV ≫ q) w

private theorem targetRadicalHaar_eq_modulus
    {τ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hQ : (Dynamic.parabolic τ).IsRepresentedBy q) (hV : (Dynamic.unipotent τ).IsRepresentedBy (iV ≫ q))
    (hN : (SubgroupFunctor.range iV).IsNormal) (x : AdelicGroupPoints F Q) :
    haveI : LocallyCompactSpace Vₐ :=
      (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
    mulEquivHaarChar (EisensteinConstantTerm.conjAdelic q iV hN x) =
      (parabolicModulus F hQ hV x : ℝ≥0) := by
  let : LocallyCompactSpace Vₐ :=
    (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
  let e : Vₐ ≃ₜ* (map F V G (iV ≫ q)).toMonoidHom.range := ContinuousMulEquiv.refl Vₐ
  rw [parabolicModulus_apply]
  exact Aubert.General.CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter _ _ _ e _
    (fun _ => rfl)

private theorem stabilizerHaar_eq_modulus
    {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ Q}
    {D : GroupScheme (Spec (CommRingCat.of F))} {d : D ⟶ Q}
    (hD : (Dynamic.parabolic χ).IsRepresentedBy d)
    (hC : (Dynamic.unipotent χ).IsRepresentedBy ιC)
    (hU : (SubgroupFunctor.range iU).IsNormal) (hV : (SubgroupFunctor.range iV).IsNormal)
    (hi : IsClosedSubgroup (iU ≫ p)) (hVu : IsUnipotent V)
    (hw : IsWeylConjugation p l q l' w c) (m : AdelicGroupPoints F M')
    (x : AdelicGroupPoints F D) (hx : map F D Q d x = map F M' Q l' m) :
    haveI : LocallyCompactSpace H := (intertwiningStabilizer p iU (iV ≫ q) w
      (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi hVu).1.locallyCompactSpace
    mulEquivHaarChar (subgroupAutomorphism H (EisensteinConstantTerm.conjAdelic q iV hV
      (map F M' Q l' m)) (conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU hV m)) =
      (parabolicModulus F hD hC x : ℝ≥0) := by
  let : LocallyCompactSpace H := (intertwiningStabilizer p iU (iV ≫ q) w
    (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi hVu).1.locallyCompactSpace
  have hj := (intertwiningStabilizer_geometry p iU (iV ≫ q) w
    (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi hVu).1
  have : IsClosedImmersion (jC).hom.hom.left := hj
  have : IsAffine (C).X.left := isAffine_left_of_isClosedSubgroup F jC hj
  let e₁ := rangeEquiv F ιC (isClosedEmbedding_map_unipotent F hC).isEmbedding
  let e₂ := rangeEquiv F jC (isClosedEmbedding_map F C G jC).isEmbedding
  let e := (intertwiningStabilizerEquiv p iU (iV ≫ q) w).symm.trans (e₂.symm.trans e₁)
  rw [parabolicModulus_apply]
  apply Aubert.General.CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter _ _ _ e
  intro y
  apply (isClosedEmbedding_map F Q G q).injective
  have he (z : H) : map F Q G q ((e z : (map F C Q ιC).toMonoidHom.range) : AdelicGroupPoints F Q) =
      z.val.val := by
    change map F Q G q (map F C Q ιC (e₂.symm ((intertwiningStabilizerEquiv p iU (iV ≫ q) w).symm z))) = _
    rw [← map_comp_apply_of_hom, intertwiningStabilizerToParabolic_comp]
    exact map_rangeEquiv_symm F jC (isClosedEmbedding_map F C G jC).isEmbedding _
  simp only [map_mul, map_inv, he, hx]
  rfl

end Scales

section Characters

variable {F : Type u} [Field F]
  {P G M U M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine M'.X.left] [IsAffineHom U.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {p : P ⟶ G} {l : M ⟶ P} {i : U ⟶ G}
  (hP : (Dynamic.parabolic χ).IsRepresentedBy p)
  (hZ : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ p))
  (hU : (Dynamic.unipotent χ).IsRepresentedBy i)

include hP in
private theorem radicalDeterminant_eq_restriction {n : ℕ} (b : Lie.FiniteCoordinates U n)
    (hM : IsConnectedReductive M) :
    characterRestrict l (Lie.adjointDeterminantCharacter P) =
      (Dynamic.centralizerAdjointAction hZ hU).determinantCharacter b := by
  have hl : Dynamic.centralizerToParabolic hP hZ = l :=
    hP.hom_ext (Dynamic.centralizerToParabolic_comp hP hZ)
  simpa only [hl, Lie.connectedReductiveAdjointDeterminant F M hM, add_zero] using
    Dynamic.characterRestrict_adjointDeterminantCharacter_parabolic hP hZ hU b

private theorem conjugateSourceRadicalAction {χ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    {j : M' ⟶ G} (f : G ≅ G) (c : M' ⟶ M) (hj : c ≫ (l ≫ p) ≫ f.hom = j)
    (hZ' : SubgroupFunctor.range j ≤ Dynamic.centralizer χ')
    (hU' : (Dynamic.unipotent χ').IsRepresentedBy (i ≫ f.hom)) :
    Dynamic.centralizingUnipotentAction χ' j hZ' hU' =
      (Dynamic.centralizerAdjointAction hZ hU).restrict c := by
  have : Mono (i ≫ f.hom).hom.hom := hU'.1
  apply AutomorphicAction.ext_act
  intro X z y
  apply (cancel_mono (i ≫ f.hom).hom.hom).mp
  rw [Dynamic.centralizingUnipotentAction_act_comp, AutomorphicAction.restrict_act]
  have hz : (z ≫ c.hom.hom ≫ (l ≫ p).hom.hom) ≫ f.hom.hom.hom = z ≫ j.hom.hom := by
    have hj' : c ≫ l ≫ p ≫ f.hom = j := by simpa only [Category.assoc] using hj
    simp only [Category.assoc, ← Grp.comp_hom_hom, hj']
  change _ = (((Dynamic.centralizerAdjointAction hZ hU).act (z ≫ c.hom.hom) y) ≫ i.hom.hom) ≫
    f.hom.hom.hom
  rw [Dynamic.centralizerAdjointAction_act_comp]
  let fX : (X ⟶ G.X) →* (X ⟶ G.X) := ((pointsMap f.hom).app (Opposite.op X)).hom
  change _ = fX
    (((z ≫ c.hom.hom) ≫ (l ≫ p).hom.hom) * (y ≫ i.hom.hom) *
      ((z ≫ c.hom.hom) ≫ (l ≫ p).hom.hom)⁻¹)
  rw [map_mul, map_mul, map_inv]
  change _ = (((z ≫ c.hom.hom) ≫ (l ≫ p).hom.hom) ≫ f.hom.hom.hom) *
    ((y ≫ i.hom.hom) ≫ f.hom.hom.hom) * (((z ≫ c.hom.hom) ≫ (l ≫ p).hom.hom) ≫ f.hom.hom.hom)⁻¹
  rw [Category.assoc z, hz, Category.assoc y, ← Grp.comp_hom_hom]

end Characters

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- The forward Haar scale of the intertwining quotient is the ratio of the target and source
half moduli at the corresponding Levi points, as used in Bernstein–Lapid (6.5). -/
def IntertwiningLeviHaarBalanceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine Q.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (_r : ParabolicRootPresentation p l a)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (a' : A'.toGrp ⟶ M') (_r' : ParabolicRootPresentation q l' a')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    have : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType
      (j := p) ‹IsClosedImmersion p.hom.hom.left›
    have : LocallyOfFiniteType Q.X.hom := IsClosedSubgroup.locallyOfFiniteType
      (j := q) ‹IsClosedImmersion q.hom.hom.left›
    have : IsAffineHom V.X.hom := isAffineHom_of_isAffine _
    have : LocallyOfFiniteType V.X.hom := IsClosedSubgroup.locallyOfFiniteType
      (j := iV ≫ q) ‹IsClosedImmersion (iV ≫ q).hom.hom.left›
    IsConnectedReductive G →
    ∀ (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
      (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hw : IsWeylConjugation p l q l' w c)
      (m : AdelicGroupPoints F M'),
      intertwiningLeviHaarFactor iU iV hw hU.1.isNormal hV.1.isNormal
        ‹IsClosedImmersion (iU ≫ p).hom.hom.left› hV.1.isUnipotent m *
          parameterPower F P (halfModulusParameter F P) (map F M P l (map F M' M c m)) =
        parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' m)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 1200 in
/-- The normalized Haar balance on the actual intertwining quotient follows from the
three radical determinants on the common Levi. -/
private theorem intertwiningLeviHaarBalance_of_presentations
    {F : Type u} [Field F] [NumberField F]
    {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
    {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
    [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left] [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
    [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom] [IsAffine V.X.left]
    [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    (hi : IsClosedSubgroup (iU ≫ p)) {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [hj : IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} (r' : ParabolicRootPresentation q l' a')
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hw : IsWeylConjugation p l q l' w c)
    (m : AdelicGroupPoints F M') :
    intertwiningLeviHaarFactor iU iV hw hU.1.isNormal hV.1.isNormal hi hV.1.isUnipotent m *
        parameterPower F P (halfModulusParameter F P) (map F M P l (map F M' M c m)) =
      parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' m) := by
  classical
  have : IsClosedImmersion (iU ≫ p).hom.hom.left := hi
  let χP := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
  let χQ := CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a' ≫ l' ≫ q
  let f := G.innerIso w
  let C := IntertwiningStabilizer p iU (iV ≫ q) w
  let jC := intertwiningStabilizerHom p iU (iV ≫ q) w
  let ιC := intertwiningStabilizerToParabolic iU iV q p w
  have : IsAffineHom V.X.hom := isAffineHom_of_isAffine _
  have : Smooth G.X.hom := hG.smooth
  have : Smooth Q.X.hom := r'.isCompatible.parabolic.smooth
  have : IsAffineHom Q.X.hom := isAffineHom_of_isAffine _
  have : IsAffineHom U.X.hom := isAffineHom_of_isAffine _
  have : LocallyOfFiniteType U.X.hom := IsClosedSubgroup.locallyOfFiniteType (j := iU ≫ p) hi
  have hjC := (intertwiningStabilizer_geometry p iU (iV ≫ q) w hj hi hV.1.isUnipotent).1
  have : IsAffineHom C.X.hom := hjC.isAffineHom
  have : LocallyOfFiniteType C.X.hom := hjC.locallyOfFiniteType
  let bU := Lie.finiteCoordinates U
  let bV := Lie.finiteCoordinates V
  let bC := Lie.finiteCoordinates C
  have : IsClosedImmersion (l ≫ p).hom.hom.left :=
    r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  have : IsClosedImmersion (l' ≫ q).hom.hom.left :=
    r'.isCompatible.levi.isClosedSubgroup.comp r'.isCompatible.parabolic.isClosedSubgroup
  have hd : IsClosedSubgroup (iU ≫ p ≫ f.hom) := by
    rw [← Category.assoc]
    exact (show IsClosedSubgroup (iU ≫ p) from hi).comp_iso f
  have hP : (Dynamic.parabolic χP).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
  have hQ : (Dynamic.parabolic χQ).IsRepresentedBy q :=
    ⟨Over.mono_of_mono_left _, r'.parabolic_eq_splitComponentCocharacter⟩
  have hZP : (Dynamic.centralizer χP).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, r.levi_eq_splitComponentCocharacter⟩
  have hZQ : (Dynamic.centralizer χQ).IsRepresentedBy (l' ≫ q) :=
    ⟨Over.mono_of_mono_left _, r'.levi_eq_splitComponentCocharacter⟩
  have hUP : (Dynamic.unipotent χP).IsRepresentedBy (iU ≫ p) :=
    ⟨Over.mono_of_mono_left _, r.range_comp_radical_eq hU⟩
  have : Mono (iU ≫ p ≫ f.hom).hom.hom.left := hd.mono
  have hU' : (Dynamic.unipotent (χP ≫ f.hom)).IsRepresentedBy (iU ≫ p ≫ f.hom) :=
    ⟨Over.mono_of_mono_left _, range_conjugate_sourceRadical r hU⟩
  have hV' : (Dynamic.unipotent χQ).IsRepresentedBy (iV ≫ q) :=
    ⟨Over.mono_of_mono_left _, r'.range_comp_radical_eq hV⟩
  have hC' : (Dynamic.unipotent (χP ≫ f.hom) ⊓ Dynamic.unipotent χQ).IsRepresentedBy jC := by
    have : Mono jC.hom.hom.left := hjC.mono
    refine ⟨Over.mono_of_mono_left _, ?_⟩
    change SubgroupFunctor.range (subgroupIntersectionHom (iV ≫ q) (iU ≫ p ≫ f.hom)) = _
    rw [range_subgroupIntersectionHom, hU'.2, hV'.2]
    apply SubgroupFunctor.ext
    intro T
    simp only [SubgroupFunctor.inf_carrier, inf_comm]
  have hZ' : SubgroupFunctor.range (l' ≫ q) ≤ Dynamic.centralizer (χP ≫ f.hom) :=
    (centralizer_conjugate_sourceCocharacter r hw).ge
  have hDet := intertwiningRadicalDeterminantBalance r r' hw hG bU bV bC hU' hV' hC' hZ' hZQ.2.le
  obtain ⟨χ, _, hZχ, hCχ⟩ := exists_intertwiningStabilizer_dynamic r r' hw hU hV
  let D := Dynamic.Affine.parabolicScheme χ
  let d := Dynamic.Affine.parabolicHom χ
  have hD : (Dynamic.parabolic χ).IsRepresentedBy d := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have : IsAffine D.X.left := isAffine_parabolic F hD
  have : LocallyOfFiniteType D.X.hom := locallyOfFiniteType_parabolic F hD
  have hDs : Smooth D.X.hom := (dynamicSmooth F Q χ D d).1 hD
  have hl : Dynamic.centralizerToParabolic hQ hZQ = l' :=
    hQ.hom_ext (Dynamic.centralizerToParabolic_comp hQ hZQ)
  let x := map F M' D (Dynamic.centralizerToParabolic hD hZχ) m
  have hx : map F D Q d x = map F M' Q l' m := by
    rw [← map_comp_apply_of_hom, Dynamic.centralizerToParabolic_comp]
  have hcomp : ιC ≫ q = jC := intertwiningStabilizerToParabolic_comp
  have hActC : Dynamic.centralizingUnipotentIntersectionAction (χP ≫ f.hom) χQ (l' ≫ q)
      hZ' hZQ.2.le hC' = Dynamic.centralizerAdjointAction hZχ hCχ := by
    have : Mono jC.hom.hom := hC'.1
    apply AutomorphicAction.ext_act
    intro X z y
    apply (cancel_mono jC.hom.hom).mp
    rw [Dynamic.centralizingUnipotentIntersectionAction_act_comp, ← hcomp, Grp.comp_hom_hom ιC q,
      ← Category.assoc ((Dynamic.centralizerAdjointAction hZχ hCχ).act z y) ιC.hom.hom q.hom.hom,
      Dynamic.centralizerAdjointAction_act_comp]
    let qX : (X ⟶ Q.X) →* (X ⟶ G.X) := ((pointsMap q).app (Opposite.op X)).hom
    change _ = qX ((z ≫ l'.hom.hom) * (y ≫ ιC.hom.hom) * (z ≫ l'.hom.hom)⁻¹)
    rw [map_mul, map_mul, map_inv]
    change _ = ((z ≫ l'.hom.hom) ≫ q.hom.hom) * ((y ≫ ιC.hom.hom) ≫ q.hom.hom) *
      (((z ≫ l'.hom.hom) ≫ q.hom.hom)⁻¹)
    simp only [Category.assoc, Grp.comp_hom_hom]
  have hWeyl : c ≫ (l ≫ p) ≫ f.hom = l' ≫ q := by
    let : IsIso c := hw.isIso
    rw [hw.comp_inner_hom, IsIso.hom_inv_id_assoc]
  have hActU : Dynamic.centralizingUnipotentAction (χP ≫ f.hom) (l' ≫ q) hZ' hU' =
      (Dynamic.centralizerAdjointAction hZP hUP).restrict c := by
    have hUt : (Dynamic.unipotent (χP ≫ f.hom)).IsRepresentedBy ((iU ≫ p) ≫ f.hom) := by
      simpa only [Category.assoc] using hU'
    simpa only [Category.assoc] using conjugateSourceRadicalAction hZP hUP f c hWeyl hZ' hUt
  have hActV : Dynamic.centralizingUnipotentAction χQ (l' ≫ q) hZQ.2.le hV' =
      Dynamic.centralizerAdjointAction hZQ hV' := by
    simpa only [AutomorphicAction.restrict_id] using
      (Dynamic.centralizerAdjointAction_restrict_eq_centralizingUnipotentAction χQ (l' ≫ q)
        hZQ.2.le hZQ hV' (𝟙 M') (Category.id_comp _)).symm
  change (Dynamic.centralizingUnipotentAction (χP ≫ f.hom) (l' ≫ q) hZ' hU').determinantCharacter bU +
    (Dynamic.centralizingUnipotentAction χQ (l' ≫ q) hZQ.2.le hV').determinantCharacter bV =
    2 • (Dynamic.centralizingUnipotentIntersectionAction (χP ≫ f.hom) χQ (l' ≫ q) hZ' hZQ.2.le hC').determinantCharacter bC at hDet
  rw [hActC, hActV, hActU] at hDet
  have hDet' : characterRestrict c (characterRestrict l (Lie.adjointDeterminantCharacter P)) +
      characterRestrict l' (Lie.adjointDeterminantCharacter Q) =
      2 • (Dynamic.centralizerAdjointAction hZχ hCχ).determinantCharacter bC := by
    rw [radicalDeterminant_eq_restriction hP hZP hUP bU r.isCompatible.levi.isConnectedReductive,
      radicalDeterminant_eq_restriction hQ hZQ hV' bV r'.isCompatible.levi.isConnectedReductive,
      AutomorphicAction.determinantCharacter_restrict]
    exact hDet
  have hVmod := targetRadicalHaar_eq_modulus hQ hV' hV.1.isNormal (map F M' Q l' m)
  have hQmod := dynamicModulus_levi_eq_characterNorm hQ hZQ hV'
    r'.isCompatible.levi.isConnectedReductive r'.isCompatible.parabolic.smooth bV m
  rw [hl] at hQmod
  have hCmod := dynamicModulus_levi_eq_characterNorm hD hZχ hCχ
    r'.isCompatible.levi.isConnectedReductive hDs bC m
  have hHmod := stabilizerHaar_eq_modulus hD hCχ hU.1.isNormal hV.1.isNormal hi hV.1.isUnipotent hw m x hx
  change parabolicModulus F hD hCχ x = _ at hCmod
  let δP := characterNorm F P (Lie.adjointDeterminantCharacter P).toMul (map F M P l (map F M' M c m))
  let δQ := characterNorm F Q (Lie.adjointDeterminantCharacter Q).toMul (map F M' Q l' m)
  let δC := characterNorm F M' ((Dynamic.centralizerAdjointAction hZχ hCχ).determinantCharacter bC).toMul m
  have hdetN := congrArg (fun ψ : rationalCharacters M' => characterNorm F M' ψ.toMul m) hDet'
  simp only [characterNorm_add, characterNorm_nsmul, characterRestrict_apply, characterNorm_comp] at hdetN
  have hdetR : ((δP : ℝ≥0) : ℝ) * ((δQ : ℝ≥0) : ℝ) = ((δC : ℝ≥0) : ℝ) ^ 2 := by
    exact_mod_cast congrArg (fun d : ℝ≥0ˣ => (d : ℝ≥0)) hdetN
  have hQmod' : parabolicModulus F hQ hV' (map F M' Q l' m) = δQ := by
    rw [hQmod, ← radicalDeterminant_eq_restriction hQ hZQ hV' bV r'.isCompatible.levi.isConnectedReductive,
      characterRestrict_apply, characterNorm_comp]
  dsimp only [intertwiningLeviHaarFactor]
  rw [hVmod, hQmod', hHmod, hCmod, parameterPower_halfModulus_eq_sqrt, parameterPower_halfModulus_eq_sqrt]
  change ((↑((δQ : ℝ≥0) / (δC : ℝ≥0)) : ℝ) : ℂ) *
    (Real.sqrt ((δP : ℝ≥0) : ℝ) : ℂ) = (Real.sqrt ((δQ : ℝ≥0) : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, Complex.ofReal_inj, NNReal.coe_div]
  let p₀ : ℝ := (δP : ℝ≥0)
  let q₀ : ℝ := (δQ : ℝ≥0)
  let c₀ : ℝ := (δC : ℝ≥0)
  have hp₀ : 0 ≤ p₀ := NNReal.zero_le_coe
  have hq₀ : 0 ≤ q₀ := NNReal.zero_le_coe
  have hc₀ : 0 < c₀ := by exact_mod_cast pos_iff_ne_zero.mpr δC.ne_zero
  have hsqrt : Real.sqrt p₀ * Real.sqrt q₀ = c₀ := by
    rw [← Real.sqrt_mul hp₀, hdetR, Real.sqrt_sq hc₀.le]
  change q₀ / c₀ * Real.sqrt p₀ = Real.sqrt q₀
  rw [div_mul_eq_mul_div, div_eq_iff hc₀.ne']
  calc
    q₀ * Real.sqrt p₀ = Real.sqrt q₀ ^ 2 * Real.sqrt p₀ :=
      congrArg (· * Real.sqrt p₀) (Real.sq_sqrt hq₀).symm
    _ = Real.sqrt q₀ * (Real.sqrt p₀ * Real.sqrt q₀) := by ring
    _ = Real.sqrt q₀ * c₀ := by rw [hsqrt]

/-- The normalized Haar balance on the actual intertwining quotient follows from the three
radical determinants on the common Levi. -/
theorem intertwiningLeviHaarBalance : IntertwiningLeviHaarBalanceStatement := by
  intro F _ _ G P M U Q M' V A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l hi a r q _ iV l' hj a' r' w c
    _ _ _ _ hG hU hV hw m
  exact intertwiningLeviHaarBalance_of_presentations hi r r' hG hU hV hw m

/-- For the specified rational parabolics of a connected reductive number-field group,
    with geometric unipotent radicals and Weyl-conjugate Levi subgroups, the quotient Haar
    factor times the source half modulus equals the target half modulus. -/
def IntertwiningLeviHaarBalanceOfParabolicsStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F]
    {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
    [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
    {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {q : Q ⟶ G} {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M},
    IsConnectedReductive G → ∀ (hp : IsParabolicSubgroup p)
      (hU : LeviSubgroup.IsGeometricUnipotentRadical iU),
      IsRationalLeviSubgroup l → IsParabolicSubgroup q →
      ∀ (hV : LeviSubgroup.IsGeometricUnipotentRadical iV),
        IsRationalLeviSubgroup l' → ∀ (hw : IsWeylConjugation p l q l' w c)
          (m : AdelicGroupPoints F M'),
          intertwiningLeviHaarFactor iU iV hw hU.1.isNormal hV.1.isNormal
              (hU.1.isClosedSubgroup.comp hp.isClosedSubgroup) hV.1.isUnipotent m *
              parameterPower F P (halfModulusParameter F P) (map F M P l (map F M' M c m)) =
            parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' m)

/-- Choose split components and compatible root presentations to apply determinant balance. -/
theorem intertwiningLeviHaarBalance_of_parabolics :
    IntertwiningLeviHaarBalanceOfParabolicsStatement.{u} := by
  intro F _ _ G P M U Q M' V _ _ _ _ _ _ _ _ _ p iU l q iV l' _ w c hG hp hU hl hq hV hl' hw m
  have := hG.isAffineHom
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
  have hM := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have hM' := hl'.isClosedSubgroup.comp hq.isClosedSubgroup
  have hUG := hU.1.isClosedSubgroup.comp hp.isClosedSubgroup
  have : IsAffine M.X.left := isAffine_left_of_isClosedSubgroup F (l ≫ p) hM
  have : LocallyOfFiniteType M.X.hom := hM.locallyOfFiniteType
  have : IsAffine M'.X.left := isAffine_left_of_isClosedSubgroup F (l' ≫ q) hM'
  have : LocallyOfFiniteType M'.X.hom := hM'.locallyOfFiniteType
  have : IsAffine U.X.left := isAffine_left_of_isClosedSubgroup F (iU ≫ p) hUG
  obtain ⟨A, a, ha⟩ := exists_isSplitComponent M
  obtain ⟨A', a', ha'⟩ := exists_isSplitComponent M'
  obtain ⟨r⟩ := parabolicRootPresentationExistence F G hG P M A p l a hp hl ha
  obtain ⟨r'⟩ := parabolicRootPresentationExistence F G hG Q M' A' q l' a' hq hl' ha'
  exact intertwiningLeviHaarBalance_of_presentations hUG r r' hG hU hV hw m

end Langlands.Global
