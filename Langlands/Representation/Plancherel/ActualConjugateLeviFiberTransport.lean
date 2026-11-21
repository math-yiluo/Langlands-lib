import Langlands.Representation.Plancherel.ActualParabolicUnitaryTranslation
import Langlands.Representation.Aubert.General.ConjugationComposition
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Canonical target fiber transport for successive conjugations -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviFiberTransport

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition ActualCommonLeviTensor ActualCommonLeviCoherence
open ActualConjugateLeviTensor ActualConjugateLeviV3 ActualParabolicUnitaryTranslation
open ActualCommonLeviV3 (unitaryParameter)

section Inducing

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {M N L : Subgroup H} (t s : H)
  (ht : ∀ x : H, x ∈ N ↔ t⁻¹ * x * t ∈ M)
  (hs : ∀ x : H, x ∈ L ↔ s⁻¹ * x * s ∈ N)
  {A : SmoothRep.{0, u, uV} ℂ M} {B : SmoothRep.{0, u, uV} ℂ N}
  {C D : SmoothRep.{0, u, uV} ℂ L}

private def undoSuccessiveTwistIdentifications
    (e₁ : (conjugationFunctor t ht).obj A ≅ B)
    (e₂ : (conjugationFunctor s hs).obj B ≅ C)
    (e : (conjugationFunctor s hs).obj ((conjugationFunctor t ht).obj A) ≅ D) :
    C ≅ D :=
  ((conjugationFunctor s hs).mapIso e₁ ≪≫ e₂).symm ≪≫ e

private def conjugationCompAt (g : H) (hg : s * t = g)
    (h : ∀ x : H, x ∈ L ↔ g⁻¹ * x * g ∈ M) (A : SmoothRep.{0, u, uV} ℂ M) :
    (conjugationFunctor s hs).obj ((conjugationFunctor t ht).obj A) ≅
      (conjugationFunctor g h).obj A := by
  subst g
  exact conjugationFunctorCompIsoApp t s ht hs A

end Inducing

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Cochar" => (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G
set_option hygiene false in
local notation "Gpts" => RationalPoint F G.X

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The actual conjugated cocharacters act in the order t, then s. -/
theorem conjugationAnchor_mul (χ : Cochar) (s t : Gpts) :
    (χ ≫ (G.innerIso t).hom) ≫ (G.innerIso s).hom = χ ≫ (G.innerIso (s * t)).hom := by
  rw [G.innerIso_mul_hom, Category.assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Conjugation of the cocharacter by the identity point. -/
theorem conjugationAnchor_one (χ : Cochar) : χ ≫ (G.innerIso (1 : Gpts)).hom = χ := by
  rw [G.innerIso_one_hom, Category.comp_id]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Return of the conjugated cocharacter after actual inverse conjugation. -/
theorem conjugationAnchor_inv (χ : Cochar) (g : Gpts) :
    (χ ≫ (G.innerIso g).hom) ≫ (G.innerIso g⁻¹).hom = χ :=
  (conjugationAnchor_mul χ g⁻¹ g).trans (by
    rw [inv_mul_cancel, conjugationAnchor_one])

private abbrev twistAt (χ : Cochar) (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  twistObject χ (unitaryParameter χ z) A

private abbrev fiberOf {χ : Cochar} {K : OpenSubgroup Gpts} (P : ParabolicPresentation χ K)
    (B : SmoothRep.{0, u, uV} ℂ (levi χ)) :=
  leviProductInducedCoefficientObject
    (commonDecomposition χ P.cocharacter P.centralizer_eq) (radical_isClosed P.cocharacter) B

/-- Reuse the same parabolic and Iwasawa factorization over the equal Levi. -/
def changeAnchor {χ φ : Cochar} (h : χ = φ) {K : OpenSubgroup Gpts}
    (P : ParabolicPresentation χ K) : ParabolicPresentation φ K where
  cocharacter := P.cocharacter
  centralizer_eq := P.centralizer_eq.trans (congrArg Dynamic.centralizer h)
  iwasawa := P.iwasawa

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem anchorMembership {χ φ : Cochar} (h : χ = φ) (x : Gpts) :
    x ∈ levi φ ↔ (1 : Gpts)⁻¹ * x * 1 ∈ levi χ := by
  subst φ
  simp only [inv_one, one_mul, mul_one]

private abbrev changeInducingAnchor {χ φ : Cochar} (h : χ = φ)
    (B : SmoothRep.{0, u, uV} ℂ (levi χ)) : SmoothRep.{0, u, uV} ℂ (levi φ) :=
  (conjugationFunctor 1 (anchorMembership h)).obj B

private def coefficientEquivOfAnchorIso {χ φ : Cochar} (h : χ = φ) {K : OpenSubgroup Gpts}
    (P : ParabolicPresentation χ K) (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Gpts))
    (A : SmoothRep.{0, u, uV} ℂ (levi φ)) (B : SmoothRep.{0, u, uV} ℂ (levi χ))
    (e : A ≅ changeInducingAnchor h B) :
    (fiberOf (changeAnchor h P) A).representation.Equiv
      (fiberOf P B).representation := by
  let Q := changeAnchor h P
  let ds := commonDecomposition χ P.cocharacter P.centralizer_eq
  let dt := commonDecomposition φ Q.cocharacter Q.centralizer_eq
  let hc := radical_isClosed P.cocharacter
  let hd := DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K hK Q.cocharacter Q.iwasawa
  have hp : ∀ x : Gpts, x ∈ parabolic Q.cocharacter ↔ (1 : Gpts)⁻¹ * x * 1 ∈ parabolic P.cocharacter := by
    intro x
    simp only [Q, changeAnchor, inv_one, one_mul, mul_one]
  have hu : ∀ x : Gpts, x ∈ radical Q.cocharacter ↔ (1 : Gpts)⁻¹ * x * 1 ∈ radical P.cocharacter := by
    intro x
    simp only [Q, changeAnchor, inv_one, one_mul, mul_one]
  let E := CoefficientConjugation.leviCoefficientLeftTranslation ds dt 1 hp
    (anchorMembership h) hu hc hc hd hd B
  exact (coefficientCongr dt hc hd (SmoothRep.equivOfIso e)).trans E.symm

private def literalConjugateTwistIso (χ : Cochar) (g : Gpts)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (conjugationFunctor g (DynamicCoefficientConjugation.levi_mem_conjugation χ g)).obj
      (twistAt χ A z) ≅
      twistAt (χ ≫ (G.innerIso g).hom) (conjugateRepresentation χ g A)
        (unitaryConjugateParameter χ g z) :=
  eqToIso (DynamicCoefficientConjugation.conjugationFunctor_obj_eq χ g (twistAt χ A z)) ≪≫
    SmoothRep.mkIso (unitaryTwistEquiv χ g A z)

/-- Identify the twist after reindexing the target Levi anchor. -/
private def conjugateTwistIso (χ : Cochar) (g : Gpts) {φ : Cochar}
    (hφ : χ ≫ (G.innerIso g).hom = φ)
    (hM : ∀ x : Gpts, x ∈ levi φ ↔ g⁻¹ * x * g ∈ levi χ)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (conjugationFunctor g hM).obj (twistAt χ A z) ≅
      changeInducingAnchor hφ
        (twistAt (χ ≫ (G.innerIso g).hom) (conjugateRepresentation χ g A)
          (unitaryConjugateParameter χ g z)) :=
  (conjugationCompAt g 1 (DynamicCoefficientConjugation.levi_mem_conjugation χ g)
    (anchorMembership hφ) g (one_mul g) hM (twistAt χ A z)).symm ≪≫
    (conjugationFunctor 1 (anchorMembership hφ)).mapIso (literalConjugateTwistIso χ g A z)

section Multiplication

variable (χ : Cochar) (s t : Gpts) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  {K : OpenSubgroup Gpts} (hK : IsCompact (K : Set Gpts))

set_option hygiene false in
set_option quotPrecheck false in
local notation "χt" => (χ ≫ (G.innerIso t).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χts" => (χt ≫ (G.innerIso s).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χst" => (χ ≫ (G.innerIso (s * t)).hom)
set_option hygiene false in
local notation "At" => conjugateRepresentation χ t A
set_option hygiene false in
local notation "Ats" => conjugateRepresentation χt s At
set_option hygiene false in
local notation "Ast" => conjugateRepresentation χ (s * t) A
set_option hygiene false in
local notation "zt" => unitaryConjugateParameter χ t
set_option hygiene false in
local notation "zts" => unitaryConjugateParameter χt s
set_option hygiene false in
local notation "zst" => unitaryConjugateParameter χ (s * t)
set_option hygiene false in
local notation "hmul" => conjugationAnchor_mul χ s t

/-- The target parabolic for two successive transports is the same actual
parabolic, presented over the twice-conjugated Levi anchor. -/
abbrev multiplicationTarget (R : ParabolicPresentation χst K) : ParabolicPresentation χts K :=
  changeAnchor (hmul).symm R

/-- Identify the twice-conjugated target coefficient fiber with the direct
product-conjugated one, by the actual composition of inducing pullbacks. -/
private def multiplicationTwistIso (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    twistAt χts Ats (zts (zt z)) ≅
      changeInducingAnchor (hmul).symm (twistAt χst Ast (zst z)) :=
  let hMt := DynamicCoefficientConjugation.levi_mem_conjugation χ t
  let hMs := DynamicCoefficientConjugation.levi_mem_conjugation χt s
  let e₁ := literalConjugateTwistIso χ t A z
  let e₂ := literalConjugateTwistIso χt s At (zt z)
  let e₃ := conjugateTwistIso χ (s * t) (hmul).symm
    (conjugationMembership_mul t s hMt hMs) A z
  let composed := conjugationFunctorCompIsoApp t s hMt hMs (twistAt χ A z) ≪≫ e₃
  undoSuccessiveTwistIdentifications t s hMt hMs
    (A := twistAt χ A z) (B := twistAt χt At (zt z)) (C := twistAt χts Ats (zts (zt z)))
    e₁ e₂ composed

/-- The canonical comparison from the twice-conjugated coefficient fiber to
the direct product-conjugated coefficient fiber at the same parabolic. -/
def multiplicationEquiv (R : ParabolicPresentation χst K)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  coefficientEquivOfAnchorIso (hmul).symm R hG hK
    (twistAt χts Ats (zts (zt z))) (twistAt χst Ast (zst z)) (multiplicationTwistIso χ s t A z)

end Multiplication

section Identity

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  {K : OpenSubgroup Gpts} (hK : IsCompact (K : Set Gpts)) (P : ParabolicPresentation χ K)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χone" => (χ ≫ (G.innerIso (1 : Gpts)).hom)
set_option hygiene false in
local notation "hone" => (conjugationAnchor_one χ).symm

/-- The identity arrow uses the original parabolic on the identity-conjugate
Levi anchor. -/
abbrev identityTarget : ParabolicPresentation χone K := changeAnchor hone P

/-- The target of an identity arrow is canonically the original fiber. -/
def identityEquiv (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  coefficientEquivOfAnchorIso hone P hG hK
    (twistAt χone (conjugateRepresentation χ 1 A) (unitaryConjugateParameter χ 1 z))
    (twistAt χ A z) (literalConjugateTwistIso χ 1 A z).symm

end Identity

section Inverse

variable (χ : Cochar) (g : Gpts) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  {K : OpenSubgroup Gpts} (hK : IsCompact (K : Set Gpts)) (P : ParabolicPresentation χ K)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χback" => (χg ≫ (G.innerIso g⁻¹).hom)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "Aback" => conjugateRepresentation χg g⁻¹ Ag
set_option hygiene false in
local notation "zg" => unitaryConjugateParameter χ g
set_option hygiene false in
local notation "zback" => unitaryConjugateParameter χg g⁻¹
set_option hygiene false in
local notation "hback" => (conjugationAnchor_inv χ g).symm

/-- The return parabolic for the actual inverse conjugating point. -/
abbrev inverseTarget : ParabolicPresentation χback K := changeAnchor hback P

private def inverseTwistIso (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    twistAt χback Aback (zback (zg z)) ≅ changeInducingAnchor hback (twistAt χ A z) :=
  let hM := DynamicCoefficientConjugation.levi_mem_conjugation χ g
  let hM' := DynamicCoefficientConjugation.levi_mem_conjugation χg g⁻¹
  let e₁ := literalConjugateTwistIso χ g A z
  let e₂ := literalConjugateTwistIso χg g⁻¹ Ag (zg z)
  let e₃ := conjugationCompAt g g⁻¹ hM hM' 1 (inv_mul_cancel g)
    (anchorMembership hback) (twistAt χ A z)
  undoSuccessiveTwistIdentifications g g⁻¹ hM hM'
    (A := twistAt χ A z) (B := twistAt χg Ag (zg z)) (C := twistAt χback Aback (zback (zg z)))
    e₁ e₂ e₃

/-- Identify the inverse-conjugated target with the actual original
coefficient fiber, using the published inverse inducing pullback. -/
def inverseEquiv (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  coefficientEquivOfAnchorIso hback P hG hK
    (twistAt χback Aback (zback (zg z))) (twistAt χ A z) (inverseTwistIso χ g A z)

end Inverse

end Langlands.Plancherel.ActualConjugateLeviFiberTransport
