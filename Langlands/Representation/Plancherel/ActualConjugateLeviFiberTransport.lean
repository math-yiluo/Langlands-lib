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

section SameCarrier

variable {H : Type u} [Group H] [TopologicalSpace H] {M N₁ N₂ N : Subgroup H}
  (B : SmoothRep.{0, u, uV} ℂ M)

/-- For subgroups of one group and characters `α`, `β` with open kernels, a
twist of a pullback of `B` and a pullback of a twist of `B` have the same
carrier; the identity linear map intertwines them when the two pullback
isomorphisms agree pointwise and the characters correspond. -/
def twistPullbackEquiv (e e' : N ≃ₜ* M) (α : M →* ℂˣ) (β : N →* ℂˣ)
    (hα : IsOpen (α.ker : Set M)) (hβ : IsOpen (β.ker : Set N))
    (he : ∀ n, e n = e' n) (h : ∀ n, β n = α (e' n)) :
    ((SmoothRep.pullback e B).twist β hβ).representation.Equiv
      (SmoothRep.pullback e' (B.twist α hα)).representation where
  toLinearEquiv := LinearEquiv.refl ℂ B
  isIntertwining' n := by
    ext v
    change (β n : ℂ) • B.representation (e n) v =
      (α (e' n) : ℂ) • B.representation (e' n) v
    rw [h, he]

/-- `twistPullbackEquiv` is the identity linear map of the carrier of `B`. -/
theorem twistPullbackEquiv_linear_heq (e e' : N ≃ₜ* M) (α : M →* ℂˣ) (β : N →* ℂˣ)
    (hα : IsOpen (α.ker : Set M)) (hβ : IsOpen (β.ker : Set N))
    (he : ∀ n, e n = e' n) (h : ∀ n, β n = α (e' n)) :
    HEq (twistPullbackEquiv B e e' α β hα hβ he h).toLinearEquiv (LinearEquiv.refl ℂ B) :=
  HEq.rfl

/-- For subgroups of one group and characters `α`, `β` with open kernels, a
twist of a twofold pullback of `B` and a pullback of a twist of `B` have the
same carrier; the identity linear map intertwines them when the composite of
the two pullback isomorphisms agrees pointwise with the third and the
characters correspond. -/
def twistPullbackPullbackEquiv (e₁ : N₁ ≃ₜ* M) (e₂ : N ≃ₜ* N₁) (e : N ≃ₜ* M)
    (α : M →* ℂˣ) (β : N →* ℂˣ)
    (hα : IsOpen (α.ker : Set M)) (hβ : IsOpen (β.ker : Set N))
    (he : ∀ n, e₁ (e₂ n) = e n) (h : ∀ n, β n = α (e n)) :
    ((SmoothRep.pullback e₂ (SmoothRep.pullback e₁ B)).twist β hβ).representation.Equiv
      (SmoothRep.pullback e (B.twist α hα)).representation where
  toLinearEquiv := LinearEquiv.refl ℂ B
  isIntertwining' n := by
    ext v
    change (β n : ℂ) • B.representation (e₁ (e₂ n)) v =
      (α (e n) : ℂ) • B.representation (e n) v
    rw [h, he]

/-- `twistPullbackPullbackEquiv` is the identity linear map of the carrier of
`B`. -/
theorem twistPullbackPullbackEquiv_linear_heq (e₁ : N₁ ≃ₜ* M) (e₂ : N ≃ₜ* N₁)
    (e : N ≃ₜ* M) (α : M →* ℂˣ) (β : N →* ℂˣ)
    (hα : IsOpen (α.ker : Set M)) (hβ : IsOpen (β.ker : Set N))
    (he : ∀ n, e₁ (e₂ n) = e n) (h : ∀ n, β n = α (e n)) :
    HEq (twistPullbackPullbackEquiv B e₁ e₂ e α β hα hβ he h).toLinearEquiv
      (LinearEquiv.refl ℂ B) :=
  HEq.rfl

/-- For subgroups of one group and characters `β`, `δ` with open kernels, a
twist of a twofold pullback of `B` and a pullback of a twist of another
pullback of `B` have the same carrier; the identity linear map intertwines
them when the two composites of pullback isomorphisms agree pointwise and the
characters correspond. -/
def twistPullbackPullbackTwistEquiv (e₁ : N₁ ≃ₜ* M) (e₂ : N ≃ₜ* N₁)
    (e₃ : N ≃ₜ* N₂) (e₄ : N₂ ≃ₜ* M) (β : N →* ℂˣ) (δ : N₂ →* ℂˣ)
    (hβ : IsOpen (β.ker : Set N)) (hδ : IsOpen (δ.ker : Set N₂))
    (he : ∀ n, e₁ (e₂ n) = e₄ (e₃ n)) (h : ∀ n, β n = δ (e₃ n)) :
    ((SmoothRep.pullback e₂ (SmoothRep.pullback e₁ B)).twist β hβ).representation.Equiv
      (SmoothRep.pullback e₃ ((SmoothRep.pullback e₄ B).twist δ hδ)).representation where
  toLinearEquiv := LinearEquiv.refl ℂ B
  isIntertwining' n := by
    ext v
    change (β n : ℂ) • B.representation (e₁ (e₂ n)) v =
      (δ (e₃ n) : ℂ) • B.representation (e₄ (e₃ n)) v
    rw [h, he]

/-- `twistPullbackPullbackTwistEquiv` is the identity linear map of the carrier
of `B`. -/
theorem twistPullbackPullbackTwistEquiv_linear_heq (e₁ : N₁ ≃ₜ* M) (e₂ : N ≃ₜ* N₁)
    (e₃ : N ≃ₜ* N₂) (e₄ : N₂ ≃ₜ* M) (β : N →* ℂˣ) (δ : N₂ →* ℂˣ)
    (hβ : IsOpen (β.ker : Set N)) (hδ : IsOpen (δ.ker : Set N₂))
    (he : ∀ n, e₁ (e₂ n) = e₄ (e₃ n)) (h : ∀ n, β n = δ (e₃ n)) :
    HEq (twistPullbackPullbackTwistEquiv B e₁ e₂ e₃ e₄ β δ hβ hδ he h).toLinearEquiv
      (LinearEquiv.refl ℂ B) :=
  HEq.rfl

end SameCarrier

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

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The parabolic of a presentation is the semidirect product of the literal
Levi of its anchor and its unipotent radical. -/
theorem fiberDecomposition {χ : Cochar} {K : OpenSubgroup Gpts} (P : ParabolicPresentation χ K) :
    IsSemidirectDecomposition (parabolic P.cocharacter) (levi χ) (radical P.cocharacter) :=
  commonDecomposition χ P.cocharacter P.centralizer_eq

omit [LocallyOfFiniteType G.X.hom] in
/-- The unipotent radical of the parabolic of a presentation is closed. -/
theorem fiberRadicalClosed {χ : Cochar} {K : OpenSubgroup Gpts} (P : ParabolicPresentation χ K) :
    IsClosed (radical P.cocharacter : Set Gpts) :=
  radical_isClosed P.cocharacter

private abbrev fiberOf {χ : Cochar} {K : OpenSubgroup Gpts} (P : ParabolicPresentation χ K)
    (B : SmoothRep.{0, u, uV} ℂ (levi χ)) :=
  leviProductInducedCoefficientObject (fiberDecomposition P) (fiberRadicalClosed P) B

/-- Reuse the same parabolic and Iwasawa factorization over the equal Levi. -/
def changeAnchor {χ φ : Cochar} (h : χ = φ) {K : OpenSubgroup Gpts}
    (P : ParabolicPresentation χ K) : ParabolicPresentation φ K where
  cocharacter := P.cocharacter
  centralizer_eq := P.centralizer_eq.trans (congrArg Dynamic.centralizer h)
  iwasawa := P.iwasawa

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Equal Levi anchors give the same literal Levi subgroup, presented as
conjugation by the identity point. -/
theorem anchorMembership {χ φ : Cochar} (h : χ = φ) (x : Gpts) :
    x ∈ levi φ ↔ (1 : Gpts)⁻¹ * x * 1 ∈ levi χ := by
  subst φ
  simp only [inv_one, one_mul, mul_one]

/- The pullback along the identity of points between the Levi subgroups of two
equal anchors, written with the topological-group structure that
`CoefficientConjugation.leviCoefficientLeftTranslation` derives from
`NonarchimedeanGroup`, so that the coefficient fiber induced from a pullback is
literally the target of the forward left translation by the identity point. -/
set_option hygiene false in
local notation "anchorPullback " h:max =>
  (@conjugationFunctor Gpts _ _ NonarchimedeanGroup.toIsTopologicalGroup 1 _ _ (anchorMembership h))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The parabolic of a changed anchor is the original parabolic, presented as
conjugation by the identity point. -/
theorem changeAnchor_parabolicMembership {χ φ : Cochar} (h : χ = φ) {K : OpenSubgroup Gpts}
    (P : ParabolicPresentation χ K) (x : Gpts) :
    x ∈ parabolic (changeAnchor h P).cocharacter ↔
      (1 : Gpts)⁻¹ * x * 1 ∈ parabolic P.cocharacter := by
  simp only [changeAnchor, inv_one, one_mul, mul_one]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The unipotent radical of a changed anchor is the original one, presented as
conjugation by the identity point. -/
theorem changeAnchor_radicalMembership {χ φ : Cochar} (h : χ = φ) {K : OpenSubgroup Gpts}
    (P : ParabolicPresentation χ K) (x : Gpts) :
    x ∈ radical (changeAnchor h P).cocharacter ↔
      (1 : Gpts)⁻¹ * x * 1 ∈ radical P.cocharacter := by
  simp only [changeAnchor, inv_one, one_mul, mul_one]

/-- Unimodularity of the actual unipotent radical, stated with the topology,
local compactness and Haar structures used for the coefficient fibers here. -/
theorem radicalUnimodular (ψ : Cochar) (hG : IsConnectedReductive G) :
    IsUnimodularModulus (radical ψ) (radical_isClosed ψ) :=
  DynamicOppositeCanonicalScalar.radical_unimodular ψ hG

/-- The coefficient-fiber comparison for a change of anchor: the same-Levi
transport along an inducing equivalence, followed by the inverse of the product
left translation by the identity point. -/
private def coefficientEquivOfAnchorEquiv {χ φ : Cochar} (h : χ = φ) {K : OpenSubgroup Gpts}
    (P : ParabolicPresentation χ K) (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Gpts))
    (A : SmoothRep.{0, u, uV} ℂ (levi φ)) (B : SmoothRep.{0, u, uV} ℂ (levi χ))
    (e : A.representation.Equiv ((anchorPullback h).obj B).representation) :
    (fiberOf (changeAnchor h P) A).representation.Equiv
      (fiberOf P B).representation :=
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K hK (changeAnchor h P).cocharacter (changeAnchor h P).iwasawa
  (coefficientCongr
      (fiberDecomposition (changeAnchor h P))
      (fiberRadicalClosed (changeAnchor h P))
      (radicalUnimodular (changeAnchor h P).cocharacter hG) e).trans
    (CoefficientConjugation.leviCoefficientLeftTranslation
      (fiberDecomposition P)
      (fiberDecomposition (changeAnchor h P))
      1 (changeAnchor_parabolicMembership h P) (anchorMembership h)
      (changeAnchor_radicalMembership h P)
      (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor h P))
      (radicalUnimodular P.cocharacter hG)
      (radicalUnimodular (changeAnchor h P).cocharacter hG)
      B).symm

/-- The anchor-change comparison unfolds to the explicit composite. -/
private theorem coefficientEquivOfAnchorEquiv_eq {χ φ : Cochar} (h : χ = φ)
    {K : OpenSubgroup Gpts} (P : ParabolicPresentation χ K) (hG : IsConnectedReductive G)
    (hK : IsCompact (K : Set Gpts))
    (A : SmoothRep.{0, u, uV} ℂ (levi φ)) (B : SmoothRep.{0, u, uV} ℂ (levi χ))
    (e : A.representation.Equiv ((anchorPullback h).obj B).representation) :
    letI := quotientCompact K hK P.cocharacter P.iwasawa
    letI := quotientCompact K hK (changeAnchor h P).cocharacter (changeAnchor h P).iwasawa
    coefficientEquivOfAnchorEquiv h P hG hK A B e =
      (coefficientCongr (fiberDecomposition (changeAnchor h P))
          (fiberRadicalClosed (changeAnchor h P))
          (radicalUnimodular (changeAnchor h P).cocharacter hG) e).trans
        (CoefficientConjugation.leviCoefficientLeftTranslation
          (fiberDecomposition P) (fiberDecomposition (changeAnchor h P))
          1 (changeAnchor_parabolicMembership h P) (anchorMembership h)
          (changeAnchor_radicalMembership h P)
          (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor h P))
          (radicalUnimodular P.cocharacter hG)
          (radicalUnimodular (changeAnchor h P).cocharacter hG) B).symm :=
  rfl

private theorem leviConjugation_symm_coe (χ : Cochar) (g : Gpts)
    (m : levi (χ ≫ (G.innerIso g).hom)) :
    (((leviConjugation χ g).symm m : levi χ) : Gpts) = g⁻¹ * m * g := by
  rw [← DynamicCoefficientConjugation.conjugationEquiv_eq]
  rfl

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
set_option quotPrecheck false in
local notation "χst'" => (χ ≫ (G.innerIso (s * t : Gpts)).hom)
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
set_option hygiene false in
local notation "hmul'" => conjugationAnchor_mul_points χ s t

/-- The target parabolic for two successive transports is the same actual
parabolic, presented over the twice-conjugated Levi anchor. -/
abbrev multiplicationTarget (R : ParabolicPresentation χst K) : ParabolicPresentation χts K :=
  changeAnchor (hmul).symm R

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `conjugationAnchor_mul`, with the product formed in the group of rational
points, as in `leviConjugation χ (s * t)` and `unitaryConjugateParameter χ (s * t)`. -/
theorem conjugationAnchor_mul_points : χts = χst' :=
  conjugationAnchor_mul χ s t

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The twice-conjugated Levi is the product-conjugated Levi, presented as
conjugation by the identity point. -/
theorem multiplication_anchorMembership (x : Gpts) :
    x ∈ levi χts ↔ (1 : Gpts)⁻¹ * x * 1 ∈ levi χst' :=
  anchorMembership (hmul').symm x

/-- Successive inverse conjugation by `s` and then by `t` is inverse
conjugation by `s * t` after the identity of points. -/
theorem multiplication_point_eq (n : levi χts) :
    (leviConjugation χ t).symm ((leviConjugation χt s).symm n) =
      (leviConjugation χ (s * t)).symm
        (conjugationEquiv 1 (multiplication_anchorMembership χ s t) n) := by
  apply Subtype.ext
  simp only [leviConjugation_symm_coe, conjugationEquiv_apply, mul_inv_rev, inv_one,
    one_mul, mul_one, mul_assoc]

/-- The literal Levi character at the twice-transported unitary point is the
literal Levi character at the product-transported unitary point, after the
identity of points between the two equal Levi subgroups. -/
theorem multiplication_character_eq (z : unitaryUnramifiedCharacters (normCharacters χ))
    (n : levi χts) :
    (parameterTransport χts (unitaryParameter χts (zts (zt z)))).val.toMonoidHom n =
      (parameterTransport χst' (unitaryParameter χst' (zst z))).val.toMonoidHom
        (conjugationEquiv 1 (multiplication_anchorMembership χ s t) n) := by
  change (parameterTransport χts (unitaryParameter χts (zts (zt z)))).val n =
      (parameterTransport χst' (unitaryParameter χst' (zst z))).val
        (conjugationEquiv 1 (multiplication_anchorMembership χ s t) n)
  rw [unitaryParameter_conjugation_apply χt s (zt z), unitaryParameter_conjugation_apply χ t z,
    unitaryParameter_conjugation_apply χ (s * t) z, multiplication_point_eq]

/-- The inducing comparison for two successive conjugations: the identity
linear map of the carrier of `A`, from the twist of the twice-conjugated
representation at the twice-transported unitary point to the anchor change of
the twist of the product-conjugated representation at the product-transported
unitary point. -/
def multiplicationInducingEquiv (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (twistAt χts Ats (zts (zt z))).representation.Equiv
      ((anchorPullback (hmul).symm).obj (twistAt χst Ast (zst z))).representation :=
  (twistPullbackPullbackTwistEquiv A (leviConjugation χ t).symm (leviConjugation χt s).symm
    (conjugationEquiv 1 (multiplication_anchorMembership χ s t)) (leviConjugation χ (s * t)).symm
    (parameterTransport χts (unitaryParameter χts (zts (zt z)))).val.toMonoidHom
    (parameterTransport χst' (unitaryParameter χst' (zst z))).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    (multiplication_point_eq χ s t) (multiplication_character_eq χ s t z) :
    (twistObject χts (unitaryParameter χts (zts (zt z))) Ats).representation.Equiv
      (SmoothRep.pullback (conjugationEquiv 1 (multiplication_anchorMembership χ s t))
        (twistObject χst' (unitaryParameter χst' (zst z)) Ast)).representation)

/-- The inducing comparison for two successive conjugations is the identity
linear map of the carrier of `A`. -/
theorem multiplicationInducingEquiv_linear_heq
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    HEq (multiplicationInducingEquiv χ s t A z).toLinearEquiv (LinearEquiv.refl ℂ A) := by
  delta multiplicationInducingEquiv
  exact twistPullbackPullbackTwistEquiv_linear_heq A _ _ _ _ _ _ _ _
    (multiplication_point_eq χ s t) (multiplication_character_eq χ s t z)

/-- The canonical comparison from the twice-conjugated coefficient fiber to
the direct product-conjugated coefficient fiber at the same parabolic. -/
def multiplicationEquiv (R : ParabolicPresentation χst K)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  coefficientEquivOfAnchorEquiv (hmul).symm R hG hK
    (twistAt χts Ats (zts (zt z))) (twistAt χst Ast (zst z))
    (multiplicationInducingEquiv χ s t A z)

/-- The twice-conjugated fiber comparison is the same-Levi transport along
`multiplicationInducingEquiv`, followed by the inverse of the product left
translation by the identity point. -/
theorem multiplicationEquiv_eq (R : ParabolicPresentation χst K)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    letI := quotientCompact K hK R.cocharacter R.iwasawa
    letI := quotientCompact K hK (changeAnchor (hmul).symm R).cocharacter
      (changeAnchor (hmul).symm R).iwasawa
    multiplicationEquiv χ s t hG A hK R z =
      (coefficientCongr
          (fiberDecomposition (changeAnchor (hmul).symm R))
          (fiberRadicalClosed (changeAnchor (hmul).symm R))
          (radicalUnimodular
            (changeAnchor (hmul).symm R).cocharacter hG)
          (multiplicationInducingEquiv χ s t A z)).trans
        (CoefficientConjugation.leviCoefficientLeftTranslation
          (fiberDecomposition R)
          (fiberDecomposition (changeAnchor (hmul).symm R))
          1 (changeAnchor_parabolicMembership (hmul).symm R) (anchorMembership (hmul).symm)
          (changeAnchor_radicalMembership (hmul).symm R)
          (fiberRadicalClosed R)
          (fiberRadicalClosed (changeAnchor (hmul).symm R))
          (radicalUnimodular R.cocharacter hG)
          (radicalUnimodular
            (changeAnchor (hmul).symm R).cocharacter hG)
          (twistAt χst Ast (zst z))).symm :=
  coefficientEquivOfAnchorEquiv_eq (hmul).symm R hG hK _ _
    (multiplicationInducingEquiv χ s t A z)

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

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The identity-conjugate Levi is the original Levi, presented as conjugation
by the identity point. -/
theorem identity_anchorMembership (x : Gpts) :
    x ∈ levi χone ↔ (1 : Gpts)⁻¹ * x * 1 ∈ levi χ :=
  anchorMembership hone x

/-- Inverse conjugation by the identity point is the identity of points. -/
theorem identity_point_eq (n : levi χone) :
    (leviConjugation χ 1).symm n = conjugationEquiv 1 (identity_anchorMembership χ) n :=
  (DFunLike.congr_fun (DynamicCoefficientConjugation.conjugationEquiv_eq χ 1) n).symm

/-- The literal Levi character at the identity-transported unitary point is the
original literal Levi character, after the identity of points. -/
theorem identity_character_eq (z : unitaryUnramifiedCharacters (normCharacters χ))
    (n : levi χone) :
    (parameterTransport χone
        (unitaryParameter χone (unitaryConjugateParameter χ 1 z))).val.toMonoidHom n =
      (parameterTransport χ (unitaryParameter χ z)).val.toMonoidHom
        (conjugationEquiv 1 (identity_anchorMembership χ) n) := by
  change (parameterTransport χone
      (unitaryParameter χone (unitaryConjugateParameter χ 1 z))).val n =
      (parameterTransport χ (unitaryParameter χ z)).val
        (conjugationEquiv 1 (identity_anchorMembership χ) n)
  rw [unitaryParameter_conjugation_apply χ 1 z, identity_point_eq]

/-- The inducing comparison for the identity arrow: the identity linear map of
the carrier of `A`, from the twist of the identity-conjugate representation at
the identity-transported unitary point to the anchor change of the original
twist. -/
def identityInducingEquiv (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (twistAt χone (conjugateRepresentation χ 1 A)
        (unitaryConjugateParameter χ 1 z)).representation.Equiv
      ((anchorPullback hone).obj (twistAt χ A z)).representation :=
  twistPullbackEquiv A (leviConjugation χ 1).symm
    (conjugationEquiv 1 (identity_anchorMembership χ))
    (parameterTransport χ (unitaryParameter χ z)).val.toMonoidHom
    (parameterTransport χone
      (unitaryParameter χone (unitaryConjugateParameter χ 1 z))).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    (identity_point_eq χ) (identity_character_eq χ z)

/-- The inducing comparison for the identity arrow is the identity linear map
of the carrier of `A`. -/
theorem identityInducingEquiv_linear_heq
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    HEq (identityInducingEquiv χ A z).toLinearEquiv (LinearEquiv.refl ℂ A) := by
  delta identityInducingEquiv
  exact twistPullbackEquiv_linear_heq A _ _ _ _ _ _ (identity_point_eq χ)
    (identity_character_eq χ z)

/-- The target of an identity arrow is canonically the original fiber. -/
def identityEquiv (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  coefficientEquivOfAnchorEquiv hone P hG hK
    (twistAt χone (conjugateRepresentation χ 1 A) (unitaryConjugateParameter χ 1 z))
    (twistAt χ A z) (identityInducingEquiv χ A z)

/-- The identity-arrow fiber comparison is the same-Levi transport along
`identityInducingEquiv`, followed by the inverse of the product left
translation by the identity point. -/
theorem identityEquiv_eq (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    letI := quotientCompact K hK P.cocharacter P.iwasawa
    letI := quotientCompact K hK (changeAnchor hone P).cocharacter (changeAnchor hone P).iwasawa
    identityEquiv χ hG A hK P z =
      (coefficientCongr
          (fiberDecomposition (changeAnchor hone P))
          (fiberRadicalClosed (changeAnchor hone P))
          (radicalUnimodular (changeAnchor hone P).cocharacter hG)
          (identityInducingEquiv χ A z)).trans
        (CoefficientConjugation.leviCoefficientLeftTranslation
          (fiberDecomposition P)
          (fiberDecomposition (changeAnchor hone P))
          1 (changeAnchor_parabolicMembership hone P) (anchorMembership hone)
          (changeAnchor_radicalMembership hone P)
          (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor hone P))
          (radicalUnimodular P.cocharacter hG)
          (radicalUnimodular (changeAnchor hone P).cocharacter hG)
          (twistAt χ A z)).symm :=
  coefficientEquivOfAnchorEquiv_eq hone P hG hK _ _ (identityInducingEquiv χ A z)

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
set_option quotPrecheck false in
local notation "χback'" => (χg ≫ (G.innerIso (g⁻¹ : Gpts)).hom)
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
set_option hygiene false in
local notation "hback'" => (conjugationAnchor_inv_points χ g).symm

/-- The return parabolic for the actual inverse conjugating point. -/
abbrev inverseTarget : ParabolicPresentation χback K := changeAnchor hback P

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `conjugationAnchor_inv`, with the inverse formed in the group of rational
points, as in `leviConjugation χg g⁻¹` and `unitaryConjugateParameter χg g⁻¹`. -/
theorem conjugationAnchor_inv_points : χback' = χ :=
  (conjugationAnchor_mul χ g⁻¹ g).trans (by
    rw [inv_mul_cancel, conjugationAnchor_one])

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The Levi conjugated by `g` and then by `g⁻¹` is the original Levi,
presented as conjugation by the identity point. -/
theorem inverse_anchorMembership (x : Gpts) :
    x ∈ levi χback' ↔ (1 : Gpts)⁻¹ * x * 1 ∈ levi χ :=
  anchorMembership hback' x

/-- Inverse conjugation by `g⁻¹` and then by `g` is the identity of points. -/
theorem inverse_point_eq (n : levi χback') :
    (leviConjugation χ g).symm ((leviConjugation χg g⁻¹).symm n) =
      conjugationEquiv 1 (inverse_anchorMembership χ g) n := by
  apply Subtype.ext
  simp only [leviConjugation_symm_coe, conjugationEquiv_apply, inv_inv, inv_one, one_mul,
    mul_one, mul_assoc, inv_mul_cancel_left, inv_mul_cancel]

/-- The literal Levi character at the unitary point transported by `g` and then
by `g⁻¹` is the original literal Levi character, after the identity of points. -/
theorem inverse_character_eq (z : unitaryUnramifiedCharacters (normCharacters χ))
    (n : levi χback') :
    (parameterTransport χback' (unitaryParameter χback' (zback (zg z)))).val.toMonoidHom n =
      (parameterTransport χ (unitaryParameter χ z)).val.toMonoidHom
        (conjugationEquiv 1 (inverse_anchorMembership χ g) n) := by
  change (parameterTransport χback' (unitaryParameter χback' (zback (zg z)))).val n =
      (parameterTransport χ (unitaryParameter χ z)).val
        (conjugationEquiv 1 (inverse_anchorMembership χ g) n)
  rw [unitaryParameter_conjugation_apply χg g⁻¹ (zg z), unitaryParameter_conjugation_apply χ g z,
    inverse_point_eq]

/-- The inducing comparison for the inverse arrow: the identity linear map of
the carrier of `A`, from the twist of the representation conjugated by `g` and
then by `g⁻¹` at the twice-transported unitary point to the anchor change of
the original twist. -/
def inverseInducingEquiv (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (twistAt χback Aback (zback (zg z))).representation.Equiv
      ((anchorPullback hback).obj (twistAt χ A z)).representation :=
  twistPullbackPullbackEquiv A (leviConjugation χ g).symm (leviConjugation χg g⁻¹).symm
    (conjugationEquiv 1 (inverse_anchorMembership χ g))
    (parameterTransport χ (unitaryParameter χ z)).val.toMonoidHom
    (parameterTransport χback' (unitaryParameter χback' (zback (zg z)))).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    (inverse_point_eq χ g) (inverse_character_eq χ g z)

/-- The inducing comparison for the inverse arrow is the identity linear map of
the carrier of `A`. -/
theorem inverseInducingEquiv_linear_heq
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    HEq (inverseInducingEquiv χ g A z).toLinearEquiv (LinearEquiv.refl ℂ A) := by
  delta inverseInducingEquiv
  exact twistPullbackPullbackEquiv_linear_heq A _ _ _ _ _ _ _ (inverse_point_eq χ g)
    (inverse_character_eq χ g z)

/-- Identify the inverse-conjugated target with the actual original
coefficient fiber. -/
def inverseEquiv (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  coefficientEquivOfAnchorEquiv hback P hG hK
    (twistAt χback Aback (zback (zg z))) (twistAt χ A z) (inverseInducingEquiv χ g A z)

/-- The inverse-arrow fiber comparison is the same-Levi transport along
`inverseInducingEquiv`, followed by the inverse of the product left
translation by the identity point. -/
theorem inverseEquiv_eq (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    letI := quotientCompact K hK P.cocharacter P.iwasawa
    letI := quotientCompact K hK (changeAnchor hback P).cocharacter (changeAnchor hback P).iwasawa
    inverseEquiv χ g hG A hK P z =
      (coefficientCongr
          (fiberDecomposition (changeAnchor hback P))
          (fiberRadicalClosed (changeAnchor hback P))
          (radicalUnimodular (changeAnchor hback P).cocharacter hG)
          (inverseInducingEquiv χ g A z)).trans
        (CoefficientConjugation.leviCoefficientLeftTranslation
          (fiberDecomposition P)
          (fiberDecomposition (changeAnchor hback P))
          1 (changeAnchor_parabolicMembership hback P) (anchorMembership hback)
          (changeAnchor_radicalMembership hback P)
          (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor hback P))
          (radicalUnimodular P.cocharacter hG)
          (radicalUnimodular (changeAnchor hback P).cocharacter hG)
          (twistAt χ A z)).symm :=
  coefficientEquivOfAnchorEquiv_eq hback P hG hK _ _ (inverseInducingEquiv χ g A z)

end Inverse

end Langlands.Plancherel.ActualConjugateLeviFiberTransport
