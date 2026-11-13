import Langlands.Representation.CuspidalSupport.BernsteinBlockCenterFunctionsLevi
import Langlands.Representation.CuspidalSupport.BernsteinBlockCenterFunctionsInvariantCenter
import Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsReduction
import Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceStatement
import Langlands.Representation.CuspidalSupport.InducedProgeneratorCenterInclusionStatement
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.CategoryTheory.Renard.GeneratorCenter

/-! # Conditional reduction of Renard VI.10.4, Theorem, first sentence -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uG uW

/-- Derived reduction: Renard VI.10.4, Theorem, first sentence, with Remark 1
(`BernsteinBlockCenterFunctionsStatement`), follows from Renard VI.10.2, Theorem
(`BernsteinBlockHomEquivalenceStatement`), the centre inclusion of Renard VI.10.4, second Lemma,
and the centralizer identity after it, in represented form
(`RepresentedParabolic.InducedProgeneratorCenterInclusionStatement` at carriers in
`Type (max uF uV)`), the invariance of irreducible induction-subquotients under association
(VI.5.4, `BernsteinAssociatedSupportInvarianceStatement`) for every standard family, and the
inclusion `ℨ_D^{W(D)} ⊂ ℨ_Ω` of the proof of VI.10.4
(`BernsteinInvariantCenterInclusionStatement`). -/
def BernsteinBlockCenterFunctionsReductionStatement : Prop :=
  BernsteinBlockHomEquivalenceStatement.{uF, uV} →
    RepresentedParabolic.InducedProgeneratorCenterInclusionStatement.{uF, max uF uV} →
    (∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F]
        (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [LocallyOfFiniteType G.X.hom]
        (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T),
        letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
        letI : TopologicalSpace (rationalPoints G) := pointTopology
        ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
          (family : BernsteinStandardFamily i ν),
          BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family) →
    BernsteinInvariantCenterInclusionStatement.{uF, uV} →
    BernsteinBlockCenterFunctionsStatement.{uF, uV}

/-- Conjugating a commuting pair by an isomorphism. -/
theorem conj_comm_of_comm {C : Type*} [Category C] {A B : C} (e : A ≅ B) (f : A ⟶ A)
    (g : B ⟶ B) (h : (e.hom ≫ g ≫ e.inv) ≫ f = f ≫ (e.hom ≫ g ≫ e.inv)) :
    (e.inv ≫ f ≫ e.hom) ≫ g = g ≫ (e.inv ≫ f ≫ e.hom) := by
  have h' := congrArg (fun t => e.inv ≫ t ≫ e.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h'.symm

/-- The underlying map of an isomorphism of smooth representations is surjective. -/
theorem smoothRep_iso_hom_surjective {H : Type uG} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, uG, uW} ℂ H} (e : A ≅ B) : Function.Surjective (SmoothRep.hom e.hom) :=
  fun y => ⟨SmoothRep.hom e.inv y, by
    change SmoothRep.hom (e.inv ≫ e.hom) y = y
    rw [e.inv_hom_id]
    rfl⟩

/-- Two scalar multiples of a surjection onto a nonzero representation agree only for equal
scalars. -/
theorem smul_eq_of_surjective {H : Type uG} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, uG, uW} ℂ H} [Nontrivial B] (φ : A ⟶ B)
    (hφ : Function.Surjective (SmoothRep.hom φ)) {c d : ℂ} (h : c • φ = d • φ) : c = d := by
  obtain ⟨v, hv⟩ := exists_ne (0 : B)
  obtain ⟨y, rfl⟩ := hφ v
  have h' : c • SmoothRep.hom φ y = d • SmoothRep.hom φ y :=
    congrArg (fun f => SmoothRep.hom f y) h
  by_contra hcd
  apply hv
  have h'' : (c - d) • SmoothRep.hom φ y = 0 := by rw [sub_smul, h', sub_self]
  exact (smul_eq_zero.mp h'').resolve_left (sub_ne_zero.mpr hcd)

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinBlockCenterRedInstance1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinBlockCenterRedInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinBlockCenterRedInstance3 : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinBlockCenterRedInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinBlockCenterRedInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinBlockCenterRedInstance10 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinBlockCenterRedInstance6 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinBlockCenterRedInstance7 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinBlockCenterRedInstance8 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual represented standard induction sends surjections to surjections (exactness of
`i_P^G`, Renard VI.1.2). -/
theorem bernsteinStandardRepresentedInduction_map_surjective (I : Finset (SimpleRoot i ν))
    {A B : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))}
    (φ : A ⟶ B) (hφ : Function.Surjective (SmoothRep.hom φ)) :
    Function.Surjective
      (SmoothRep.hom
        ((bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family I).map φ)) := by
  let h := bernsteinStandardRepresentativesGeometric i ν family I
  obtain ⟨hind, -⟩ := RepresentedParabolic.leviParabolicFunctorsExact.{uF, max uF uV} F G
    family.connectedReductive _ _ _
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I)) h.1 h.2.1 h.2.2.1 h.2.2.2
  have hse : SmoothRep.IsShortExact (SmoothRep.hom (SmoothRep.kernelι φ)) (SmoothRep.hom φ) := by
    refine ⟨SmoothRep.subtype_injective _ _, hφ, ?_⟩
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  exact (hind (SmoothRep.kernelι φ) φ hse).2.1

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual represented standard induction is `ℂ`-linear on morphisms. -/
theorem bernsteinStandardRepresentedInduction_map_smul (I : Finset (SimpleRoot i ν))
    {A B : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))}
    (c : ℂ) (φ : A ⟶ B) :
    (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family I).map (c • φ) =
      c • (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family I).map φ := by
  apply ObjectProperty.hom_ext
  ext v
  rfl

/-- For `s` in the stabilizer of `ρ` and `χ ∈ X(M)`, the identity conjugation associates
`(M, ρ ⊗ χs)` with `(M, ρ ⊗ χ)`. -/
theorem twist_mul_stabilizer_associated (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (s χ : unramifiedCharacters
      (fun ψ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) ψ).toMul))
    (hs : Nonempty
      (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) s a.representation ≅
        a.representation)) :
    ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
        (Standard.leviHom i ν (rootSet i ν a.roots)),
      Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) (χ * s)
          a.representation ≅
        rationalIsoPullback c.iso
          (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) χ a.representation)) := by
  obtain ⟨e⟩ := hs
  refine ⟨RationalLeviConjugacy.refl _, ⟨?_⟩⟩
  exact (rationalUnramifiedTwistMulIso (bernsteinLeviScheme i ν a.roots) χ s
      a.representation).symm ≪≫
    SmoothRep.twistIso _ (isOpen_rationalUnramifiedCharacter_ker _ χ) e ≪≫
    (rationalIsoPullbackReflIso _).symm

/-- Key transfer (Renard VI.10.4, proof of the Theorem): if a central `z` of the block acts on
`Π_Ω = i_P^G Π_D` through `I(ζ)` for an endomorphism `ζ` of `Π_D` acting by `c ω` on every map
`Π_D → ρ ⊗ ω`, then `z` acts by `c ω` on `i_P^G(ρ ⊗ ω)`. -/
theorem twistInduction_centerScalar_of_generator
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    [Nontrivial ρ₀]
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (hmem : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))))
    (z : CatCenter (BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)))
    (ζ : End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
    (c : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) → ℂ)
    (hζ : ∀ ω (φ : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
        rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation),
      ζ ≫ φ = c ω • φ)
    (hz : (z.app ⟨_, hmem⟩).hom =
      (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).inv ≫
        (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).map ζ ≫
        (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).hom)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (hω : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))))
    (x : (normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))) :
    SmoothRep.hom (z.app ⟨_, hω⟩).hom x = c ω • x := by
  obtain ⟨φ, hφ⟩ :=
    bernsteinCuspidalDatum_exists_surjective_twist.{uF, uV} i ν family a ρ₀ j hj ω
  let eΩ := bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
    (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)
  let eω := bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
    (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)
  let g := eΩ.inv ≫
    (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).map φ ≫ eω.hom
  have hg : Function.Surjective (SmoothRep.hom g) := by
    intro y
    obtain ⟨y₁, rfl⟩ := smoothRep_iso_hom_surjective eω y
    obtain ⟨y₂, rfl⟩ := bernsteinStandardRepresentedInduction_map_surjective i ν family a.roots
      φ hφ y₁
    obtain ⟨y₃, rfl⟩ := smoothRep_iso_hom_surjective eΩ.symm y₂
    exact ⟨y₃, rfl⟩
  have hnat := z.naturality
    (X := (⟨_, hmem⟩ : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)))
    (Y := ⟨_, hω⟩) (ObjectProperty.homMk g)
  have h2 : g ≫ (z.app ⟨_, hω⟩).hom = c ω • g := by
    have h1 := congrArg (fun f => f.hom) hnat
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom] at h1
    rw [h1, hz]
    simp only [g, eΩ, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, hζ ω φ, bernsteinStandardRepresentedInduction_map_smul,
      Linear.smul_comp, Linear.comp_smul]
  obtain ⟨y, rfl⟩ := hg x
  exact congrArg (fun f => SmoothRep.hom f y) h2

/-- Scalars of a central element on `i_P^G(ρ ⊗ ω)` are unique (the induction is nonzero). -/
theorem twistInduction_centerScalar_unique
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (z : CatCenter (BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)))
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (hω : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))))
    {c d : ℂ} (hc : ∀ x, SmoothRep.hom (z.app ⟨_, hω⟩).hom x = c • x)
    (hd : ∀ x, SmoothRep.hom (z.app ⟨_, hω⟩).hom x = d • x) : c = d := by
  have := nontrivial_twistInduction.{uF, uV} i ν family a ω
  exact SmoothRep.scalar_unique _ hc hd

/-- Scalars of a central element on `i_P^G(ρ ⊗ ω)` and `i_P^G(ρ ⊗ ω')` agree when
`(M, ρ ⊗ ω)` and `(M, ρ ⊗ ω')` are associated (Renard VI.5.4 through a common irreducible
subquotient). -/
theorem twistInduction_centerScalar_eq_of_associated
    (hP4 : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (z : CatCenter (BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)))
    (ω ω' : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (hassoc : ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
        (Standard.leviHom i ν (rootSet i ν a.roots)),
      Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation ≅
        rationalIsoPullback c.iso
          (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω' a.representation)))
    (hω : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))))
    (hω' : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω' a.representation))))
    {c c' : ℂ} (hc : ∀ x, SmoothRep.hom (z.app ⟨_, hω⟩).hom x = c • x)
    (hc' : ∀ x, SmoothRep.hom (z.app ⟨_, hω'⟩).hom x = c' • x) : c = c' := by
  obtain ⟨π, hπ, h1, h2⟩ := exists_common_irreducible_subquotient.{uF, uV} i ν family hP4 a a
    ω ω' hassoc
  have hP : ∀ {V W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)},
      bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V →
      SmoothRep.IsSubquotient W V →
      bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) W :=
    fun hV hWV => bernsteinSaturatedBlockProperty_of_isSubquotient.{uF, uV} i ν family hV hWV
  have hπblock := bernsteinSaturatedBlockProperty_of_isSubquotient.{uF, uV} i ν family hω h1
  have e1 := SmoothRep.fullSubcategory_centerScalar_of_isSubquotient hP z hω hπblock h1 hc
  have e2 := SmoothRep.fullSubcategory_centerScalar_of_isSubquotient hP z hω' hπblock h2 hc'
  have := Langlands.Classification.SegmentHeadSupport.nontrivial_of_isIrreducible hπ
  exact SmoothRep.scalar_unique _ e1 e2

/-- Renard VI.10.4, second Lemma and the centralizer identity after it (P2), in the form used
here: every central endomorphism of `I(Π_D)` is `I(ζ)` for a central `ζ` of `End_M(Π_D)`. -/
theorem bernsteinInducedCenter_exists
    (hP2 : RepresentedParabolic.InducedProgeneratorCenterInclusionStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (x : End ((bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).obj
      (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)))
    (hx : x ∈ Subring.center _) :
    ∃ ζ ∈ Subring.center
        (End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)),
      x = (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).map ζ := by
  let A := bernsteinStandardRepresentativesGeometric i ν family a.roots
  have h := hP2 F G family.connectedReductive
    (Standard.parabolicScheme i ν (rootSet i ν a.roots)) (bernsteinLeviScheme i ν a.roots)
    (Standard.unipotentScheme i ν (rootSet i ν a.roots))
    (Standard.parabolicHom i ν (rootSet i ν a.roots))
    (Standard.leviToParabolic i ν (rootSet i ν a.roots))
    (Standard.unipotentToParabolic i ν (rootSet i ν a.roots))
    A.1 A.2.1 A.2.2.1 A.2.2.2 a.representation a.irreducible (a.isSupercuspidal i ν family)
    ρ₀ hρ₀ j hj
  obtain ⟨ζ, hζ, hxζ, -⟩ := (Set.ext_iff.mp h x).mp hx
  exact ⟨ζ, hζ, hxζ⟩

/-- Conjugating the component at `Π_Ω` of a central element of the block by
`I(Π_D) ≅ Π_Ω` gives a central endomorphism of `I(Π_D)`. -/
theorem catCenter_conj_mem_center
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hmem : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))))
    (z : CatCenter (BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))) :
    (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).hom ≫
        (z.app ⟨_, hmem⟩).hom ≫
        (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).inv ∈
      Subring.center (End ((bernsteinStandardRepresentedInductionFunctor.{uF, uV}
        i ν family a.roots).obj
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))) := by
  refine (Subring.mem_center_iff (R := End
    ((bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).obj
      (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)))).mpr
    fun g => ?_
  let eΩ := bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
    (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)
  have hnat := z.naturality
    (X := (⟨_, hmem⟩ : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)))
    (Y := ⟨_, hmem⟩) (ObjectProperty.homMk (eΩ.inv ≫ g ≫ eΩ.hom))
  have h1 := congrArg (fun f => f.hom) hnat
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom] at h1
  exact conj_comm_of_comm eΩ.symm (z.app ⟨_, hmem⟩).hom g h1

/-- If `I(ζ)` is central in `End(I(Π_D))`, its conjugate by `I(Π_D) ≅ Π_Ω` is the component at
`Π_Ω` of a central element of the block (Morita, Renard VI.10.2). -/
theorem catCenter_exists_of_inducedCenter
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hmem : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))))
    (hEq : (preadditiveCoyonedaObj (⟨_, hmem⟩ :
      BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))).IsEquivalence)
    (ζ : End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
    (hζ : (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).map ζ ∈
      Subring.center (End ((bernsteinStandardRepresentedInductionFunctor.{uF, uV}
        i ν family a.roots).obj
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)))) :
    ∃ z : CatCenter (BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)),
      (z.app ⟨_, hmem⟩).hom =
        (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).inv ≫
          (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).map ζ ≫
          (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).hom := by
  let eΩ := bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
    (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)
  let P : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a) := ⟨_, hmem⟩
  have hc : (ObjectProperty.homMk
      (eΩ.inv ≫ (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).map ζ ≫
        eΩ.hom) : P ⟶ P) ∈ Subring.center (End P) := by
    refine (Subring.mem_center_iff (R := End P)).mpr fun f => ?_
    apply ObjectProperty.hom_ext
    have hcomm := (Subring.mem_center_iff (R := End
      ((bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).obj
        (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)))).mp hζ
      (eΩ.hom ≫ f.hom ≫ eΩ.inv)
    exact conj_comm_of_comm eΩ _ f.hom hcomm.symm
  obtain ⟨z, hz⟩ := Renard.generatorCenterEvaluation_surjective P ⟨_, hc⟩
  exact ⟨z, congrArg (fun t => t.val.hom) hz⟩

/-- Renard VI.10.4, Theorem, first sentence, with Remark 1, at a fixed cuspidal datum `a`, from
VI.10.2, Theorem (`BernsteinBlockHomEquivalenceStatement`), the centre inclusion of VI.10.4, second
Lemma (the represented `InducedProgeneratorCenterInclusionStatement`), VI.5.4 for the family
(`BernsteinAssociatedSupportInvarianceStatement`) and the inclusion `ℨ_D^{W(D)} ⊂ ℨ_Ω`
(`BernsteinInvariantCenterInclusionStatement`). -/
theorem bernsteinBlockCenterFunctions_of_inputs
    (hP1 : BernsteinBlockHomEquivalenceStatement.{uF, uV})
    (hP2 : RepresentedParabolic.InducedProgeneratorCenterInclusionStatement.{uF, max uF uV})
    (hP4 : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (hP5 : BernsteinInvariantCenterInclusionStatement.{uF, uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    let X := unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
    let twist : X →
        SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
      fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
    let ind : X → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
      (normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots (twist ω))
    let Assoc : X → X → Prop := fun ω ω' =>
      ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
          (Standard.leviHom i ν (rootSet i ν a.roots)),
        Nonempty (twist ω ≅ rationalIsoPullback c.iso (twist ω'))
    let regular := unramifiedRegularFunctions
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
    let invariant : Set (X → ℂ) :=
      {f | f ∈ regular ∧ ∀ ω ω', Assoc ω ω' → f ω = f ω'}
    (∀ ω, bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      (ind ω)) ∧
    ∃ O : Subalgebra ℂ (X → ℂ), (O : Set (X → ℂ)) = invariant ∧
      ∃ e : CatCenter (BernsteinSaturatedBlock i ν family
          (bernsteinInertialClass i ν family a)) ≃+* O,
        ∀ (z : CatCenter (BernsteinSaturatedBlock i ν family
            (bernsteinInertialClass i ν family a))) (ω : X)
          (hω : bernsteinSaturatedBlockProperty i ν family
            (bernsteinInertialClass i ν family a) (ind ω)),
          ∀ x : ind ω, SmoothRep.hom (z.app ⟨ind ω, hω⟩).hom x = (e z : X → ℂ) ω • x := by
  intro X twist ind Assoc regular invariant
  have hblock : ∀ ω, bernsteinSaturatedBlockProperty i ν family
      (bernsteinInertialClass i ν family a) (ind ω) :=
    fun ω => twistInduction_mem_saturatedBlock.{uF, uV} i ν family a ω
  refine ⟨hblock, ?_⟩
  obtain ⟨ρ₀, j, hρ₀, hj⟩ :=
    bernsteinCuspidalDatum_exists_normKernelConstituent.{uF, uV} i ν family a
  have : Nontrivial ρ₀ :=
    Langlands.Classification.SegmentHeadSupport.nontrivial_of_isIrreducible hρ₀
  obtain ⟨hmem, hEq⟩ := hP1 F G T i ν family a ρ₀ hρ₀ j hj
  obtain ⟨Ψ, hΨinj, hΨrange, hΨ⟩ :=
    bernsteinLeviCenterVarietyStatement_holds.{uF, uV} F G T i ν family a ρ₀ hρ₀ j hj
  have hζex : ∀ z : CatCenter (BernsteinSaturatedBlock i ν family
      (bernsteinInertialClass i ν family a)),
      ∃ ζ : End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀),
        ζ ∈ Subring.center
          (End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)) ∧
        (z.app ⟨_, hmem⟩).hom =
          (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
              (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).inv ≫
            (bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots).map ζ ≫
            (bernsteinStandardRepresentedInductionIso.{uF, uV} i ν family a.roots
              (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)).hom := by
    intro z
    obtain ⟨ζ, hζ, hx⟩ := bernsteinInducedCenter_exists.{uF, uV} i ν family hP2 a ρ₀ hρ₀ j hj _
      (catCenter_conj_mem_center.{uF, uV} i ν family a ρ₀ hmem z)
    refine ⟨ζ, hζ, ?_⟩
    rw [← hx]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  choose ζ hζc hζz using hζex
  have hζc' : ∀ z, ζ z ∈ Subalgebra.center ℂ
      (End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)) :=
    fun z => Subalgebra.mem_center_iff.mpr ((Subring.mem_center_iff (R := End
      (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))).mp (hζc z))
  have hscal : ∀ (z : CatCenter (BernsteinSaturatedBlock i ν family
      (bernsteinInertialClass i ν family a))) (ω : X)
      (hω : bernsteinSaturatedBlockProperty i ν family
        (bernsteinInertialClass i ν family a) (ind ω)) (x : ind ω),
      SmoothRep.hom (z.app ⟨ind ω, hω⟩).hom x = Ψ ⟨ζ z, hζc' z⟩ ω • x :=
    fun z ω hω x => twistInduction_centerScalar_of_generator.{uF, uV} i ν family a ρ₀ j hj hmem z
      (ζ z) (fun ω => Ψ ⟨ζ z, hζc' z⟩ ω) (fun ω φ => hΨ ⟨ζ z, hζc' z⟩ ω φ) (hζz z) ω hω x
  have huniq : ∀ (z : CatCenter (BernsteinSaturatedBlock i ν family
      (bernsteinInertialClass i ν family a))) (ω : X) {c : ℂ},
      (∀ x : ind ω, SmoothRep.hom (z.app ⟨ind ω, hblock ω⟩).hom x = c • x) →
      Ψ ⟨ζ z, hζc' z⟩ ω = c :=
    fun z ω _ hc => twistInduction_centerScalar_unique.{uF, uV} i ν family a z ω (hblock ω)
      (hscal z ω (hblock ω)) hc
  let sMon : CatCenter (BernsteinSaturatedBlock i ν family
      (bernsteinInertialClass i ν family a)) →* (X → ℂ) :=
    { toFun := fun z ω => Ψ ⟨ζ z, hζc' z⟩ ω
      map_one' := funext fun ω => huniq 1 ω fun x => (one_smul ℂ x).symm
      map_mul' := fun z w => funext fun ω => huniq (z * w) ω fun x => by
        rw [CatCenter.mul_app']
        change SmoothRep.hom (z.app ⟨ind ω, hblock ω⟩).hom
          (SmoothRep.hom (w.app ⟨ind ω, hblock ω⟩).hom x) = _
        rw [hscal w ω (hblock ω) x, map_smul, hscal z ω (hblock ω) x, smul_smul, mul_comm]
        rfl }
  let sHom : CatCenter (BernsteinSaturatedBlock i ν family
      (bernsteinInertialClass i ν family a)) →+* (X → ℂ) :=
    RingHom.mk' sMon fun z w => funext fun ω => huniq (z + w) ω fun x => by
      rw [CatCenter.app_add]
      change SmoothRep.hom (z.app ⟨ind ω, hblock ω⟩).hom x +
        SmoothRep.hom (w.app ⟨ind ω, hblock ω⟩).hom x = _
      rw [hscal z ω (hblock ω) x, hscal w ω (hblock ω) x, ← add_smul]
      rfl
  let O : Subalgebra ℂ (X → ℂ) :=
    { carrier := invariant
      mul_mem' := fun {f g} hf hg => ⟨regular.mul_mem hf.1 hg.1, fun ω ω' h => by
        change f ω * g ω = f ω' * g ω'
        rw [hf.2 ω ω' h, hg.2 ω ω' h]⟩
      add_mem' := fun {f g} hf hg => ⟨regular.add_mem hf.1 hg.1, fun ω ω' h => by
        change f ω + g ω = f ω' + g ω'
        rw [hf.2 ω ω' h, hg.2 ω ω' h]⟩
      algebraMap_mem' := fun c => ⟨regular.algebraMap_mem c, fun _ _ _ => rfl⟩ }
  have hmemO : ∀ z, sHom z ∈ O := by
    intro z
    have hr : Ψ ⟨ζ z, hζc' z⟩ ∈ Set.range Ψ := Set.mem_range_self _
    rw [hΨrange] at hr
    exact ⟨hr.1, fun ω ω' h => twistInduction_centerScalar_eq_of_associated.{uF, uV} i ν family
      hP4 a z ω ω' h (hblock ω) (hblock ω') (hscal z ω (hblock ω)) (hscal z ω' (hblock ω'))⟩
  have := hEq
  have hinj : Function.Injective (sHom.codRestrict O hmemO) := by
    intro z w h
    have h1 : Ψ ⟨ζ z, hζc' z⟩ = Ψ ⟨ζ w, hζc' w⟩ := congrArg Subtype.val h
    have h3 : ζ z = ζ w := congrArg Subtype.val (hΨinj h1)
    have h4 : z.app ⟨_, hmem⟩ = w.app ⟨_, hmem⟩ := by
      apply ObjectProperty.hom_ext
      rw [hζz z, hζz w, h3]
    exact Renard.generatorCenterEvaluation_injective
      (⟨_, hmem⟩ : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))
      (Subtype.ext h4)
  have hsurj : Function.Surjective (sHom.codRestrict O hmemO) := by
    rintro ⟨f, hf⟩
    have hf' : f ∈ invariant := hf
    have hfr : f ∈ Set.range Ψ := by
      rw [hΨrange]
      exact ⟨hf'.1, fun s hs χ => hf'.2 _ _
        (twist_mul_stabilizer_associated.{uF, uV} i ν family a s χ hs)⟩
    obtain ⟨ζ0, rfl⟩ := hfr
    have hyp : ∀ ω ω', Assoc ω ω' → ∀ c : ℂ,
        (∀ φ : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
          twist ω, (ζ0 : End _) ≫ φ = c • φ) →
        ∀ φ' : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
          twist ω', (ζ0 : End _) ≫ φ' = c • φ' := by
      intro ω ω' hA c hc φ'
      obtain ⟨φ, hφ⟩ :=
        bernsteinCuspidalDatum_exists_surjective_twist.{uF, uV} i ν family a ρ₀ j hj ω
      have : Nontrivial (twist ω) :=
        Langlands.Classification.SegmentHeadSupport.nontrivial_of_isIrreducible
          ((isIrreducible_rationalUnramifiedTwist_iff _ ω a.representation).mpr a.irreducible)
      have hcΨ : c = Ψ ζ0 ω := smul_eq_of_surjective φ hφ ((hc φ).symm.trans (hΨ ζ0 ω φ))
      have hωω' : Ψ ζ0 ω = Ψ ζ0 ω' := hf'.2 ω ω' hA
      rw [hcΨ, hωω']
      exact hΨ ζ0 ω' φ'
    have hζ0 : (ζ0 : End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots)
        ρ₀)) ∈ Subring.center
          (End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)) :=
      (Subring.mem_center_iff (R := End
        (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))).mpr
        (Subalgebra.mem_center_iff.mp ζ0.2)
    have hcent := hP5 F G T i ν family a ρ₀ hρ₀ j hj ζ0 hζ0 hyp
    obtain ⟨z, hz⟩ :=
      catCenter_exists_of_inducedCenter.{uF, uV} i ν family a ρ₀ hmem hEq ζ0 hcent
    refine ⟨z, Subtype.ext (funext fun ω => ?_)⟩
    exact huniq z ω fun x => twistInduction_centerScalar_of_generator.{uF, uV} i ν family a ρ₀
      j hj hmem z ζ0 (Ψ ζ0) (hΨ ζ0) hz ω (hblock ω) x
  exact ⟨O, rfl, RingEquiv.ofBijective (sHom.codRestrict O hmemO) ⟨hinj, hsurj⟩,
    fun z ω hω x => hscal z ω hω x⟩

/-- Proof of the reduction: introduce the data of `BernsteinBlockCenterFunctionsStatement` and
apply `bernsteinBlockCenterFunctions_of_inputs`. -/
theorem bernsteinBlockCenterFunctions_reduction :
    BernsteinBlockCenterFunctionsReductionStatement.{uF, uV} := by
  intro hP1 hP2 hP4 hP5 F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family a
  exact bernsteinBlockCenterFunctions_of_inputs i ν family hP1 hP2 (hP4 F G T i ν family) hP5 a

end Langlands.CuspidalSupport
