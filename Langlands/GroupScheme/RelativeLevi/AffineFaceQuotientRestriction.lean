import Langlands.GroupScheme.RelativeLevi.FaceChartOverlapComparison
import Langlands.GroupScheme.RelativeLevi.SplitFaceAffineQuotientTransport

/-! # Linear original vector quotients on arbitrary affine chart overlaps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.VectorGroup

variable {R A : CommRingCat.{u}}

/-- The canonical standard vector comparison along an arbitrary affine morphism. -/
def affineCoefficientIso (b : Spec A ⟶ Spec R) (n : ℕ) :
    (GroupScheme.baseChange b).obj (groupScheme R n) ≅ groupScheme A n :=
  eqToIso (congrArg (fun q => (GroupScheme.baseChange q).obj (groupScheme R n))
    (Spec.map_preimage b).symm) ≪≫ baseChangeIso (Spec.preimage b)

/-- On an actual coefficient morphism this is the original canonical vector isomorphism. -/
theorem affineCoefficientIso_map (ρ : R ⟶ A) (n : ℕ) :
    affineCoefficientIso (Spec.map ρ) n = baseChangeIso (n := n) ρ := by
  have aux (σ : R ⟶ A) (h : Spec.map σ = Spec.map ρ) :
      eqToIso (congrArg (fun q => (GroupScheme.baseChange q).obj (groupScheme R n)) h.symm) ≪≫
        baseChangeIso σ = baseChangeIso (n := n) ρ := by
    have hs : σ = ρ := Spec.map_injective h
    subst σ
    rfl
  exact aux _ (Spec.map_preimage (Spec.map ρ))

end Langlands.GroupScheme.VectorGroup

namespace Langlands.GroupScheme.RelativeLevi

open LocalSplitCell

variable {S : Scheme.{u}} {G H U : GroupScheme S} [IsAffineHom G.X.hom]
  {p : H ⟶ G}

local instance quotientRestriction_ambientAffine {T : Scheme.{u}} (a : T ⟶ S) :
    IsAffineHom ((baseChange a).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom a)
  exact MorphismProperty.pullback_snd G.X.hom a inferInstance

local instance quotientRestriction_affineScheme {A : CommRingCat.{u}} (a : Spec A ⟶ S) :
    IsAffine ((baseChange a).obj G).X.left :=
  isAffine_of_isAffineHom ((baseChange a).obj G).X.hom

namespace AffineParabolicFaceModel

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] {p : H ⟶ G} (M : AffineParabolicFaceModel p)

local instance quotientRestriction_model_coordinate : Fintype M.coordinateType := M.coordinateFintype
local instance quotientRestriction_model_root : Fintype M.rootType := M.rootFintype

abbrev termGroup (d : ℕ) := M.chart.weights.groupScheme d
abbrev layerRank (d : ℕ) := Nat.card (M.chart.weights.exactSupport d)
def termStep (d : ℕ) : M.termGroup (d + 1) ⟶ M.termGroup d := M.chart.weights.step d
def layerProjection (d : ℕ) : M.termGroup d ⟶ VectorGroup.groupScheme R (M.layerRank d) :=
  M.chart.weights.quotientMap d

end AffineParabolicFaceModel

namespace AffineParabolicFaceChart

variable {s t : S} (C : AffineParabolicFaceChart p s) (D : AffineParabolicFaceChart p t)

local instance quotientRestriction_C_coordinate : Fintype C.coordinateType := C.coordinateFintype
local instance quotientRestriction_C_root : Fintype C.rootType := C.rootFintype
local instance quotientRestriction_D_coordinate : Fintype D.coordinateType := D.coordinateFintype
local instance quotientRestriction_D_root : Fintype D.rootType := D.rootFintype

/-- The ORIGINAL restricted quotient, with precisely the canonical vector coefficient map. -/
def restrictionQuotientMap (A : CommRingCat.{u}) (b : Spec A ⟶ Spec C.ring) (d : ℕ) :
    (baseChange b).obj (C.termGroup d) ⟶
      VectorGroup.groupScheme A (Nat.card (C.chart.weights.exactSupport d)) :=
  (baseChange b).map (C.layerProjection d) ≫
    (VectorGroup.affineCoefficientIso (R := CommRingCat.of C.ring) (A := A) b (Nat.card (C.chart.weights.exactSupport d))).hom

/-- Its full kernel is the original restricted next term. -/
theorem isFppfQuotient_restrictionQuotientMap
    (A : CommRingCat.{u}) (b : Spec A ⟶ Spec C.ring) (d : ℕ) :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange b).map (C.termStep d)))
      (C.restrictionQuotientMap A b d) := by
  rw [SubgroupFunctor.range_baseChangeHom]
  exact ((C.isFppfQuotient_layerProjection d).baseChange b).comp_iso
    (VectorGroup.affineCoefficientIso b _)

/-- A proved actual comparison from the original restriction to a full face
model in the direct ambient pullback. -/
structure RestrictionPresentation (A : CommRingCat.{u})
    (b : Spec A ⟶ Spec C.ring) (a : Spec A ⟶ S) (hb : b ≫ C.projection = a) where
  model : AffineParabolicFaceModel ((baseChange a).map p)
  termIso : ∀ d, (baseChange b).obj (C.termGroup d) ≅ model.termGroup d
  term_fac : ∀ d, (termIso d).hom ≫ model.termInclusion d =
    (baseChange b).map (C.termInclusion d) ≫
      (Descent.pullbackComparison C.projection b a hb G).hom
  step_fac : ∀ d, (baseChange b).map (C.termStep d) ≫ (termIso d).hom =
    (termIso (d + 1)).hom ≫ model.termStep d
  quotientIso : ∀ d,
    VectorGroup.groupScheme A (Nat.card (C.chart.weights.exactSupport d)) ≅
      VectorGroup.groupScheme A (model.layerRank d)
  quotient_fac : ∀ d, C.restrictionQuotientMap A b d ≫ (quotientIso d).hom =
    (termIso d).hom ≫ model.layerProjection d
  scalar : ∀ d N,
    (VectorGroup.powerWeightAction (Nat.card (C.chart.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (model.layerRank d) N)
      (quotientIso d).hom

section Coefficients

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (A : Type u) [hA : CommRing A] [hCA : Algebra C.ring A] (hG : IsReductive G)

local instance coefficientRestriction_sourceNontrivial : Nontrivial C.ring := C.point.nontrivial

/-- The actual coefficient-to-direct-model term comparison. -/
def coefficientRestrictionTermIso (d : ℕ) :
    (baseChange (algebraBaseMap C.ring A)).obj (C.termGroup d) ≅
      (C.coefficientModel (CommRingCat.of A) hG).termGroup d :=
  @SplitParabolicFaceChart.affineTransportTermIso C.ring A C.ring.commRing hA inferInstance hCA
    C.coordinateType C.rootType C.coordinateFintype C.rootFintype
    _ inferInstance _ inferInstance C.torus C.rootDatum C.roots C.weight C.chart
    (hG.baseChange C.projection) C.maximal C.fibrewise C.parametrized
    (C.coefficientAmbientIso (CommRingCat.of A)) (C.coefficientChart (CommRingCat.of A) hG) d

/-- Actual ambient compatibility of the coefficient-to-direct-model term comparison. -/
theorem coefficientRestrictionTermIso_fac (d : ℕ) :
    (C.coefficientRestrictionTermIso A hG d).hom ≫
        (C.coefficientModel (CommRingCat.of A) hG).termInclusion d =
      (baseChange (algebraBaseMap C.ring A)).map (C.termInclusion d) ≫
        (C.coefficientAmbientIso (CommRingCat.of A)).hom := by
  dsimp only [AffineParabolicFaceModel.termInclusion,
    coefficientModel, termInclusion, coefficientTorus, id]
  exact @SplitParabolicFaceChart.affineTransportTermIso_hom_comp C.ring A C.ring.commRing hA inferInstance hCA
    C.coordinateType C.rootType C.coordinateFintype C.rootFintype
    _ inferInstance _ inferInstance C.torus C.rootDatum C.roots C.weight C.chart
    (hG.baseChange C.projection) C.maximal C.fibrewise C.parametrized
    (C.coefficientAmbientIso (CommRingCat.of A)) (C.coefficientChart (CommRingCat.of A) hG) d

/-- Actual consecutive-step compatibility of coefficient-to-model term comparison. -/
theorem coefficientRestrictionTermIso_step (d : ℕ) :
    (baseChange (algebraBaseMap C.ring A)).map (C.termStep d) ≫
        (C.coefficientRestrictionTermIso A hG d).hom =
      (C.coefficientRestrictionTermIso A hG (d + 1)).hom ≫
        (C.coefficientModel (CommRingCat.of A) hG).termStep d := by
  dsimp only [AffineParabolicFaceModel.termStep,
    coefficientModel, termStep, id]
  exact @SplitParabolicFaceChart.step_comp_affineTransportTermIso C.ring A C.ring.commRing hA inferInstance hCA
    C.coordinateType C.rootType C.coordinateFintype C.rootFintype
    _ inferInstance _ inferInstance C.torus C.rootDatum C.roots C.weight C.chart
    (hG.baseChange C.projection) C.maximal C.fibrewise C.parametrized
    (C.coefficientAmbientIso (CommRingCat.of A)) (C.coefficientChart (CommRingCat.of A) hG) d

/-- The actual original coefficient quotient compared with the direct model quotient. -/
def coefficientRestrictionQuotientIso (d : ℕ) :
    VectorGroup.groupScheme (CommRingCat.of A) (Nat.card (C.chart.weights.exactSupport d)) ≅
      VectorGroup.groupScheme (CommRingCat.of A)
        ((C.coefficientModel (CommRingCat.of A) hG).layerRank d) :=
  @SplitParabolicFaceChart.affineTransportQuotientIso C.ring A C.ring.commRing hA inferInstance hCA
    C.coordinateType C.rootType C.coordinateFintype C.rootFintype
    _ inferInstance _ inferInstance C.torus C.rootDatum C.roots C.weight C.chart
    (hG.baseChange C.projection) C.maximal C.fibrewise C.parametrized
    (C.coefficientAmbientIso (CommRingCat.of A)) (C.coefficientChart (CommRingCat.of A) hG) d

set_option maxRecDepth 2048 in
/-- The original coefficient quotient square is retained. -/
theorem coefficientRestrictionQuotientIso_fac (d : ℕ) :
    C.restrictionQuotientMap (CommRingCat.of A) (algebraBaseMap C.ring A) d ≫
        (C.coefficientRestrictionQuotientIso A hG d).hom =
      (C.coefficientRestrictionTermIso A hG d).hom ≫
        (C.coefficientModel (CommRingCat.of A) hG).layerProjection d := by
  dsimp only [coefficientRestrictionQuotientIso, coefficientRestrictionTermIso,
    AffineParabolicFaceModel.layerProjection, AffineParabolicFaceModel.layerRank,
    coefficientModel, termGroup, layerProjection, id]
  simpa only [restrictionQuotientMap, layerProjection, algebraBaseMap, VectorGroup.affineCoefficientIso_map,
    FppfQuotientComparison.coefficientQuotient] using
    @SplitParabolicFaceChart.affineTransportQuotientIso_fac C.ring A C.ring.commRing hA inferInstance hCA
    C.coordinateType C.rootType C.coordinateFintype C.rootFintype
    _ inferInstance _ inferInstance C.torus C.rootDatum C.roots C.weight C.chart
    (hG.baseChange C.projection) C.maximal C.fibrewise C.parametrized
    (C.coefficientAmbientIso (CommRingCat.of A)) (C.coefficientChart (CommRingCat.of A) hG) d

/-- The actual original-to-direct-model quotient comparison preserves all scalar powers. -/
theorem coefficientRestrictionQuotientIso_scalar (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.chart.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction
        ((C.coefficientModel (CommRingCat.of A) hG).layerRank d) N)
      (C.coefficientRestrictionQuotientIso A hG d).hom := by
  intro T s x
  exact @SplitParabolicFaceChart.affineTransportQuotientIso_isEquivariant_power C.ring A C.ring.commRing hA inferInstance hCA
    C.coordinateType C.rootType C.coordinateFintype C.rootFintype
    _ inferInstance _ inferInstance C.torus C.rootDatum C.roots C.weight C.chart
    (hG.baseChange C.projection) C.maximal C.fibrewise C.parametrized
    (C.coefficientAmbientIso (CommRingCat.of A)) (C.coefficientChart (CommRingCat.of A) hG) d N T s x

/-- Coefficient restriction derives every actual original-to-model comparison. -/
def coefficientRestrictionPresentation :
    C.RestrictionPresentation (CommRingCat.of A) (algebraBaseMap C.ring A)
      (C.coefficientBaseMap (CommRingCat.of A)) rfl where
  model := C.coefficientModel (CommRingCat.of A) hG
  termIso := C.coefficientRestrictionTermIso A hG
  term_fac := C.coefficientRestrictionTermIso_fac A hG
  step_fac := C.coefficientRestrictionTermIso_step A hG
  quotientIso := C.coefficientRestrictionQuotientIso A hG
  quotient_fac := C.coefficientRestrictionQuotientIso_fac A hG
  scalar := C.coefficientRestrictionQuotientIso_scalar A hG

end Coefficients

/-- Arbitrary affine restriction derives all actual original-to-model quotient data,
including linearity, without nonempty or nontriviality assumptions on the new base. -/
theorem nonempty_restrictionPresentation (hG : IsReductive G)
    (A : CommRingCat.{u}) (b : Spec A ⟶ Spec C.ring) (a : Spec A ⟶ S)
    (hb : b ≫ C.projection = a) : Nonempty (C.RestrictionPresentation A b a hb) := by
  let : Algebra C.ring A := (Spec.preimage b).hom.toAlgebra
  have he : algebraBaseMap C.ring A = b := Spec.map_preimage b
  let P (q : Spec A ⟶ Spec C.ring) : Prop :=
    ∀ (a : Spec A ⟶ S) (h : q ≫ C.projection = a),
      Nonempty (C.RestrictionPresentation A q a h)
  have hp : P (algebraBaseMap C.ring A) := by
    intro a h
    subst a
    exact ⟨C.coefficientRestrictionPresentation A hG⟩
  exact (Eq.mp (congrArg P he) hp) a hb

variable (r : U ⟶ H) (hG : IsReductive G)
  (hp : IsRelativeParabolicSubgroup p) (hr : IsRelativeUnipotentRadical r)
  (A : CommRingCat.{u}) (b : Spec A ⟶ Spec C.ring) (c : Spec A ⟶ Spec D.ring)
  (a : Spec A ⟶ S) (hb : b ≫ C.projection = a) (hc : c ≫ D.projection = a)

/-- The canonical ORIGINAL term comparison is induced by identity in the direct ambient group. -/
def restrictionTermIso (d : ℕ) :
    (baseChange b).obj (C.termGroup d) ≅ (baseChange c).obj (D.termGroup d) := by
  let i := (baseChange b).map (C.termInclusion d) ≫
    (Descent.pullbackComparison C.projection b a hb G).hom
  let j := (baseChange c).map (D.termInclusion d) ≫
    (Descent.pullbackComparison D.projection c a hc G).hom
  have hi := ((C.isClosedSubgroup_termInclusion d).baseChange b).comp_iso
    (Descent.pullbackComparison C.projection b a hb G)
  have hj := ((D.isClosedSubgroup_termInclusion d).baseChange c).comp_iso
    (Descent.pullbackComparison D.projection c a hc G)
  have : Mono i.hom.hom.left := hi.mono
  have : Mono j.hom.hom.left := hj.mono
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨Over.mono_of_mono_left _, rfl⟩
  exact hrep.isoOfIsRepresentedBy
    ⟨Over.mono_of_mono_left _, (C.range_affineRestriction_eq D r hG hp hr A b c a hb hc d).symm⟩

/-- The term comparison retains the exact original ambient tower comparisons. -/
theorem restrictionTermIso_hom_comp (d : ℕ) :
    (C.restrictionTermIso D r hG hp hr A b c a hb hc d).hom ≫
        ((baseChange c).map (D.termInclusion d) ≫
          (Descent.pullbackComparison D.projection c a hc G).hom) =
      (baseChange b).map (C.termInclusion d) ≫
        (Descent.pullbackComparison C.projection b a hb G).hom := by
  unfold restrictionTermIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- Both original restricted consecutive inclusions commute with the canonical term comparison. -/
theorem step_comp_restrictionTermIso (d : ℕ) :
    (baseChange b).map (C.termStep d) ≫
        (C.restrictionTermIso D r hG hp hr A b c a hb hc d).hom =
      (C.restrictionTermIso D r hG hp hr A b c a hb hc (d + 1)).hom ≫
        (baseChange c).map (D.termStep d) := by
  let j := (baseChange c).map (D.termInclusion d) ≫
    (Descent.pullbackComparison D.projection c a hc G).hom
  have hj := ((D.isClosedSubgroup_termInclusion d).baseChange c).comp_iso
    (Descent.pullbackComparison D.projection c a hc G)
  have : Mono j.hom.hom.left := hj.mono
  have hrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  apply hrep.hom_ext
  rw [Category.assoc, C.restrictionTermIso_hom_comp D r hG hp hr A b c a hb hc d,
    ← Category.assoc, ← Functor.map_comp, C.termStep_comp_inclusion,
    Category.assoc, ← Category.assoc ((baseChange c).map (D.termStep d)),
    ← Functor.map_comp, D.termStep_comp_inclusion,
    C.restrictionTermIso_hom_comp D r hG hp hr A b c a hb hc (d + 1)]

/-- The original coefficient vector quotients compared by identity in the direct ambient group. -/
def restrictionQuotientIso (d : ℕ) :
    VectorGroup.groupScheme A (Nat.card (C.chart.weights.exactSupport d)) ≅
      VectorGroup.groupScheme A (Nat.card (D.chart.weights.exactSupport d)) :=
  FppfQuotientComparison.isoOfCompatibleTerms
    ((baseChange b).map (C.termStep d)) ((baseChange c).map (D.termStep d))
    (C.isFppfQuotient_restrictionQuotientMap A b d)
    (D.isFppfQuotient_restrictionQuotientMap A c d)
    (C.restrictionTermIso D r hG hp hr A b c a hb hc d)
    (C.restrictionTermIso D r hG hp hr A b c a hb hc (d + 1))
    (C.step_comp_restrictionTermIso D r hG hp hr A b c a hb hc d)

/-- The comparison retains precisely the two ORIGINAL restricted full quotient maps. -/
theorem restrictionQuotientIso_fac (d : ℕ) :
    C.restrictionQuotientMap A b d ≫
        (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom =
      (C.restrictionTermIso D r hG hp hr A b c a hb hc d).hom ≫
        D.restrictionQuotientMap A c d :=
  FppfQuotientComparison.isoOfCompatibleTerms_fac _ _ _ _ _ _ _

/-- Any direct-model comparison compatible with ambient identity preserves
the original term comparison. -/
theorem restrictionPresentation_term_square
    (X : C.RestrictionPresentation A b a hb) (Y : D.RestrictionPresentation A c a hc)
    (d : ℕ) (e : X.model.termGroup d ≅ Y.model.termGroup d)
    (he : e.hom ≫ Y.model.termInclusion d = X.model.termInclusion d) :
    (X.termIso d).hom ≫ e.hom =
      (C.restrictionTermIso D r hG hp hr A b c a hb hc d).hom ≫ (Y.termIso d).hom := by
  let : Fintype Y.model.coordinateType := Y.model.coordinateFintype
  let : Fintype Y.model.rootType := Y.model.rootFintype
  have hm : Mono (Y.model.termInclusion d).hom.hom := by
    change Mono ((Y.model.chart.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (Y.model.chart.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  have hrep : (SubgroupFunctor.range (Y.model.termInclusion d)).IsRepresentedBy
      (Y.model.termInclusion d) := ⟨hm, rfl⟩
  apply hrep.hom_ext
  rw [Category.assoc, he, X.term_fac, Category.assoc, Y.term_fac,
    C.restrictionTermIso_hom_comp D r hG hp hr A b c a hb hc d]

/-- Full fppf quotient uniqueness preserves the actual original-to-model square. -/
theorem restrictionPresentation_quotient_square
    (X : C.RestrictionPresentation A b a hb) (Y : D.RestrictionPresentation A c a hc)
    (d : ℕ) (e : X.model.termGroup d ≅ Y.model.termGroup d)
    (E : VectorGroup.groupScheme A (X.model.layerRank d) ≅
      VectorGroup.groupScheme A (Y.model.layerRank d))
    (he : e.hom ≫ Y.model.termInclusion d = X.model.termInclusion d)
    (hE : X.model.layerProjection d ≫ E.hom = e.hom ≫ Y.model.layerProjection d) :
    (X.quotientIso d).hom ≫ E.hom =
      (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom ≫
        (Y.quotientIso d).hom := by
  apply FppfQuotientComparison.hom_ext (C.isFppfQuotient_restrictionQuotientMap A b d)
  rw [← Category.assoc, X.quotient_fac, Category.assoc, hE, ← Category.assoc,
    C.restrictionPresentation_term_square D r hG hp hr A b c a hb hc X Y d e he,
    Category.assoc, ← Y.quotient_fac]
  rw [← Category.assoc (C.restrictionQuotientMap A b d),
    C.restrictionQuotientIso_fac D r hG hp hr A b c a hb hc d]
  simp only [Category.assoc]

set_option maxHeartbeats 2000000 in
/-- The ORIGINAL quotient comparison on any common affine restriction preserves
every natural scalar power. The coefficient ring may be zero. -/
theorem restrictionQuotientIso_isEquivariant_power (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.chart.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.chart.weights.exactSupport d)) N)
      (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let : Subsingleton A := hA
    let : IsEmpty (Spec A) := inferInstanceAs (IsEmpty (PrimeSpectrum A))
    intro T s x
    let : IsEmpty T.left := Function.isEmpty T.hom
    apply Over.OverMorphism.ext
    exact (isInitialOfIsEmpty (X := T.left)).hom_ext _ _
  | inr hA =>
    let : Nontrivial A := hA
    obtain ⟨X⟩ := C.nonempty_restrictionPresentation hG A b a hb
    obtain ⟨Y⟩ := D.nonempty_restrictionPresentation hG A c a hc
    let M := X.model
    let L := Y.model
    let : Fintype M.coordinateType := M.coordinateFintype
    let : Fintype M.rootType := M.rootFintype
    let : Fintype L.coordinateType := L.coordinateFintype
    let : Fintype L.rootType := L.rootFintype
    have hU := unipotent_eq_of_same_suppliedRadical
      (AffineRegularBorel.cocharacter M.torus M.weight)
      (AffineRegularBorel.cocharacter L.torus L.weight)
      ((baseChange a).map r) (hG.baseChange a) M.represents L.represents
      (hr.baseChange_parabolic hp hG a)
    have hPar := M.represents.2.symm.trans L.represents.2
    let e := M.chart.sameParabolicTermIso L.chart (hG.baseChange a) M.maximal L.maximal
      M.fibrewise L.fibrewise M.parametrized L.parametrized hU hPar d
    let E : VectorGroup.groupScheme A (M.layerRank d) ≅
        VectorGroup.groupScheme A (L.layerRank d) := M.chart.sameParabolicQuotientIso L.chart (hG.baseChange a) M.maximal L.maximal
      M.fibrewise L.fibrewise M.parametrized L.parametrized hU hPar d
    have he : e.hom ≫ L.termInclusion d = M.termInclusion d :=
      M.chart.sameParabolicTermIso_hom_comp L.chart (hG.baseChange a) M.maximal L.maximal
        M.fibrewise L.fibrewise M.parametrized L.parametrized hU hPar d
    have hE : M.layerProjection d ≫ E.hom = e.hom ≫ L.layerProjection d :=
      M.chart.quotientMap_comp_sameParabolicQuotientIso L.chart
        (hG.baseChange a) M.maximal L.maximal M.fibrewise L.fibrewise
        M.parametrized L.parametrized hU hPar d
    have hscalar : (VectorGroup.powerWeightAction (M.layerRank d) N).IsEquivariant
        (VectorGroup.powerWeightAction (L.layerRank d) N) E.hom := by
      intro T s x
      exact M.chart.sameParabolicQuotientIso_isEquivariant_power L.chart
        (hG.baseChange a) M.maximal L.maximal M.fibrewise L.fibrewise
        M.parametrized L.parametrized hU hPar d N s x
    intro T s x
    exact AutomorphicAction.isEquivariant_of_iso_square
      (VectorGroup.powerWeightAction (R := A) (Nat.card (C.chart.weights.exactSupport d)) N)
      (VectorGroup.powerWeightAction (R := A) (Nat.card (D.chart.weights.exactSupport d)) N)
      (VectorGroup.powerWeightAction (R := A) (X.model.layerRank d) N)
      (VectorGroup.powerWeightAction (R := A) (Y.model.layerRank d) N)
      (X.quotientIso d) (Y.quotientIso d)
      (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom E.hom
      (X.scalar d N) (Y.scalar d N) hscalar
      (C.restrictionPresentation_quotient_square D r hG hp hr A b c a hb hc
        X Y d e E he hE) s x

/-- The induced ORIGINAL overlap map has scalar weight one on all coefficient algebras. -/
theorem restrictionQuotientIso_hasScalarWeight (d : ℕ) :
    VectorGroup.HasScalarWeight (VectorGroup.pointTransformation
      (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom) 1 :=
  VectorGroup.hasScalarWeight_of_equivariant _ 1
    (C.restrictionQuotientIso_isEquivariant_power D r hG hp hr A b c a hb hc d 1)

/-- The actual original overlap is a linear equivalence over every coefficient algebra. -/
def restrictionLayerLinearEquiv (d : ℕ) (B : CommAlgCat.{u} A) :
    (Fin (Nat.card (C.chart.weights.exactSupport d)) → B) ≃ₗ[B]
      (Fin (Nat.card (D.chart.weights.exactSupport d)) → B) :=
  VectorGroup.linearEquivOfWeight (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d)
    (by decide : 0 < 1)
    (C.restrictionQuotientIso_hasScalarWeight D r hG hp hr A b c a hb hc d) B

/-- One base-ring matrix represents the ORIGINAL comparison. -/
theorem restrictionQuotientIso_eq_matrixHom (d : ℕ) :
    (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom =
      VectorGroup.matrixHom (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom)) :=
  VectorGroup.eq_matrixHom_of_hasScalarWeight _ (by decide : 0 < 1)
    (C.restrictionQuotientIso_hasScalarWeight D r hG hp hr A b c a hb hc d)

/-- The same base-ring matrix gives the ORIGINAL comparison on every scheme test. -/
theorem coordinates_restrictionQuotientIso (d : ℕ) (T : Over (Spec A))
    (x : T ⟶ (VectorGroup.groupScheme A (Nat.card (C.chart.weights.exactSupport d))).X) :
    (VectorGroup.coordinates A (Nat.card (D.chart.weights.exactSupport d)) T
      (x ≫ (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom.hom.hom)).toAdd =
      (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom)).map (scalarMap T) *ᵥ
      (VectorGroup.coordinates A (Nat.card (C.chart.weights.exactSupport d)) T x).toAdd :=
  VectorGroup.coordinates_of_hasScalarWeight _ (by decide : 0 < 1)
    (C.restrictionQuotientIso_hasScalarWeight D r hG hp hr A b c a hb hc d) T x

/-- Uniqueness identifies any map with the same ORIGINAL quotient square. -/
theorem restrictionQuotientIso_unique (d : ℕ)
    (φ : VectorGroup.groupScheme A (Nat.card (C.chart.weights.exactSupport d)) ⟶
      VectorGroup.groupScheme A (Nat.card (D.chart.weights.exactSupport d)))
    (hφ : C.restrictionQuotientMap A b d ≫ φ =
      (C.restrictionTermIso D r hG hp hr A b c a hb hc d).hom ≫
        D.restrictionQuotientMap A c d) :
    φ = (C.restrictionQuotientIso D r hG hp hr A b c a hb hc d).hom := by
  apply FppfQuotientComparison.hom_ext (C.isFppfQuotient_restrictionQuotientMap A b d)
  exact hφ.trans (C.restrictionQuotientIso_fac D r hG hp hr A b c a hb hc d).symm

end AffineParabolicFaceChart
end Langlands.GroupScheme.RelativeLevi
