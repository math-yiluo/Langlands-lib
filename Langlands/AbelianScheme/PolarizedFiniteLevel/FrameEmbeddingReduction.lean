import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameNormalization
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingExistenceStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEmbeddingReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusField
import Langlands.AlgebraicGeometry.LinearSystem.LineTwistedSections
import Langlands.AlgebraicGeometry.LinearSystem.TwistComparison
import Langlands.AlgebraicGeometry.LinearSystem.BundleComparison
import Langlands.AlgebraicGeometry.RelativeFibreClosedImmersion
import Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison

/-! # Frame-normalized cubic embeddings from the field Lefschetz theorem -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Modules.DerivedSections Langlands.AlgebraicGeometry.ProjectiveBundle

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}

/-- The identification of a module on the base with its pullback along the structure map
followed by a torsion section. -/
def Datum.torsionPullbackIso (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) :
    𝟭 S.Modules ≅
      Scheme.Modules.pullback a.abelian.X.hom ⋙ Scheme.Modules.pullback (a.torsionPoint r) :=
  (Scheme.Modules.pullbackId S).symm ≪≫
    Scheme.Modules.pullbackCongr (a.torsionPoint_hom r).symm ≪≫
      (Scheme.Modules.pullbackComp (a.torsionPoint r) a.abelian.X.hom).symm

/-- The torsion evaluation written through `Datum.torsionPullbackIso`. -/
lemma Datum.torsionEvaluation_eq_torsionPullbackIso (a : Datum P S g d n)
    (r : Fin (2 * g) → ZMod n) :
    a.torsionEvaluation r = (a.torsionPullbackIso r).hom.app _ ≫
      (Scheme.Modules.pullback (a.torsionPoint r)).map a.cubicEvaluationAdjoint := by
  rfl

/-- The pullback along a torsion section of the adjoint of a module map into the cubic
direct image is that module map followed by the torsion evaluation. -/
lemma Datum.pullback_map_cubicAdjoint (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n)
    {Λ : S.Modules} (τ : Λ ⟶ a.rigidificationModule) :
    (Scheme.Modules.pullback (a.torsionPoint r)).map
        ((Scheme.Modules.pullback a.abelian.X.hom).map τ ≫ a.cubicEvaluationAdjoint) =
      (a.torsionPullbackIso r).inv.app Λ ≫ τ ≫ a.torsionEvaluation r := by
  have h := (a.torsionPullbackIso r).hom.naturality τ
  simp only [Functor.id_map, Functor.comp_map] at h
  rw [Datum.torsionEvaluation_eq_torsionPullbackIso, ← Category.assoc τ, h, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app_assoc]

/-- The line of the cubic bundle at the last entry of a frame. -/
abbrev Datum.frameLine (a : Datum P S g d n) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) :
    LineBundle S :=
  (LineBundle.pullback (a.torsionPoint (ρ (Fin.last (m + 1))))).obj a.cubicBundle

/-- The cubic bundle twisted by the dual of the last frame line. -/
abbrev Datum.frameTwist (a : Datum P S g d n) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) :
    LineBundle a.abelian.X.left :=
  LineBundle.tensor P.preservation a.cubicBundle
    ((LineBundle.pullback a.abelian.X.hom).obj (a.frameLine ρ).dual)

/-- The non-last entries of a frame, indexed by projective coordinates. -/
def frameCoordinate (m : ℕ) (i : Fin (m + 1)) : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)} :=
  ⟨i.castSucc, Fin.castSucc_ne_last i⟩

lemma frameCoordinate_injective (m : ℕ) : Function.Injective (frameCoordinate m) := by
  intro i j h
  exact Fin.castSucc_injective _ (congrArg Subtype.val h)

/-- The twisted section of the frame twist attached to a map from the last frame line to
the cubic direct image. -/
def Datum.frameSection (a : Datum P S g d n) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (τ : (a.frameLine ρ).obj ⟶ a.rigidificationModule) :
    GlobalSections (a.frameTwist ρ).obj :=
  twistedSection a.abelian.X.hom (a.frameLine ρ)
    ((Scheme.Modules.pullback a.abelian.X.hom).map τ ≫ a.cubicEvaluationAdjoint)

lemma Datum.pullbackSection_frameSection_eq_zero (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (τ : (a.frameLine ρ).obj ⟶ a.rigidificationModule)
    (r : Fin (2 * g) → ZMod n) (h : τ ≫ a.torsionEvaluation r = 0) :
    pullbackSection (a.torsionPoint r) _ (a.frameSection ρ τ) = 0 := by
  apply pullbackSection_twistedSection_eq_zero
  rw [Datum.pullback_map_cubicAdjoint, h, Limits.comp_zero]

lemma Datum.pullbackSection_frameSection_congr (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    {τ τ' : (a.frameLine ρ).obj ⟶ a.rigidificationModule} (r : Fin (2 * g) → ZMod n)
    (h : τ ≫ a.torsionEvaluation r = τ' ≫ a.torsionEvaluation r) :
    pullbackSection (a.torsionPoint r) _ (a.frameSection ρ τ) =
      pullbackSection (a.torsionPoint r) _ (a.frameSection ρ τ') := by
  apply pullbackSection_twistedSection_congr
  rw [Datum.pullback_map_cubicAdjoint, Datum.pullback_map_cubicAdjoint, h]

lemma Datum.trivializationOpen_pullbackSection_frameSection (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (τ : (a.frameLine ρ).obj ⟶ a.rigidificationModule)
    (r : Fin (2 * g) → ZMod n) (h : IsIso (τ ≫ a.torsionEvaluation r)) :
    trivializationOpen _ (pullbackSection (a.torsionPoint r) _ (a.frameSection ρ τ)) = ⊤ := by
  apply trivializationOpen_pullbackSection_twistedSection
  rw [Datum.pullback_map_cubicAdjoint]
  infer_instance


/-- Membership in the nonvanishing locus of a line-bundle section is membership in its
trivialization open. -/
lemma mem_nonvanishingLocus_iff_mem_trivializationOpen {X : Scheme.{u}} (L : LineBundle X)
    (s : GlobalSections L.obj) (x : X) :
    x ∈ nonvanishingLocus L.obj s ↔ x ∈ trivializationOpen L.obj s := by
  rw [lineBundleResidueOpenComparison X L s]
  rfl

/-- The relative linear-system map only depends on its sections. -/
lemma relativeLinearSystemMap_congr {X S' : Scheme.{u}} {L : LineBundle X} {k : ℕ}
    {s t : Fin (k + 1) → GlobalSections L.obj} (h : s = t) (p : X ⟶ S')
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (ht : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (t i)) :
    relativeLinearSystemMap p hs = relativeLinearSystemMap p ht := by
  subst h
  rfl

/-- The point of the residue fibre at `z` given by a torsion section. -/
def Datum.fibreTorsionPoint (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) (z : S) :
    Spec (S.residueField z) ⟶ a.abelian.X.hom.fiber z :=
  pullback.lift (S.fromSpecResidueField z ≫ a.torsionPoint r) (𝟙 _) (by simp)

@[reassoc (attr := simp)]
lemma Datum.fibreTorsionPoint_fiberι (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) (z : S) :
    a.fibreTorsionPoint r z ≫ a.abelian.X.hom.fiberι z =
      S.fromSpecResidueField z ≫ a.torsionPoint r :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma Datum.fibreTorsionPoint_toResidueField (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n)
    (z : S) :
    a.fibreTorsionPoint r z ≫ a.abelian.X.hom.fiberToSpecResidueField z = 𝟙 _ :=
  pullback.lift_snd _ _ _

section Fibre

variable (a : Datum P S g d n) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (τ : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)} →
      ((a.frameLine ρ).obj ⟶ a.rigidificationModule))

/-- The coordinate sections of the frame twist. -/
def Datum.frameSections (i : Fin (m + 1)) : GlobalSections (a.frameTwist ρ).obj :=
  a.frameSection ρ (τ (frameCoordinate m i))

variable {a ρ τ}

lemma Datum.torsionPoint_mem_frameSections
    (hoff : ∀ i j : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)}, i ≠ j →
      τ i ≫ a.torsionEvaluation (ρ j.val) = 0)
    (hdiag : ∀ i : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)},
      IsIso (τ i ≫ a.torsionEvaluation (ρ i.val)))
    (i j : Fin (m + 1)) (z : S) :
    a.torsionPoint (ρ j.castSucc) z ∈
        trivializationOpen (a.frameTwist ρ).obj (a.frameSections ρ τ i) ↔ i = j := by
  rw [← mem_pullback_trivializationOpen_iff]
  change z ∈ trivializationOpen ((Scheme.Modules.pullback (a.torsionPoint (ρ j.castSucc))).obj
    (a.frameTwist ρ).obj) (pullbackSection _ _ (a.frameSection ρ (τ (frameCoordinate m i)))) ↔ _
  by_cases hij : i = j
  · subst hij
    rw [a.trivializationOpen_pullbackSection_frameSection ρ (τ (frameCoordinate m i))
      (ρ i.castSucc) (hdiag _)]
    simp
  · rw [a.pullbackSection_frameSection_eq_zero ρ (τ (frameCoordinate m i)) (ρ j.castSucc)
      (hoff _ (frameCoordinate m j) (fun h => hij (frameCoordinate_injective m h))),
      show trivializationOpen ((Scheme.Modules.pullback (a.torsionPoint (ρ j.castSucc))).obj
          (a.frameTwist ρ).obj) 0 = ⊥ from
        trivializationOpen_zero ((LineBundle.pullback (a.torsionPoint (ρ j.castSucc))).obj
          (a.frameTwist ρ))]
    simp [hij]

lemma Datum.fibreTorsionPoint_mem_frameSections
    (hoff : ∀ i j : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)}, i ≠ j →
      τ i ≫ a.torsionEvaluation (ρ j.val) = 0)
    (hdiag : ∀ i : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)},
      IsIso (τ i ≫ a.torsionEvaluation (ρ i.val)))
    (i j : Fin (m + 1)) (z : S) (w : Spec (S.residueField z)) :
    a.fibreTorsionPoint (ρ j.castSucc) z w ∈
        trivializationOpen ((LineBundle.pullback (a.abelian.X.hom.fiberι z)).obj
          (a.frameTwist ρ)).obj
          (pullbackSection (a.abelian.X.hom.fiberι z) (a.frameTwist ρ).obj
            (a.frameSections ρ τ i)) ↔ i = j := by
  refine (mem_pullback_trivializationOpen_iff _ _ _).trans ?_
  rw [← Scheme.Hom.comp_apply (a.fibreTorsionPoint (ρ j.castSucc) z) (a.abelian.X.hom.fiberι z) w,
    Datum.fibreTorsionPoint_fiberι, Scheme.Hom.comp_apply]
  exact a.torsionPoint_mem_frameSections hoff hdiag i j _

end Fibre

/-- On the residue fibre at `z`, the frame twist is the cubic bundle of the residue datum,
by a choice of trivialization of the pulled back dual frame line. -/
def Datum.fibreTwistIso (a : Datum P S g d n) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (z : S) :
    (Scheme.Modules.pullback (a.abelian.X.hom.fiberι z)).obj (a.frameTwist ρ).obj ≅
      (a.pullback (S.fromSpecResidueField z)).cubicBundle.obj :=
  let l₀ := (fieldLineBundleTriviality (S.residueField z)
    ((LineBundle.pullback (S.fromSpecResidueField z)).obj (a.frameLine ρ).dual)).some
  let triv : (Scheme.Modules.pullback (a.abelian.X.hom.fiberι z)).obj
      ((Scheme.Modules.pullback a.abelian.X.hom).obj (a.frameLine ρ).dual.obj) ≅
        structureSheaf (a.abelian.X.hom.fiber z) :=
    (Scheme.Modules.pullbackComp (a.abelian.X.hom.fiberι z) a.abelian.X.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr (a.abelian.X.hom.fiber_fac z)).app _ ≪≫
      ((Scheme.Modules.pullbackComp (a.abelian.X.hom.fiberToSpecResidueField z)
        (S.fromSpecResidueField z)).app _).symm ≪≫
      (Scheme.Modules.pullback (a.abelian.X.hom.fiberToSpecResidueField z)).mapIso l₀ ≪≫
      pullbackUnitIso (a.abelian.X.hom.fiberToSpecResidueField z)
  asIso (pullbackTensorComparisonApp (a.abelian.X.hom.fiberι z) _ _) ≪≫
    (tensorFunctor _).mapIso ((Iso.refl _).prod triv) ≪≫ tensorRightUnitor _ ≪≫
    ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso (S.fromSpecResidueField z))).symm


section FibreBasis

variable (a : Datum P S g d n) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (τ : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)} →
      ((a.frameLine ρ).obj ⟶ a.rigidificationModule))

/-- The coordinate sections on the residue fibre at `z`, as global sections of the cubic
bundle of the residue datum. -/
def Datum.fibreFrameSections (z : S) (i : Fin (m + 1)) :
    (relativeGlobalSections (a.pullback (S.fromSpecResidueField z)).abelian.X.hom).obj
      (a.pullback (S.fromSpecResidueField z)).cubicBundle.obj :=
  (a.fibreTwistIso ρ z).hom.app ⊤
    (pullbackSection (a.abelian.X.hom.fiberι z) (a.frameTwist ρ).obj (a.frameSections ρ τ i))

variable {a ρ τ}
variable (hoff : ∀ i j : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)}, i ≠ j →
      τ i ≫ a.torsionEvaluation (ρ j.val) = 0)
    (hdiag : ∀ i : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)},
      IsIso (τ i ≫ a.torsionEvaluation (ρ i.val)))

include hoff hdiag in
lemma Datum.pullbackSection_fibreFrameSections_eq_zero_iff (z : S) (i j : Fin (m + 1)) :
    pullbackSection (a.fibreTorsionPoint (ρ j.castSucc) z)
        (a.pullback (S.fromSpecResidueField z)).cubicBundle.obj
        (a.fibreFrameSections ρ τ z i) = 0 ↔ i ≠ j := by
  have h := vanishesAlong_field_iff (K := S.residueField z)
    (a.pullback (S.fromSpecResidueField z)).cubicBundle (a.fibreTorsionPoint (ρ j.castSucc) z)
    (a.fibreFrameSections ρ τ z i) (IsLocalRing.closedPoint (S.residueField z))
  refine h.trans (not_congr ?_)
  change _ ∈ trivializationOpen _ ((a.fibreTwistIso ρ z).hom.app ⊤ _) ↔ _
  rw [trivializationOpen_mapIso]
  exact a.fibreTorsionPoint_mem_frameSections hoff hdiag i j z _

include hoff hdiag in
lemma Datum.linearIndependent_fibreFrameSections (z : S) :
    LinearIndependent (S.residueField z) (a.fibreFrameSections ρ τ z) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hcj
  let y := a.fibreTorsionPoint (ρ j.castSucc) z
  let F := (a.pullback (S.fromSpecResidueField z)).cubicBundle.obj
  let V := (relativeGlobalSections (a.pullback (S.fromSpecResidueField z)).abelian.X.hom).obj F
  let ι : V →+ GlobalSections F := AddMonoidHom.mk' (fun v => v) (fun _ _ => rfl)
  let E := (pullbackSectionAddHom F y).comp ι
  have hq : y.appTop.hom.comp (a.pullback (S.fromSpecResidueField z)).abelian.X.hom.appTop.hom =
      RingHom.id _ := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    change (y ≫ a.abelian.X.hom.fiberToSpecResidueField z).appTop.hom = _
    rw [Datum.fibreTorsionPoint_toResidueField, Scheme.Hom.id_appTop]
    rfl
  have hsmul : ∀ (r : S.residueField z) (v : V),
      E (r • v) = (Scheme.ΓSpecIso (S.residueField z)).inv r • E v := by
    intro r v
    change pullbackSection y F (r • v) = _
    rw [Langlands.AlgebraicGeometry.Modules.CechResolution.relativeGlobalSections_smul,
      pullbackSection_smul]
    congr 1
    change (y.appTop.hom.comp (a.pullback (S.fromSpecResidueField z)).abelian.X.hom.appTop.hom)
      ((Scheme.ΓSpecIso (S.residueField z)).inv r) = _
    rw [hq]
    rfl
  have hE : E (∑ i, c i • a.fibreFrameSections ρ τ z i) = 0 := by rw [hc, map_zero]
  rw [map_sum] at hE
  simp only [hsmul] at hE
  rw [Finset.sum_eq_single j (fun i _ hij => by
      have h0 := (a.pullbackSection_fibreFrameSections_eq_zero_iff hoff hdiag z i j).mpr hij
      change _ • pullbackSection y F (a.fibreFrameSections ρ τ z i) = 0
      rw [show pullbackSection y F (a.fibreFrameSections ρ τ z i) = 0 from h0, smul_zero])
    (by simp)] at hE
  have hu : IsUnit ((Scheme.ΓSpecIso (S.residueField z)).inv (c j)) :=
    (IsUnit.mk0 _ hcj).map _
  rw [hu.smul_eq_zero] at hE
  exact (a.pullbackSection_fibreFrameSections_eq_zero_iff hoff hdiag z j j).mp hE rfl

include hoff hdiag in
/-- On every residue fibre, the coordinate sections generate and their linear-system map is
a closed immersion, by Lefschetz's theorem over the residue field. -/
theorem Datum.frameSections_fibre (HF : CubicFieldEmbeddingStatement.{u}) [IsLocallyNoetherian S]
    (hd : 0 < d) (hM : IsLocallyFreeOfRank a.rigidificationModule (m + 1)) (z : S) :
    (∀ x : a.abelian.X.hom.fiber z, ∃ i, a.abelian.X.hom.fiberι z x ∈
      trivializationOpen (a.frameTwist ρ).obj (a.frameSections ρ τ i)) ∧
    ∀ hs : (∀ x : a.abelian.X.hom.fiber z, ∃ i, x ∈ nonvanishingLocus
        ((LineBundle.pullback (a.abelian.X.hom.fiberι z)).obj (a.frameTwist ρ)).obj
        (pullbackSection (a.abelian.X.hom.fiberι z) (a.frameTwist ρ).obj
          (a.frameSections ρ τ i))),
      IsClosedImmersion (relativeLinearSystemMap (a.abelian.X.hom.fiberToSpecResidueField z) hs) := by
  classical
  have : IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField z)) :=
    (cubicDirectImage P S g d n hd a).2 _ _
  have := hM.isLocallyFree
  have : a.rigidificationModule.IsQuasicoherent := inferInstance
  obtain ⟨U, hzU, hU⟩ := exists_affine_frameOpen hM z
  let B₀ := a.cubicFibreSectionBasis U hU z hzU
  have hM' := (cubicDirectImage P _ g d n hd (a.pullback (S.fromSpecResidueField z))).1
  have := hM'.isLocallyFree
  have : (a.pullback (S.fromSpecResidueField z)).rigidificationModule.IsQuasicoherent :=
    inferInstance
  have : Epi (a.pullback (S.fromSpecResidueField z)).cubicEvaluationAdjoint :=
    (HF P (S.residueField z) g d n hd (a.pullback (S.fromSpecResidueField z))).1
  have : FiniteDimensional (S.residueField z)
      ((relativeGlobalSections (a.pullback (S.fromSpecResidueField z)).abelian.X.hom).obj
        (a.pullback (S.fromSpecResidueField z)).cubicBundle.obj) :=
    Module.Finite.of_basis B₀
  let B := basisOfLinearIndependentOfCardEqFinrank
    (a.linearIndependent_fibreFrameSections hoff hdiag z)
    (by rw [Module.finrank_eq_card_basis B₀])
  have hBcoe : ⇑B = a.fibreFrameSections ρ τ z :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hB := (a.pullback (S.fromSpecResidueField z)).basis_generates B
  constructor
  · intro x
    obtain ⟨i, hi⟩ := hB x
    refine ⟨i, ?_⟩
    rw [hBcoe, mem_nonvanishingLocus_iff_mem_trivializationOpen] at hi
    change x ∈ trivializationOpen _ ((a.fibreTwistIso ρ z).hom.app ⊤ _) at hi
    rw [trivializationOpen_mapIso] at hi
    exact (mem_pullback_trivializationOpen_iff _ _ x).mp hi
  · intro hs
    have hci := (HF P (S.residueField z) g d n hd (a.pullback (S.fromSpecResidueField z))).2
      m B hB
    have hsec : mapIsoSections
        (L := (LineBundle.pullback (a.abelian.X.hom.fiberι z)).obj (a.frameTwist ρ))
        (M := (a.pullback (S.fromSpecResidueField z)).cubicBundle) (a.fibreTwistIso ρ z)
        (fun i => pullbackSection (a.abelian.X.hom.fiberι z) (a.frameTwist ρ).obj
          (a.frameSections ρ τ i)) = ⇑B := by
      rw [hBcoe]
      funext i
      rfl
    have hgen' := mapIsoSections_generate
      (L := (LineBundle.pullback (a.abelian.X.hom.fiberι z)).obj (a.frameTwist ρ))
      (M := (a.pullback (S.fromSpecResidueField z)).cubicBundle) (a.fibreTwistIso ρ z) hs
    have h1 := relativeLinearSystemMap_mapIso
      (L := (LineBundle.pullback (a.abelian.X.hom.fiberι z)).obj (a.frameTwist ρ))
      (M := (a.pullback (S.fromSpecResidueField z)).cubicBundle)
      (a.abelian.X.hom.fiberToSpecResidueField z) (a.fibreTwistIso ρ z) hs
    have h2 := relativeLinearSystemMap_congr hsec (a.abelian.X.hom.fiberToSpecResidueField z)
      hgen' hB
    rw [← h1, h2]
    exact hci

end FibreBasis


/-- A relative linear-system map on a proper source is a closed immersion once the
linear-system maps of the pulled back sections on all residue fibres are. -/
lemma isClosedImmersion_relativeLinearSystemMap_of_fibres {X S' : Scheme.{u}} {L : LineBundle X}
    {k : ℕ} {s : Fin (k + 1) → GlobalSections L.obj} (p : X ⟶ S') [IsProper p]
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (H : ∀ z : S', IsClosedImmersion (relativeLinearSystemMap (p.fiberToSpecResidueField z)
      (pullbackSections_generate (p.fiberι z) hs))) :
    IsClosedImmersion (relativeLinearSystemMap p hs) := by
  have : IsProper (relativeLinearSystemMap p hs ≫ RelativeProjectiveSpace.toBase S' k) := by
    rw [relativeLinearSystemMap_toBase]
    infer_instance
  have : IsProper (relativeLinearSystemMap p hs) :=
    .of_comp _ (RelativeProjectiveSpace.toBase S' k)
  rw [isClosedImmersion_iff_relativeFibre_of_isProper _ (RelativeProjectiveSpace.toBase S' k)]
  intro z
  have hsq := relativeLinearSystemMap_pullback p (p.fiberToSpecResidueField z) (p.fiberι z)
    (S'.fromSpecResidueField z) (p.fiber_fac z) hs
  have hP := RelativeProjectiveSpace.isPullback_map k (S'.fromSpecResidueField z)
  let iP := (IsPullback.of_hasPullback (RelativeProjectiveSpace.toBase S' k)
    (S'.fromSpecResidueField z)).isoIsPullback _ _ hP.flip
  let iX : (relativeLinearSystemMap p hs ≫ RelativeProjectiveSpace.toBase S' k).fiber z ≅
      p.fiber z :=
    pullback.congrHom (relativeLinearSystemMap_toBase p hs) rfl
  have key : relativeFibreMap (relativeLinearSystemMap p hs)
      (RelativeProjectiveSpace.toBase S' k) z ≫ iP.hom =
      iX.hom ≫ relativeLinearSystemMap (p.fiberToSpecResidueField z)
        (pullbackSections_generate (p.fiberι z) hs) := by
    apply hP.flip.hom_ext
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst, Category.assoc, hsq]
      have e1 := baseFibreMap_fiberι (relativeLinearSystemMap p hs)
        (RelativeProjectiveSpace.toBase S' k) z
      have e2 : iX.hom ≫ p.fiberι z =
          (relativeLinearSystemMap p hs ≫ RelativeProjectiveSpace.toBase S' k).fiberι z := by
        simp [iX, Scheme.Hom.fiberι]
      exact e1.trans (by rw [← e2, Category.assoc])
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd, Category.assoc,
        relativeLinearSystemMap_toBase (p.fiberToSpecResidueField z)
          (pullbackSections_generate (p.fiberι z) hs)]
      have e1 := relativeFibreMap_toResidueField (relativeLinearSystemMap p hs)
        (RelativeProjectiveSpace.toBase S' k) z
      have e2 : iX.hom ≫ p.fiberToSpecResidueField z =
          (relativeLinearSystemMap p hs ≫
            RelativeProjectiveSpace.toBase S' k).fiberToSpecResidueField z := by
        simp [iX, Scheme.Hom.fiberToSpecResidueField]
      exact e1.trans e2.symm
  have he : relativeFibreMap (relativeLinearSystemMap p hs)
      (RelativeProjectiveSpace.toBase S' k) z =
      iX.hom ≫ relativeLinearSystemMap (p.fiberToSpecResidueField z)
        (pullbackSections_generate (p.fiberι z) hs) ≫ iP.inv := by
    rw [← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [he]
  have := H z
  infer_instance

/-- Pulling back a coordinate section of `𝒪(1)` along a linear-system map composed with
`f` gives, up to the canonical isomorphisms, the pullback along `f` of the section. -/
lemma pullbackSection_relativeLinearSystemMap_coordinate {X S' T : Scheme.{u}}
    {L : LineBundle X} {k : ℕ} (s : Fin (k + 1) → GlobalSections L.obj) (p : X ⟶ S')
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) (f : T ⟶ X) (i : Fin (k + 1)) :
    pullbackSection (f ≫ relativeLinearSystemMap p hs)
        (RelativeProjectiveSpace.twistOne S' k).obj
        (RelativeProjectiveSpace.twistOneCoordinate S' k i) =
      ((Scheme.Modules.pullbackComp f (relativeLinearSystemMap p hs)).hom.app _).app ⊤
        (((Scheme.Modules.pullback f).map (relativeLinearSystemTwistIso s p hs).inv).app ⊤
          (pullbackSection f L.obj (s i))) := by
  have key : pullbackSection (relativeLinearSystemMap p hs)
      (RelativeProjectiveSpace.twistOne S' k).obj
      (RelativeProjectiveSpace.twistOneCoordinate S' k i) =
        (relativeLinearSystemTwistIso s p hs).inv.app ⊤ (s i) := by
    rw [← relativeLinearSystemTwistIso_coordinate s p hs i, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  rw [← pullbackSection_comp, key, pullbackSection_naturality]

set_option linter.defProp false in
/-- Proved definition: **frame-normalized cubic embeddings from Lefschetz's theorem.** Over
a locally noetherian base, the field Lefschetz statement for the canonical cubic bundle
gives, for every datum with `0 < d` and every frame whose projective frame locus is the
whole base, a frame-normalized cubic embedding. -/
def frameEmbeddingExistence_of_cubicFieldEmbedding (HF : CubicFieldEmbeddingStatement.{u}) :
    FrameEmbeddingExistenceStatement.{u} := by
  intro P S _ g d n hd a ρ hρ
  obtain ⟨e, hoff, hlast, hdiag⟩ := a.exists_normalizedFrame ρ hρ
  let τ : {j : Fin (cubicProjectiveDimension g d + 2) //
      j ≠ Fin.last (cubicProjectiveDimension g d + 1)} →
        ((a.frameLine ρ).obj ⟶ a.rigidificationModule) :=
    fun i => Pi.ι (fun _ : {j : Fin (cubicProjectiveDimension g d + 2) //
      j ≠ Fin.last (cubicProjectiveDimension g d + 1)} =>
        (Scheme.Modules.pullback (a.torsionPoint
          (ρ (Fin.last (cubicProjectiveDimension g d + 1))))).obj a.cubicBundle.obj) i ≫ e.hom
  have hoff' : ∀ i j, i ≠ j → τ i ≫ a.torsionEvaluation (ρ j.val) = 0 := fun i j h => by
    simpa only [τ, Category.assoc] using hoff i j h
  have hdiag' : ∀ i, IsIso (τ i ≫ a.torsionEvaluation (ρ i.val)) := fun i => by
    simpa only [τ, Category.assoc] using hdiag i
  have hlast' : ∀ i, τ i ≫ a.torsionEvaluation (ρ (Fin.last _)) = 𝟙 _ := fun i => by
    simp only [τ, Category.assoc]
    exact hlast i
  have hM := a.cubicProjectiveRank hd (cubicDirectImage P S g d n hd a).1
  have hgen : ∀ x : a.abelian.X.left, ∃ i,
      x ∈ nonvanishingLocus (a.frameTwist ρ).obj (a.frameSections ρ τ i) := by
    intro x
    obtain ⟨i, hi⟩ := (a.frameSections_fibre hoff' hdiag' HF hd hM (a.abelian.X.hom x)).1
      (a.abelian.X.hom.asFiber x)
    refine ⟨i, ?_⟩
    rw [mem_nonvanishingLocus_iff_mem_trivializationOpen]
    rwa [Scheme.Hom.fiberι_asFiber] at hi
  refine ⟨relativeLinearSystemMap a.abelian.X.hom hgen,
    relativeLinearSystemMap_toBase _ _, ?_, ?_, ?_, ?_⟩
  · exact isClosedImmersion_relativeLinearSystemMap_of_fibres a.abelian.X.hom hgen
      fun z => (a.frameSections_fibre hoff' hdiag' HF hd hM z).2 _
  · exact ⟨(a.frameLine ρ).dual,
      ⟨ObjectProperty.isoMk _ (relativeLinearSystemTwistIso _ a.abelian.X.hom hgen)⟩⟩
  · intro j k hkj
    change pullbackSection _ _ _ = 0
    rw [pullbackSection_relativeLinearSystemMap_coordinate,
      show pullbackSection (a.torsionPoint (ρ j.castSucc)) (a.frameTwist ρ).obj
          (a.frameSections ρ τ k) = 0 from
        a.pullbackSection_frameSection_eq_zero ρ _ _
          (hoff' _ (frameCoordinate _ j) (fun h => hkj (frameCoordinate_injective _ h))),
      map_zero, map_zero]
  · intro i k
    rw [pullbackSection_relativeLinearSystemMap_coordinate,
      pullbackSection_relativeLinearSystemMap_coordinate,
      show pullbackSection (a.torsionPoint (ρ (Fin.last _))) (a.frameTwist ρ).obj
          (a.frameSections ρ τ i) =
        pullbackSection (a.torsionPoint (ρ (Fin.last _))) (a.frameTwist ρ).obj
          (a.frameSections ρ τ k) from
        a.pullbackSection_frameSection_congr ρ _ ((hlast' _).trans (hlast' _).symm)]

end Langlands.AbelianScheme.PolarizedFiniteLevel
