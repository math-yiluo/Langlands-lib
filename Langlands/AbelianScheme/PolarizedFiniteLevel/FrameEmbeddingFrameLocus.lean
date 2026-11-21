import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusField
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingBaseChange
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof

/-! # A normalized cubic embedding has the whole base as frame locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections Langlands.SchemeModule
open Langlands.Scheme.Modules

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem normalizedEvaluations_bijective {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] {m : ℕ}
    (W : Fin (m + 2) → ModuleCat.{u} K) (e : ∀ i, V →ₗ[K] W i)
    (s : Fin (m + 1) → V) (hV : Module.finrank K V = m + 1)
    (hW : ∀ i, Module.finrank K (W i) = 1)
    (hzero : ∀ i j : Fin (m + 1), j ≠ i → e i.castSucc (s j) = 0)
    (hdiag : ∀ i : Fin (m + 1), e i.castSucc (s i) ≠ 0)
    (hlast : ∀ j, e (Fin.last (m + 1)) (s j) ≠ 0) (k : Fin (m + 2)) :
    Function.Bijective (fun (v : V) (i : {i : Fin (m + 2) // i ≠ k}) => e i.1 v) := by
  classical
  let : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  let (i : Fin (m + 2)) : FiniteDimensional K (W i) :=
    Module.finite_of_finrank_eq_succ (hW i)
  let F := Fintype.linearCombination K s
  have hsum (i : Fin (m + 2)) (c : Fin (m + 1) → K) :
      e i (F c) = ∑ j, c j • e i (s j) := by
    simp only [F, Fintype.linearCombination_apply, map_sum, map_smul]
  have hval (i : Fin (m + 1)) (c : Fin (m + 1) → K) :
      e i.castSucc (F c) = c i • e i.castSucc (s i) := by
    rw [hsum, Finset.sum_eq_single i]
    · intro j _ hj
      rw [hzero i j hj, smul_zero]
    · simp
  have hcoeff (c : Fin (m + 1) → K) (i : Fin (m + 1))
      (h : e i.castSucc (F c) = 0) : c i = 0 := by
    rw [hval, smul_eq_zero] at h
    exact h.resolve_right (hdiag i)
  have hF : Function.Injective F := by
    apply (injective_iff_map_eq_zero F).mpr
    intro c hc
    funext i
    apply hcoeff c i
    rw [hc, map_zero]
  have hFr : Module.finrank K (Fin (m + 1) → K) = Module.finrank K V := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hV]
  have hFs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hFr).mp hF
  let E : V →ₗ[K] (∀ j : {j : Fin (m + 2) // j ≠ k}, W j.1) :=
    LinearMap.pi fun j => e j.1
  have hEinj : Function.Injective E := by
    apply (injective_iff_map_eq_zero E).mpr
    intro v hv
    obtain ⟨c, rfl⟩ := hFs v
    have hentry (i : Fin (m + 2)) (hi : i ≠ k) : e i (F c) = 0 := congrFun hv ⟨i, hi⟩
    suffices h : c = 0 by rw [h, map_zero]
    funext i
    by_cases hi : i.castSucc = k
    · have hlast' : Fin.last (m + 1) ≠ k := by
        rw [← hi]
        exact (Fin.castSucc_ne_last i).symm
      have h := hentry _ hlast'
      rw [hsum, Finset.sum_eq_single i] at h
      · exact (smul_eq_zero.mp h).resolve_right (hlast i)
      · intro j _ hj
        have hj' : j.castSucc ≠ k := by
          rw [← hi]
          exact fun h => hj (Fin.castSucc_injective _ h)
        rw [hcoeff c j (hentry _ hj'), zero_smul]
      · simp
    · exact hcoeff c i (hentry _ hi)
  have hEr : Module.finrank K V =
      Module.finrank K (∀ j : {j : Fin (m + 2) // j ≠ k}, W j.1) := by
    rw [hV, Module.finrank_pi_fintype]
    simp [hW, Fintype.card_subtype_compl]
  exact ⟨hEinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hEr).mp hEinj⟩

/-- Over a field, choose a trivialization of the base twist to identify the pullback of
`𝒪(1)` with the cubic bundle. -/
def Datum.IsFrameEmbedding.twistIsoCubicOverField {K : Type u} [Field K]
    {P : Prerequisites.{u}} {g d n m : ℕ} {a : Datum P (Spec (CommRingCat.of K)) g d n}
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K)) m}
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n} (h : a.IsFrameEmbedding ρ ψ) :
    (Scheme.Modules.pullback ψ).obj (RelativeProjectiveSpace.twistOne _ m).obj ≅
      a.cubicBundle.obj :=
  let N := h.cubic.choose
  let i := h.cubic.choose_spec.some
  let j := (fieldLineBundleTriviality K N).some
  (LineBundle.forget _).mapIso i ≪≫
    (tensorFunctor _).mapIso ((Iso.refl a.cubicBundle.obj).prod
      ((Scheme.Modules.pullback a.abelian.X.hom).mapIso j ≪≫ pullbackUnitIso _)) ≪≫
    tensorRightUnitor _

private theorem isIso_frameEvaluation_over_field {K : Type u} [Field K] [IsAlgClosed K]
    {P : Prerequisites.{u}} {g d n : ℕ} (hd : 0 < d)
    {a : Datum P (Spec (CommRingCat.of K)) g d n}
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K))
      (cubicProjectiveDimension g d)}
    {ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n}
    (h : a.IsFrameEmbedding ρ ψ) (k : Fin (cubicProjectiveDimension g d + 2)) :
    IsIso (a.frameEvaluation ρ k) := by
  let S := Spec (CommRingCat.of K)
  let m := cubicProjectiveDimension g d
  let L := RelativeProjectiveSpace.twistOne S m
  let x := RelativeProjectiveSpace.twistOneCoordinate S m
  let p (i : Fin (m + 2)) := a.torsionPoint (ρ i)
  let c := h.twistIsoCubicOverField
  let V := (relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj
  let W (i : Fin (m + 2)) : ModuleCat.{u} K :=
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (p i)).obj a.cubicBundle.obj)
  let e (i : Fin (m + 2)) : V →ₗ[K] W i :=
    (moduleSpecΓFunctor.map (a.torsionEvaluation (ρ i))).hom
  let s : Fin (m + 1) → V := fun j => c.hom.app ⊤ (pullbackSection ψ L.obj (x j))
  have hval (i : Fin (m + 2)) (j : Fin (m + 1)) :
      e i (s j) = 0 ↔ VanishesAlong L (p i ≫ ψ) (x j) := by
    change (a.torsionEvaluation (ρ i)).app ⊤
      (c.hom.app ⊤ (pullbackSection ψ L.obj (x j))) = 0 ↔ _
    rw [a.torsionEvaluation_app_top]
    exact (pullbackSection_mapIso_eq_zero_iff (p i) c _).trans
      (vanishesAlong_pullback_iff (p i) ψ L (x j))
  have hnz (i : Fin (m + 2)) : ∃ j, e i (s j) ≠ 0 := by
    have hx : (p i ≫ ψ) (IsLocalRing.closedPoint K) ∈
        ⨆ j, RelativeProjectiveSpace.coordinateOpen S m j := by
      rw [RelativeProjectiveSpace.iSup_coordinateOpen]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨j, fun hz => ?_⟩
    have hv := (LinearSystem.vanishesAlong_iff_not_mem (L := L) (p i ≫ ψ) (x j)).mp
      ((hval i j).mp hz)
    exact hv (by rwa [RelativeProjectiveSpace.trivializationOpen_twistOneCoordinate])
  have hzero (i j : Fin (m + 1)) (hij : j ≠ i) : e i.castSucc (s j) = 0 :=
    (hval i.castSucc j).mpr (h.basis i j hij)
  have hdiag (i : Fin (m + 1)) : e i.castSucc (s i) ≠ 0 := by
    obtain ⟨j, hj⟩ := hnz i.castSucc
    have hji : j = i := by
      by_contra hne
      exact hj (hzero i j hne)
    simpa only [hji] using hj
  have hlast (j : Fin (m + 1)) : e (Fin.last (m + 1)) (s j) ≠ 0 := by
    obtain ⟨i, hi⟩ := hnz (Fin.last (m + 1))
    let y := p (Fin.last (m + 1))
    have hji : e (Fin.last (m + 1)) (s j) = e (Fin.last (m + 1)) (s i) := by
      change (a.torsionEvaluation (ρ (Fin.last (m + 1)))).app ⊤ (s j) =
        (a.torsionEvaluation (ρ (Fin.last (m + 1)))).app ⊤ (s i)
      simp only [a.torsionEvaluation_app_top, s, pullbackSection_naturality]
      exact congrArg (((Scheme.Modules.pullback y).map c.hom).app ⊤)
        ((pullbackSection_pullback_eq_iff ψ y (x j) (x i)).mpr (h.unit j i))
    rw [hji]
    exact hi
  have := Langlands.AlgebraicGeometry.Modules.isFinitePresentation_of_hasFiniteLocalBasis _
    (hasFiniteLocalBasis_of_isLocallyFreeOfRank (cubicDirectImage P S g d n hd a).1)
  apply a.isIso_frameEvaluation_of_bijective ρ k
  exact normalizedEvaluations_bijective W e s (a.finrank_cubicSections hd)
    (fun i => finrank_moduleSpecΓ_lineBundle ((LineBundle.pullback (p i)).obj a.cubicBundle))
    hzero hdiag hlast k

/-- The coordinate equations of a normalized cubic embedding give a projective frame
on the entire locally noetherian base. -/
theorem Datum.IsFrameEmbedding.frameLocus_eq_top {P : Prerequisites.{u}} {S : Scheme.{u}}
    [IsLocallyNoetherian S] {g d n : ℕ} (hd : 0 < d) {a : Datum P S g d n}
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S (cubicProjectiveDimension g d)}
    {ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n}
    (h : a.IsFrameEmbedding ρ ψ) : a.frameLocus ρ = ⊤ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  let K := AlgebraicClosure (S.residueField x)
  let f : Spec (CommRingCat.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) K)) ≫ S.fromSpecResidueField x
  have hf : f (IsLocalRing.closedPoint K) = x := Scheme.fromSpecResidueField_apply x _
  have htop := (a.pullback f).frameLocus_eq_top_of_isIso ρ
    (fun k => isIso_frameEvaluation_over_field hd (h.pullback (f := f)) k)
  have hmem : IsLocalRing.closedPoint K ∈ (a.pullback f).frameLocus ρ := by
    rw [htop]
    trivial
  have hx := (a.mem_frameLocus_pullback_iff hd f ρ (IsLocalRing.closedPoint K)).mp hmem
  exact hf ▸ hx

end Langlands.AbelianScheme.PolarizedFiniteLevel
