import Langlands.AlgebraicGeometry.LangWeil.UniformLangWeilOfFamilyProof
import Langlands.GroupScheme.HomScheme.FibreComparison
import Langlands.GroupScheme.IdentityJetConjugationAction
import Langlands.GroupScheme.IdentityJetHomDetection
import Langlands.GroupScheme.SchemeActionDominantOrbit
import Langlands.GroupScheme.Torus.MultiplicativeTypeFibrewiseCentralityReduction

/-! # Detection of the centre by a finite identity jet -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

open HomScheme

variable {S : Scheme.{u}}

/-- An order detects the centre if its jet action kernel is the full centre
as a subgroup functor on relative schemes. -/
def DetectsCenter (G : GroupScheme S) [IsSeparated G.X.hom] (n : ℕ) : Prop :=
  (conjugationAction G n).kernel = center G

/-- The centre acts trivially on every identity jet. -/
theorem center_le_conjugationKernel (G : GroupScheme S) [IsSeparated G.X.hom] (n : ℕ) :
    center G ≤ (conjugationAction G n).kernel := by
  intro T g hg V b x
  rw [conjugationAction_act, ← cancel_mono (overInclusion G n), conjugatePoint_inclusion,
    (mem_center.mp hg V b (x ≫ overInclusion G n)).eq, mul_assoc, mul_inv_cancel,
    mul_one]

private theorem inclusion_comp_conjugationFamily_eq_of_mem_kernel
    {G : GroupScheme S} [IsSeparated G.X.hom] {T : Over S} {n : ℕ}
    (g : T ⟶ G.X) (hg : g ∈ (conjugationAction G n).kernel.carrier T) :
    inclusion ((baseChange T.hom).obj G) n ≫ (conjugationFamily (𝟙 G) g).hom.hom.left =
      inclusion ((baseChange T.hom).obj G) n ≫ ((baseChange T.hom).map (𝟙 G)).hom.hom.left := by
  let K := (baseChange T.hom).obj G
  let V := (schemeFunctor T.left n).obj K
  let y : V ⟶ K.X := overInclusion K n
  let b : (Over.map T.hom).obj V ⟶ T := Over.homMk V.hom rfl
  let x : (Over.map T.hom).obj V ⟶ (schemeFunctor S n).obj G := Over.homMk
    (separatedBaseChangeMap G T.hom n) (separatedBaseChange_isPullback G T.hom n).w
  have hx : baseChangePointsEquiv T.hom G V y = x ≫ overInclusion G n := by
    apply Over.OverMorphism.ext
    rw [baseChangePointsEquiv_left]
    exact (separatedBaseChangeMap_inclusion G T.hom n).symm
  let g' := RelativeLevi.pulledBackPoint G T g
  have hpoint : baseChangePointsEquiv T.hom G V (K.constantPoint g' V) = b ≫ g := by
    rw [GroupScheme.constantPoint, baseChangePointsEquiv_naturality]
    change _ ≫ baseChangeBasePointsEquiv T.hom G g' = b ≫ g
    rw [RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint]
    rfl
  have hfix := hg ((Over.map T.hom).obj V) b x
  change (conjugationAction G n).act (b ≫ g) x = x at hfix
  rw [conjugationAction_act, ← cancel_mono (overInclusion G n), conjugatePoint_inclusion,
    ← hx] at hfix
  have he : y ≫ (K.innerIso g').hom.hom.hom = y := by
    apply (baseChangePointsEquiv T.hom G V).injective
    rw [comp_innerIso_hom, map_mul, map_mul, map_inv, hpoint]
    exact hfix
  have hleft := congrArg (fun f : V ⟶ K.X => f.left) he
  change inclusion K n ≫ ((baseChange T.hom).map (𝟙 G) ≫ (K.innerIso g').hom).hom.hom.left =
    inclusion K n ≫ ((baseChange T.hom).map (𝟙 G)).hom.hom.left
  have hid : (baseChange T.hom).map (𝟙 G) = 𝟙 K := (baseChange T.hom).map_id G
  rw [hid, Category.id_comp, Grp.id_hom_hom, Over.id_left, Category.comp_id]
  exact hleft

set_option maxHeartbeats 900000 in
/-- For a smooth separated quasi-compact group with geometrically connected
fibres over a quasi-compact base, one identity jet detects the full centre. -/
theorem exists_order_detects_center (G : GroupScheme S) [CompactSpace S]
    [QuasiCompact G.X.hom] [Smooth G.X.hom] [IsSeparated G.X.hom]
    [GeometricallyConnected G.X.hom] : ∃ n : ℕ, DetectsCenter G n := by
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : GeometricallyIrreducible G.X.hom :=
    Langlands.AlgebraicGeometry.LangWeil.geometricallyIrreducible_of_smooth_of_geometricallyConnected
      G.X.hom inferInstance inferInstance
  let K := (baseChange G.X.hom).obj G
  have : Smooth K.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsSeparated K.X.hom :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : GeometricallyIrreducible K.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyIrreducible) _ _ inferInstance
  let φ : RelativeHom G G G.X := conjugationFamily (𝟙 G) (𝟙 G.X)
  let ψ : RelativeHom G G G.X := (baseChange G.X.hom).map (𝟙 G)
  obtain ⟨n, hn⟩ := exists_order_detects_baseChange_hom_eq φ ψ
  have hconj {T : Over S} (g : T ⟶ G.X)
      (hg : g ∈ (conjugationAction G n).kernel.carrier T) :
      conjugationFamily (𝟙 G) g = (baseChange T.hom).map (𝟙 G) := by
    let K' := (baseChange g.left).obj K
    let G' := (baseChange T.hom).obj G
    let e := Descent.pullbackComparison G.X.hom g.left T.hom (Over.w g) G
    let eLeft : K'.X.left ⟶ G'.X.left := e.hom.hom.hom.left
    have he (f : RelativeHom G G G.X) :
        ((baseChange g.left).map f).hom.hom.left ≫ eLeft =
          eLeft ≫ (evaluate g f).hom.hom.left :=
      congrArg (fun a : K' ⟶ G' => a.hom.hom.left) (evaluate_comparison g f)
    have htransport (f : RelativeHom G G G.X) :
        (inclusion K' n ≫ ((baseChange g.left).map f).hom.hom.left) ≫ eLeft =
          map e.hom n ≫ inclusion G' n ≫ (evaluate g f).hom.hom.left := by
      rw [Category.assoc, he, ← Category.assoc, ← map_inclusion, Category.assoc]
    have hraw : (baseChange g.left).map φ = (baseChange g.left).map ψ := by
      apply hn T.left g.left
      apply (cancel_mono eLeft).mp
      rw [htransport, htransport]
      simp only [φ, ψ, evaluate_conjugationFamily, Category.comp_id, evaluate_baseChange]
      exact congrArg (map e.hom n ≫ ·) (inclusion_comp_conjugationFamily_eq_of_mem_kernel g hg)
    have h := congrArg (fun a : K' ⟶ K' => a ≫ e.hom) hraw
    rw [evaluate_comparison, evaluate_comparison, cancel_epi] at h
    simpa only [φ, ψ, evaluate_conjugationFamily, Category.comp_id, evaluate_baseChange] using h
  refine ⟨n, le_antisymm ?_ (center_le_conjugationKernel G n)⟩
  intro T g hg
  apply mem_center.mpr
  intro V b x
  have h := MultiplicativeTypeFibrewiseCentralityReduction.commute_of_conjugationFamily_eq
    (𝟙 G) x (b ≫ g) (hconj (b ≫ g) ((conjugationAction G n).kernel.comp_mem b hg))
  simpa only [Grp.id_hom_hom, Category.comp_id] using h.symm

end Langlands.GroupScheme.IdentityJet
