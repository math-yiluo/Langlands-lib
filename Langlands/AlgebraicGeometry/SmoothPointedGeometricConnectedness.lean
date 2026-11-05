import Langlands.AlgebraicGeometry.SmoothDomainStalksProof
import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralProof
import Langlands.AlgebraicGeometry.GeometricallyConnectedDescent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric connectedness of smooth connected pointed schemes over fields -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- An open and closed map to a connected space with a nonempty singleton fibre
has connected source. -/
theorem connectedSpace_of_open_closed_singleton_fiber
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    [ConnectedSpace B] (p : A → B) (ho : IsOpenMap p) (hc : IsClosedMap p)
    (a₀ : A) (h : ∀ a, p a = p a₀ → a = a₀) : ConnectedSpace A := by
  classical
  refine connectedSpace_iff_clopen.mpr ⟨⟨a₀⟩, fun U hU => ?_⟩
  by_cases he : U = ∅
  · exact Or.inl he
  by_cases hu : U = Set.univ
  · exact Or.inr hu
  have hUi : IsClopen (p '' U) := ⟨hc _ hU.1, ho _ hU.2⟩
  have hVi : IsClopen (p '' Uᶜ) := ⟨hc _ hU.compl.1, ho _ hU.compl.2⟩
  have hUr : p '' U = Set.univ :=
    hUi.eq_univ ((Set.nonempty_iff_ne_empty.mpr he).image p)
  have hVr : p '' Uᶜ = Set.univ :=
    hVi.eq_univ ((Set.nonempty_compl.mpr hu).image p)
  obtain ⟨a, ha, hpa⟩ := hUr.ge (Set.mem_univ (p a₀))
  obtain ⟨b, hb, hpb⟩ := hVr.ge (Set.mem_univ (p a₀))
  have hmem : a₀ ∈ U := h a hpa ▸ ha
  have hnmem : a₀ ∉ U := h b hpb ▸ hb
  exact False.elim (hnmem hmem)

/-- Pulling the base-change projection back along a section recovers the new base. -/
def sectionFiberIso {X S T : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ X) (he : e ≫ f = 𝟙 _) (t : T ⟶ S) :
    pullback e (pullback.fst f t) ≅ T :=
  pullbackRightPullbackFstIso f t e ≪≫ pullback.congrHom he rfl ≪≫
    asIso (pullback.snd (𝟙 S) t)

private theorem subsingleton_pullback_section
    {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ f = 𝟙 _)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    Subsingleton ↥(pullback e (pullback.fst f t)) :=
  (sectionFiberIso f e he t).hom.homeomorph.toEquiv.subsingleton

/-- A smooth connected scheme over a field with a rational section is
geometrically connected, without quasi-compactness or affineness assumptions. -/
theorem geometricallyConnected_of_smooth_connected_section
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [ConnectedSpace X]
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  let K := AlgebraicClosure k
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Surjective t := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have : IsIntegralHom t :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  let e' : Spec (CommRingCat.of K) ⟶ pullback f t :=
    pullback.lift (t ≫ e) (𝟙 _)
      (by simp only [Category.assoc, he, Category.comp_id, Category.id_comp])
  let a₀ : ↥(pullback f t) := e' (IsLocalRing.closedPoint K)
  have ha₀ : pullback.fst f t a₀ = e (IsLocalRing.closedPoint k) := by
    change (e' ≫ pullback.fst f t) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_fst]
    exact congrArg e (Subsingleton.elim _ _)
  have hr : Set.range (pullback.snd e (pullback.fst f t)) =
      pullback.fst f t ⁻¹' {e (IsLocalRing.closedPoint k)} := by
    rw [Scheme.Pullback.range_snd]
    congr 1
    exact Set.range_eq_singleton fun _ => congrArg e (Subsingleton.elim _ _)
  have hsing (a : ↥(pullback f t)) (ha : pullback.fst f t a = pullback.fst f t a₀) :
      a = a₀ := by
    have ha' : a ∈ Set.range (pullback.snd e (pullback.fst f t)) := by
      rw [hr]
      exact ha.trans ha₀
    have ha₀' : a₀ ∈ Set.range (pullback.snd e (pullback.fst f t)) := by
      rw [hr]
      exact ha₀
    obtain ⟨z, rfl⟩ := ha'
    obtain ⟨w, hw⟩ := ha₀'
    have := subsingleton_pullback_section f e he t
    rw [← hw, Subsingleton.elim z w]
  have : ConnectedSpace ↥(pullback f t) :=
    connectedSpace_of_open_closed_singleton_fiber (pullback.fst f t)
      (pullback.fst f t).isOpenMap (pullback.fst f t).isClosedMap a₀ hsing
  have : IsIntegral (pullback f t) :=
    connectedLocallyNoetherianDomainStalksIntegral _ inferInstance inferInstance
      (smoothDomainStalks K _ (pullback.snd f t) inferInstance)
  have : GeometricallyIrreducible (pullback.snd f t) :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed _
  have : GeometricallyConnected (pullback.snd f t) :=
    GeometricallyIrreducible.geometricallyConnected _
  exact geometricallyConnected_of_surjective_baseChange f t

end Langlands.AlgebraicGeometry
