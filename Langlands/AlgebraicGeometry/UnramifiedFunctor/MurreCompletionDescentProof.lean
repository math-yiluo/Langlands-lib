import Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness
import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.ChartProperties
import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Saturation
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingRepr
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalReduction
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.QuasiAffineChart
import Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Step 2b of Murre's induction: descent from the completion

Let `R` be a noetherian local ring with completion `R̂`, punctured spectrum `U ⊆ Spec R`, and
let `F` satisfy Murre's conditions. If `F ×_S U` and `F ×_S Spec R̂` are represented by
separated, locally of finite type, formally unramified schemes `X_U` and `X'`, then so is `F`.

The proof: for every pair `(O', M)` of quasi-compact opens of `X'` and `X_U` with
`puncMap(ι⁻¹ O') ⊆ M`, the open `W = O' ∪ ι(puncMap⁻¹ M)` of `X'` is saturated for the
descent datum on `X'` (`sat_satOpen`), quasi-compact, hence quasi-affine over `Spec R̂` by
Zariski's main theorem; it therefore descends to a scheme `V` over `Spec R` carrying an element
`ξ ∈ F(V)` which is a monomorphism, infinitesimally étale and locally of finite type. Every
field-valued point of `F` factors through one of these charts, so Murre's Lemma 3
(`murreChartGluing`) makes `F` representable by a scheme `Y` locally of finite type over
`Spec R`. Since `Y ×_S Spec R̂ ≅ X'`, formal unramifiedness and separatedness descend along
the faithfully flat quasi-compact morphism `Spec R̂ ⟶ Spec R`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompletionDescent

set_option backward.isDefEq.respectTransparency.types false in
/-- Separatedness descends along flat surjective quasi-compact morphisms: the diagonal is
universally closed after base change, hence before, and a universally closed immersion is a
closed immersion. -/
lemma isSeparated_of_isSeparated_pullback_snd {Y S S' : Scheme.{u}} (q : Y ⟶ S) (π : S' ⟶ S)
    [Surjective π] [Flat π] [QuasiCompact π] [IsSeparated (pullback.snd q π)] :
    IsSeparated q := by
  have : (MorphismProperty.diagonal @UniversallyClosed).DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := inferInstance
  have : UniversallyClosed (pullback.diagonal q) :=
    MorphismProperty.diagonal_iff.mp (MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback q π).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      (MorphismProperty.diagonal_iff.mpr inferInstance))
  exact ⟨.of_isPreimmersion _ (pullback.diagonal q).isClosedMap.isClosed_range⟩

section Charts

variable {R : CommRingCat.{u}} [IsLocalRing R] [IsNoetherianRing R]
  {F : (Over (Spec R))ᵒᵖ ⥤ Type v} {X' : Scheme.{u}}
  {q' : X' ⟶ Spec (CommRingCat.of (AdicCompletion (maximalIdeal R) R))}
  (e : (baseChange (completionMap R) F).RepresentableBy (Over.mk q'))
  {XU : Scheme.{u}} {qU : XU ⟶ puncturedSpectrum R}
  (eU : (baseChange (puncturedSpectrum R).ι F).RepresentableBy (Over.mk qU))
  {σ : pullback (q' ≫ completionMap R) (completionMap R) ⟶ X'}
  (hσ : σ ≫ q' = pullback.snd _ _)
  (hσpt : pt e (prodOver q' (completionMap R)) σ (sigma_comp_eq hσ) =
    pt e (prodOver q' (completionMap R)) (pullback.fst _ _) (fst_comp_eq q' (completionMap R)))

include hσ hσpt in
/-- The chart attached to a pair `(O', M)`: the saturated open `O' ∪ ι(puncMap⁻¹ M)` of `X'`
descends to a scheme `V` over `Spec R` with an element `ξ ∈ F(V)` which is a monomorphism,
infinitesimally étale at every point and locally of finite type, and through which every
`v ∈ F(T)` factors whose morphism `T ×_S Spec R̂ ⟶ X'` lands in `O'`. -/
theorem exists_chart (hF : FaithfullyFlatSheaf F) [IsSeparated q'] [LocallyOfFiniteType q']
    [FormallyUnramified q'] (O' : X'.Opens) (M : XU.Opens) (hO : IsCompact (O' : Set X'))
    (hM : IsCompact (M : Set XU))
    (hOM : ∀ a, puncι (completionMap R) (puncturedSpectrum R) q' a ∈ O' →
      puncMap (completionMap R) (puncturedSpectrum R) e eU a ∈ M) :
    ∃ (V : Scheme.{u}) (w : V ⟶ Spec R) (ξ : F.obj (op (Over.mk w))),
      LocallyOfFiniteType w ∧ IsMonoElement F ξ ∧ (∀ y, InfinitesimallyEtaleAt F ξ y) ∧
      ∀ (T : Over (Spec R)) (v : F.obj (op T)) (v' : pullback T.hom (completionMap R) ⟶ X')
        (hv'q : v' ≫ q' = pullback.snd _ _),
        pt e (pullOver (completionMap R) T) v' (by rw [← Category.assoc, hv'q]; rfl) =
          F.map (pullHom (completionMap R) T).op v →
        Set.range v' ⊆ (O' : Set X') → ∃ h : T ⟶ Over.mk w, F.map h.op ξ = v := by
  let W := satOpen e eU O' M
  have hsat := sat_satOpen e eU hσ hσpt O' M hOM
  have : CompactSpace W := isCompact_iff_compactSpace.mp (isCompact_satOpen e eU hO hM)
  have : LocallyQuasiFinite q' := Langlands.AlgebraicGeometry.GenericFiniteness.locallyQuasiFinite_of_formallyUnramified q'
  have : W.toScheme.IsQuasiAffine :=
    LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite (W.ι ≫ q')
  obtain ⟨V, w, p, hpb, hfst⟩ := exists_chart_isPullback e hσ W.ι hsat hσpt
  obtain ⟨ξ, hξ⟩ := exists_isChartElement e hσ hσpt W.ι hsat hpb hfst hF
  refine ⟨V, w, ξ, locallyOfFiniteType_w W.ι hpb, isMonoElement_of_isChartElement e W.ι hpb hξ,
    infinitesimallyEtaleAt_of_isChartElement e hσ hσpt W.ι hsat hpb hfst hF hξ, ?_⟩
  intro T v v' hv'q hv' hr
  refine exists_map_eq_of_range_subset e hσ hσpt W.ι hsat hpb hfst hF hξ T v v' hv'q hv' ?_
  rw [Scheme.Opens.range_ι]
  exact fun x hx ↦ Or.inl (hr hx)

end Charts

end CompletionDescent

open CompletionDescent

/-- **Step 2b of Murre's induction** (Bourbaki exp. 294, Proposition 1, for the completion of a
local noetherian base). -/
theorem murreCompletionDescent : MurreCompletionDescentStatement.{u, v} := by
  intro R _ _ F hF hU hC
  obtain ⟨XU, qU, ⟨eU⟩, -, -, -⟩ := hU
  obtain ⟨X', q', ⟨e⟩, hsep, hlft, hfu⟩ := hC
  obtain ⟨σ, hσ, hσpt⟩ := exists_sigma e
  obtain ⟨hsmall, hzar, hff, hfilt, hadic, -⟩ := hF
  let ι : Type u := {c : X'.Opens × XU.Opens // IsCompact (c.1 : Set X') ∧
    IsCompact (c.2 : Set XU) ∧ ∀ a, puncι (completionMap R) (puncturedSpectrum R) q' a ∈ c.1 →
      puncMap (completionMap R) (puncturedSpectrum R) e eU a ∈ c.2}
  have hch := fun c : ι ↦ exists_chart e eU hσ hσpt hff c.1.1 c.1.2 c.2.1 c.2.2.1 c.2.2.2
  choose V w ξ hlftV hmono hét hfac using hch
  obtain ⟨Y, q, e', hlftY, -, -⟩ := ChartGluing.murreChartGluing (Spec R) F hsmall hzar hff hfilt hadic ι
    (fun c ↦ Over.mk (w c)) ξ hlftV hmono hét (by
      intro K _ f η
      let T : Over (Spec R) := Over.mk f
      obtain ⟨v', hv'q, hv'⟩ := exists_pt e (pullOver (completionMap R) T)
        (pullback.snd T.hom (completionMap R)) rfl (F.map (pullHom (completionMap R) T).op η)
      have : IsAffine (pullOver (completionMap R) T).left := by
        change IsAffine (pullback f (completionMap R))
        infer_instance
      have hK : IsCompact (Set.range v') := isCompact_range v'.continuous
      obtain ⟨O', M, hO, hM, hOM, hKO⟩ := exists_satOpen e eU hK
      exact ⟨⟨(O', M), hO, hM, hOM⟩, hfac ⟨(O', M), hO, hM, hOM⟩ T η v' hv'q hv' hKO⟩)
  -- `Y ×_S Spec R̂` is isomorphic to `X'` over `Spec R̂`.
  let i := (LocalToGlobal.representableByBaseChange e' (completionMap R)).uniqueUpToIso e
  have hw : i.hom.left ≫ q' = pullback.snd q (completionMap R) := Over.w i.hom
  have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso i).hom)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (completionMap R) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hpb := (IsPullback.of_hasPullback q (completionMap R)).flip
  refine ⟨Y, q, ⟨e'⟩, ?_, hlftY, ?_⟩
  · have : IsSeparated (pullback.snd q (completionMap R)) := by
      rw [← hw]
      infer_instance
    exact isSeparated_of_isSeparated_pullback_snd q (completionMap R)
  · have hsnd : FormallyUnramified (pullback.snd q (completionMap R)) := by
      rw [← hw]
      have : FormallyUnramified i.hom.left := inferInstance
      exact MorphismProperty.comp_mem @FormallyUnramified _ _ this hfu
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @FormallyUnramified)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb hQ hsnd

end Langlands.AlgebraicGeometry.UnramifiedFunctor
