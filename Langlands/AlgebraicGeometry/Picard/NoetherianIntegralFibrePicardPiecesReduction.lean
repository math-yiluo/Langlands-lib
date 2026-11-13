import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardPiecesReductionStatement
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Proof of the reduction of the noetherian-test Picard scheme to its pieces -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

namespace Langlands.AlgebraicGeometry.Picard

/-- A presheaf on schemes over `S` which is an fppf sheaf is a Zariski sheaf. -/
lemma isSheaf_zariskiTopology_over_of_fppf {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F := by
  have hle : Scheme.zariskiTopology.{u} ≤ Scheme.fppfTopology.{u} :=
    Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
  exact Presheaf.IsSheaf.of_le (fun Y R hR => hle Y.left hR) hF

/-- Composing the inverse symmetry of `T' ×_S X` with the base change map of `h` is the base
change map of `X ×_S T'` followed by the inverse symmetry of `T ×_S X`. -/
lemma relativeSpaceSymmetry_inv_map {S X : Scheme.{u}} (f : X ⟶ S) {T T' : Over S}
    (h : T' ⟶ T) :
    (relativeSpaceSymmetry f T').inv ≫ (relativeSpace f).map h =
      pullback.map f T'.hom f T.hom (𝟙 X) h.left (𝟙 S) (by simp) (by simp) ≫
        (relativeSpaceSymmetry f T).inv := by
  have h1 : (relativeSpace f).map h ≫ pullback.fst T.hom f = pullback.fst T'.hom f ≫ h.left :=
    (relativeProjection f).naturality h
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, h1]
    simp only [relativeSpaceSymmetry, pullbackSymmetry_inv_comp_fst_assoc,
      pullbackSymmetry_inv_comp_fst]
    exact (pullback.lift_snd _ _ _).symm
  · rw [Category.assoc, Category.assoc, relativeSpace_map_snd]
    simp only [relativeSpaceSymmetry, pullbackSymmetry_inv_comp_snd]
    exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm

/-- The reduction of the noetherian-test Picard scheme to its Hilbert-polynomial pieces. -/
theorem noetherianIntegralFibrePicardPiecesReduction :
    NoetherianIntegralFibrePicardPiecesReductionStatement.{u} := by
  intro hK1 hd hC hcls he R _ _ X f hprop hflat hgi hsec hample
  obtain ⟨𝓛X, h𝓛inv, h𝓛cis⟩ := hK1 R X f hprop hample
  obtain ⟨κ, θ, U, P1, P2, P3, P4, P5⟩ := hd R f 𝓛X hprop hflat hgi h𝓛inv h𝓛cis
  have hC' := hC R f 𝓛X hprop hflat hgi hsec h𝓛inv h𝓛cis κ θ U P1 P2 P4 P5
  have hlfp : LocallyOfFinitePresentation f := by
    have := hprop
    infer_instance
  have hcls' := hcls f hprop hflat hlfp hgi hsec
  -- `U` only depends on the isomorphism class of the module
  have Uiso : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ Spec (CommRingCat.of R))
      (L L' : (pullback f s).Modules), Scheme.Modules.IsInvertible L →
      Scheme.Modules.IsInvertible L' → Nonempty (L ≅ L') →
      ∀ (c : κ) (m : ℕ), U T s L c m = U T s L' c m := by
    intro T _ s L L' hL hL' ⟨e⟩ c m
    refine P1 T s L L' (𝟙_ T.Modules) hL hL' (Scheme.Modules.isInvertible_unit T) ⟨?_⟩ c m
    exact e ≪≫ (ρ_ L').symm ≪≫
      whiskerLeftIso L' (Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd f s)).symm
  -- base change along a morphism whose composite with the structure map is only propositionally
  -- the structure map
  have P2' : ∀ (T T' : Scheme.{u}) [IsLocallyNoetherian T] [IsLocallyNoetherian T']
      (s : T ⟶ Spec (CommRingCat.of R)) (s' : T' ⟶ Spec (CommRingCat.of R)) (h : T' ⟶ T)
      (e : h ≫ s = s') (L : (pullback f s).Modules), Scheme.Modules.IsInvertible L →
      ∀ (c : κ) (m : ℕ),
        U T' s' ((Scheme.Modules.pullback
            (pullback.map f s' f s (𝟙 X) h (𝟙 _) (by simp) (by simp [e]))).obj L) c m =
          h ⁻¹ᵁ U T s L c m := by
    intro T T' _ _ s s' h e L hL c m
    subst e
    exact P2 T T' s h L hL c m
  -- transport of line bundles on `T ×_S X` to modules on `X ×_S T`
  let tr : ∀ T : Over (Spec (CommRingCat.of R)), LineBundle ((relativeSpace f).obj T) →
      (pullback f T.hom).Modules := fun T L =>
    (Scheme.Modules.pullback (relativeSpaceSymmetry f T).inv).obj L.obj
  have tr_inv : ∀ T L, Scheme.Modules.IsInvertible (tr T L) := fun T L =>
    (isInvertible_of_isLocallyFreeRankOne L.property).pullback _
  -- `U ∘ tr` only depends on the fppf class
  have Ucls : ∀ (T : Over (Spec (CommRingCat.of R))) [IsLocallyNoetherian T.left]
      (L L' : LineBundle ((relativeSpace f).obj T)),
      RelativePicard.sheafClassOf f T L = RelativePicard.sheafClassOf f T L' →
      ∀ (c : κ) (m : ℕ), U T.left T.hom (tr T L) c m = U T.left T.hom (tr T L') c m := by
    intro T _ L L' hLL' c m
    obtain ⟨N, hN, ⟨e⟩⟩ := ((hcls' T).2 L L').1 hLL'
    have hσ : (relativeSpaceSymmetry f T).inv ≫ (relativeProjection f).app T =
        pullback.snd f T.hom := by
      simp [relativeSpaceSymmetry, relativeProjection]
    refine P1 T.left T.hom (tr T L) (tr T L') N (tr_inv T L) (tr_inv T L') hN ⟨?_⟩ c m
    exact (Scheme.Modules.pullback (relativeSpaceSymmetry f T).inv).mapIso e ≪≫
      Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        whiskerLeftIso (tr T L')
          ((Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr hσ).app N)
  -- `U ∘ tr` is compatible with base change
  have Ubc : ∀ (T T' : Over (Spec (CommRingCat.of R))) [IsLocallyNoetherian T.left]
      [IsLocallyNoetherian T'.left] (h : T' ⟶ T) (L : LineBundle ((relativeSpace f).obj T))
      (c : κ) (m : ℕ),
      U T'.left T'.hom (tr T' ((LineBundle.pullback ((relativeSpace f).map h)).obj L)) c m =
        h.left ⁻¹ᵁ U T.left T.hom (tr T L) c m := by
    intro T T' _ _ h L c m
    have hL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback
        (pullback.map f T'.hom f T.hom (𝟙 X) h.left (𝟙 _) (by simp) (by simp))).obj
          (tr T L)) := (tr_inv T L).pullback _
    rw [← P2' T.left T'.left T.hom T'.hom h.left (Over.w h) (tr T L) (tr_inv T L) c m]
    refine Uiso T'.left T'.hom _ _ (tr_inv T' _) hL ⟨?_⟩ c m
    exact (Scheme.Modules.pullbackComp _ _).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr (relativeSpaceSymmetry_inv_map f h)).app L.obj ≪≫
        ((Scheme.Modules.pullbackComp _ _).app L.obj).symm
  -- chosen line bundles representing the elements of the Picard sheaf
  choose rep hrep using fun T => (hcls' T).1
  let V : ∀ T : Over (Spec (CommRingCat.of R)),
      (RelativePicard.classSheafPresheaf f).obj (op T) → κ → ℕ → T.left.Opens :=
    fun T ξ c m => U T.left T.hom (tr T (rep T ξ)) c m
  choose Q β hQ hβ using hC'
  refine he R (RelativePicard.classSheafPresheaf f)
    (isSheaf_zariskiTopology_over_of_fppf (RelativePicard.classSheafPresheaf_isSheaf f))
    κ V Q β ?_ ?_ ?_ ?_
  · intro T T' _ _ h ξ c m
    have hcl : RelativePicard.sheafClassOf f T' (rep T' ((RelativePicard.classSheafPresheaf f).map
          h.op ξ)) = RelativePicard.sheafClassOf f T'
          ((LineBundle.pullback ((relativeSpace f).map h)).obj (rep T ξ)) := by
      rw [hrep, ← RelativePicard.map_sheafClassOf, hrep]
    change U T'.left T'.hom _ c m = h.left ⁻¹ᵁ U T.left T.hom _ c m
    rw [Ucls T' _ _ hcl c m, Ubc T T' h (rep T ξ) c m]
  · intro T _ ξ
    exact P3 T.left T.hom (tr T (rep T ξ)) (tr_inv T _)
  · intro c m
    obtain ⟨n, i, hi, -, hc⟩ := hQ c m
    exact ⟨n, i, hi, hc⟩
  · intro c m T _
    refine ⟨(hβ c m T).1, fun ξ => ?_⟩
    have := (hβ c m T).2 (rep T ξ)
    rw [hrep] at this
    exact this.symm

end Langlands.AlgebraicGeometry.Picard
