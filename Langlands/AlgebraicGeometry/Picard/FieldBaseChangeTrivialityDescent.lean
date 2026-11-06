import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Triviality of line bundles descends along field extensions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- The pullback of a trivial module sheaf is trivial. -/
lemma pullback_nonempty_iso_structureSheaf {Y Z : Scheme.{u}} (a : Y ⟶ Z) {N : Z.Modules}
    (e : N ≅ Langlands.Scheme.Modules.structureSheaf Z) :
    Nonempty ((Scheme.Modules.pullback a).obj N ≅ Langlands.Scheme.Modules.structureSheaf Y) :=
  ⟨(Scheme.Modules.pullback a).mapIso e ≪≫ Langlands.Scheme.Modules.pullbackUnitIso a⟩

/-- Pullback along an isomorphism of schemes reflects isomorphism of module sheaves. -/
lemma nonempty_iso_of_pullback_isIso {Y Z : Scheme.{u}} (a : Y ⟶ Z) [IsIso a]
    {N N' : Z.Modules}
    (e : (Scheme.Modules.pullback a).obj N ≅ (Scheme.Modules.pullback a).obj N') :
    Nonempty (N ≅ N') :=
  ⟨((Scheme.Modules.pullbackId Z).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id a).symm).app N ≪≫
    ((Scheme.Modules.pullbackComp (inv a) a).app N).symm ≪≫
    (Scheme.Modules.pullback (inv a)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (inv a) a).app N' ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id a)).app N' ≪≫
    (Scheme.Modules.pullbackId Z).app N'⟩

/-- Pullback along an isomorphism of schemes reflects triviality of module sheaves. -/
lemma nonempty_iso_structureSheaf_of_pullback_isIso {Y Z : Scheme.{u}} (a : Y ⟶ Z) [IsIso a]
    {N : Z.Modules}
    (e : (Scheme.Modules.pullback a).obj N ≅ Langlands.Scheme.Modules.structureSheaf Y) :
    Nonempty (N ≅ Langlands.Scheme.Modules.structureSheaf Z) :=
  nonempty_iso_of_pullback_isIso a
    (e ≪≫ (Langlands.Scheme.Modules.pullbackUnitIso a).symm)

/-- Let `X` be smooth, proper and geometrically connected over a field `k`, and let `L` be a
locally free sheaf of rank one on `X`. If the pullback of `L` to `X ×_k K` is trivial for some
morphism `Spec K ⟶ Spec k` from the spectrum of a field, then `L` itself is trivial. -/
theorem fieldBaseChangeTrivialityDescent {k K : Type u} [Field k] [Field K]
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [IsProper f] [GeometricallyConnected f]
    (L : X.Modules) (hL : IsLocallyFreeRankOne L)
    (h : Nonempty ((Scheme.Modules.pullback (pullback.fst f g)).obj L ≅
      Langlands.Scheme.Modules.structureSheaf (pullback f g))) :
    Nonempty (L ≅ Langlands.Scheme.Modules.structureSheaf X) := by
  obtain ⟨eK⟩ := h
  have : GeometricallyIntegral f :=
    Langlands.AbelianScheme.smoothGeometricIntegrality k X f inferInstance inferInstance
  have hH0 : ∀ (B : Type u) [CommRing B] [Algebra k B],
      Function.Bijective
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop := by
    intro B _ _
    have := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B))))
      inferInstance inferInstance inferInstance ⊤
    exact ConcreteCategory.bijective_of_isIso
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).app ⊤)
  let T := Spec (CommRingCat.of k)
  let M : (pullback f (𝟙 T)).Modules := (Scheme.Modules.pullback (pullback.fst f (𝟙 T))).obj L
  have hM : IsLocallyFreeRankOne M := hL.pullback _
  obtain ⟨Z, ι, hι, hZ⟩ := noetherianLineBundleSeesaw f hH0 (𝟙 T) M
    (SheafOfModules.unit (pullback f (𝟙 T)).ringCatSheaf) hM
    (LineBundle.trivial (pullback f (𝟙 T))).property
  -- The pullbacks of `M` and of the structure sheaf agree after base change along `g`.
  let φ : pullback (pullback.snd f (𝟙 T)) g ⟶ pullback f g :=
    pullback.lift (pullback.fst (pullback.snd f (𝟙 T)) g ≫ pullback.fst f (𝟙 T))
      (pullback.snd (pullback.snd f (𝟙 T)) g) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, Category.comp_id])
  have hφ : φ ≫ pullback.fst f g =
      pullback.fst (pullback.snd f (𝟙 T)) g ≫ pullback.fst f (𝟙 T) := pullback.lift_fst _ _ _
  obtain ⟨eφ⟩ := pullback_nonempty_iso_structureSheaf φ eK
  let EK : (Scheme.Modules.pullback (pullback.fst (pullback.snd f (𝟙 T)) g)).obj M ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd f (𝟙 T)) g)).obj
        (SheafOfModules.unit (pullback f (𝟙 T)).ringCatSheaf) :=
    (Scheme.Modules.pullbackComp _ _).app L ≪≫
      (Scheme.Modules.pullbackCongr hφ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp φ (pullback.fst f g)).app L).symm ≪≫ eφ ≪≫
      (Langlands.Scheme.Modules.pullbackUnitIso _).symm
  obtain ⟨z, hz⟩ := (hZ g).2 fun τ =>
    ⟨⊤, trivial, ⟨(Scheme.Modules.restrictFunctor _).mapIso EK⟩⟩
  -- The closed subscheme `Z` has a point, hence is all of `Spec k`.
  have : Surjective ι := ⟨fun x => ⟨z.base default, Subsingleton.elim _ _⟩⟩
  have : IsIso ι := isIso_of_isClosedImmersion_of_surjective ι
  obtain ⟨U, hU, ⟨eU⟩⟩ := ((hZ (𝟙 T)).1 ⟨inv ι, IsIso.inv_hom_id ι⟩) default
  let W := (pullback.snd (pullback.snd f (𝟙 T)) (𝟙 T)) ⁻¹ᵁ U
  have hW : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    show pullback.snd (pullback.snd f (𝟙 T)) (𝟙 T) x ∈ U
    rwa [Subsingleton.elim (pullback.snd (pullback.snd f (𝟙 T)) (𝟙 T) x) default]
  have : IsIso W.ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x => ⟨⟨x, by rw [hW]; trivial⟩, rfl⟩⟩⟩
  obtain ⟨eW⟩ := nonempty_iso_of_pullback_isIso W.ι
    (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm ≪≫ eU ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _)
  obtain ⟨eT⟩ := nonempty_iso_structureSheaf_of_pullback_isIso
    (pullback.fst (pullback.snd f (𝟙 T)) (𝟙 T))
    (eW ≪≫ Langlands.Scheme.Modules.pullbackUnitIso _)
  exact nonempty_iso_structureSheaf_of_pullback_isIso (pullback.fst f (𝟙 T)) eT

end Langlands.AlgebraicGeometry.Picard
