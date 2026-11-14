import Langlands.AlgebraicGeometry.FppfKernelPairDescent
import Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure

/-! # Proof of the reduction of the fppf quotient on locally noetherian tests to effective
quotients by flat proper equivalence relations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReduction

open AlgebraicSpace

section General

variable {S : Scheme.{u}} {G : FppfSheaf S} {Z R : Over S}
  {ζ : (schemeYoneda S).obj Z ⟶ G.obj} {s t : R ⟶ Z}

/-- Naturality of a map out of the functor of points of `Z`, on precomposed points. -/
lemma app_comp {T T' : Over S} (f : T' ⟶ T) (x : T ⟶ Z) :
    ζ.app (op T') (ULift.up (f ≫ x) : ULift.{u + 1} (T' ⟶ Z)) =
      G.obj.map f.op (ζ.app (op T) (ULift.up x : ULift.{u + 1} (T ⟶ Z))) :=
  NatTrans.naturality_apply ζ f.op (ULift.up x : ULift.{u + 1} (T ⟶ Z))

/-- The two projections of the relation have the same image in `G` on every point. -/
lemma app_s_eq_app_t (hst : (schemeYoneda S).map s ≫ ζ = (schemeYoneda S).map t ≫ ζ)
    {T : Over S} (r : T ⟶ R) :
    ζ.app (op T) (ULift.up (r ≫ s) : ULift.{u + 1} (T ⟶ Z)) =
      ζ.app (op T) (ULift.up (r ≫ t) : ULift.{u + 1} (T ⟶ Z)) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app hst (op T))
    (ULift.up r : ULift.{u + 1} (T ⟶ R))
  exact this

/-- A factorization of `ζ` through `π` on points. -/
lemma fac_app {Q : Over S} {π : Z ⟶ Q} {e : (schemeYoneda S).obj Q ⟶ G.obj}
    (he : (schemeYoneda S).map π ≫ e = ζ) {T : Over S} (x : T ⟶ Z) :
    e.app (op T) (ULift.up (x ≫ π) : ULift.{u + 1} (T ⟶ Q)) =
      ζ.app (op T) (ULift.up x : ULift.{u + 1} (T ⟶ Z)) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app he (op T))
    (ULift.up x : ULift.{u + 1} (T ⟶ Z))
  exact this

variable (hst : (schemeYoneda S).map s ≫ ζ = (schemeYoneda S).map t ≫ ζ)
  (huniq : ∀ (T : Over S) [IsLocallyNoetherian T.left] (x y : T ⟶ Z),
    ζ.app (op T) (ULift.up x) = ζ.app (op T) (ULift.up y) →
      ∃! r : T ⟶ R, r ≫ s = x ∧ r ≫ t = y)
include hst huniq

/-- On a locally noetherian test, a point of `R` is determined by its two projections. -/
lemma eq_of_comp_eq (T : Over S) [IsLocallyNoetherian T.left] {a b : T ⟶ R}
    (hs : a ≫ s = b ≫ s) (ht : a ≫ t = b ≫ t) : a = b :=
  (huniq T (a ≫ s) (a ≫ t) (app_s_eq_app_t hst a)).unique ⟨rfl, rfl⟩ ⟨hs.symm, ht.symm⟩

/-- The morphism from `R` to `Z ×_S Z` given by the two projections is a monomorphism. -/
lemma mono_of_fst_snd [IsLocallyNoetherian R.left] (l : R.left ⟶ pullback Z.hom Z.hom)
    (hl₁ : l ≫ pullback.fst Z.hom Z.hom = s.left) (hl₂ : l ≫ pullback.snd Z.hom Z.hom = t.left)
    [LocallyOfFiniteType s.left] : Mono l := by
  have : LocallyOfFiniteType (l ≫ pullback.fst Z.hom Z.hom) := by
    rw [hl₁]
    infer_instance
  have : LocallyOfFiniteType l := locallyOfFiniteType_of_comp l (pullback.fst Z.hom Z.hom)
  have : IsLocallyNoetherian (pullback l l) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst l l)
  have hs' : pullback.fst l l ≫ s.left = pullback.snd l l ≫ s.left := by
    rw [← hl₁, ← Category.assoc, pullback.condition, Category.assoc]
  have ht' : pullback.fst l l ≫ t.left = pullback.snd l l ≫ t.left := by
    rw [← hl₂, ← Category.assoc, pullback.condition, Category.assoc]
  let K : Over S := Over.mk (pullback.fst l l ≫ R.hom)
  have : IsLocallyNoetherian K.left := by assumption
  let a : K ⟶ R := Over.homMk (pullback.fst l l) rfl
  let b : K ⟶ R := Over.homMk (pullback.snd l l) (by
    change pullback.snd l l ≫ R.hom = pullback.fst l l ≫ R.hom
    rw [← Over.w s, ← Category.assoc, ← hs', Category.assoc])
  have hab : a = b := eq_of_comp_eq hst huniq K (Over.OverMorphism.ext hs')
    (Over.OverMorphism.ext ht')
  have hfs : pullback.fst l l = pullback.snd l l := congrArg CommaMorphism.left hab
  constructor
  intro T x y hxy
  calc x = pullback.lift x y hxy ≫ pullback.fst l l := (pullback.lift_fst _ _ _).symm
    _ = pullback.lift x y hxy ≫ pullback.snd l l := by rw [hfs]
    _ = y := pullback.lift_snd _ _ _

/-- The image of `R` on the points of every scheme is an equivalence relation. -/
lemma equivalence [IsLocallyNoetherian Z.left] [IsLocallyNoetherian R.left]
    [LocallyOfFiniteType s.left] (T : Scheme.{u}) :
    Equivalence fun x y : T ⟶ Z.left => ∃ φ : T ⟶ R.left, φ ≫ s.left = x ∧ φ ≫ t.left = y := by
  obtain ⟨δ, ⟨hδs, hδt⟩, -⟩ := huniq Z (𝟙 Z) (𝟙 Z) rfl
  obtain ⟨σ, ⟨hσs, hσt⟩, -⟩ := huniq R t s (by
    simpa using (app_s_eq_app_t hst (𝟙 R)).symm)
  have : IsLocallyNoetherian (pullback t.left s.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst t.left s.left)
  let P : Over S := Over.mk (pullback.fst t.left s.left ≫ R.hom)
  have : IsLocallyNoetherian P.left := by assumption
  let p₁ : P ⟶ R := Over.homMk (pullback.fst t.left s.left) rfl
  let p₂ : P ⟶ R := Over.homMk (pullback.snd t.left s.left) (by
    change pullback.snd t.left s.left ≫ R.hom = pullback.fst t.left s.left ≫ R.hom
    rw [← Over.w s, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w t, Over.w s])
  have hp : p₁ ≫ t = p₂ ≫ s := Over.OverMorphism.ext pullback.condition
  obtain ⟨μ, ⟨hμs, hμt⟩, -⟩ := huniq P (p₁ ≫ s) (p₂ ≫ t) (by
    rw [app_s_eq_app_t hst p₁, hp, app_s_eq_app_t hst p₂])
  refine ⟨fun x => ⟨x ≫ δ.left, ?_, ?_⟩, fun {x y} h => ?_, fun {x y z} h h' => ?_⟩
  · rw [Category.assoc, ← Over.comp_left, hδs, Over.id_left, Category.comp_id]
  · rw [Category.assoc, ← Over.comp_left, hδt, Over.id_left, Category.comp_id]
  · obtain ⟨φ, h₁, h₂⟩ := h
    refine ⟨φ ≫ σ.left, ?_, ?_⟩
    · rw [Category.assoc, ← Over.comp_left, hσs, h₂]
    · rw [Category.assoc, ← Over.comp_left, hσt, h₁]
  · obtain ⟨φ₁, h₁, h₂⟩ := h
    obtain ⟨φ₂, h₃, h₄⟩ := h'
    have hw : φ₁ ≫ t.left = φ₂ ≫ s.left := by rw [h₂, h₃]
    refine ⟨pullback.lift φ₁ φ₂ hw ≫ μ.left, ?_, ?_⟩
    · rw [Category.assoc, ← Over.comp_left, hμs, Over.comp_left]
      change pullback.lift φ₁ φ₂ hw ≫ pullback.fst t.left s.left ≫ s.left = x
      rw [pullback.lift_fst_assoc, h₁]
    · rw [Category.assoc, ← Over.comp_left, hμt, Over.comp_left]
      change pullback.lift φ₁ φ₂ hw ≫ pullback.snd t.left s.left ≫ t.left = z
      rw [pullback.lift_snd_assoc, h₄]

omit hst in
/-- Two points `x, y` of `Q` over `T` with the same image in `G` agree, if after pulling back
along an epimorphism `d : W ⟶ T` from a locally noetherian scheme they lift to points of `Z`. -/
lemma eq_of_cover {Q : Over S} {π : Z ⟶ Q} {e : (schemeYoneda S).obj Q ⟶ G.obj}
    (he : (schemeYoneda S).map π ≫ e = ζ) (hπ : s ≫ π = t ≫ π)
    {T : Over S} {W : Scheme.{u}} [IsLocallyNoetherian W] (d : W ⟶ T.left) [Epi d]
    {x y : T ⟶ Q} (a b : W ⟶ Z.left) (ha : a ≫ π.left = d ≫ x.left)
    (hb : b ≫ π.left = d ≫ y.left)
    (hxy : e.app (op T) (ULift.up x : ULift.{u + 1} (T ⟶ Q)) =
      e.app (op T) (ULift.up y : ULift.{u + 1} (T ⟶ Q))) : x = y := by
  let W' : Over S := Over.mk (d ≫ T.hom)
  have : IsLocallyNoetherian W'.left := by assumption
  let d' : W' ⟶ T := Over.homMk d rfl
  let a' : W' ⟶ Z := Over.homMk a (by
    change a ≫ Z.hom = d ≫ T.hom
    rw [← Over.w π, ← Category.assoc, ha, Category.assoc, Over.w x])
  let b' : W' ⟶ Z := Over.homMk b (by
    change b ≫ Z.hom = d ≫ T.hom
    rw [← Over.w π, ← Category.assoc, hb, Category.assoc, Over.w y])
  have ha' : a' ≫ π = d' ≫ x := Over.OverMorphism.ext ha
  have hb' : b' ≫ π = d' ≫ y := Over.OverMorphism.ext hb
  have hab : ζ.app (op W') (ULift.up a' : ULift.{u + 1} (W' ⟶ Z)) =
      ζ.app (op W') (ULift.up b' : ULift.{u + 1} (W' ⟶ Z)) := by
    rw [← fac_app he a', ← fac_app he b', ha', hb', app_comp (ζ := e) d' x,
      app_comp (ζ := e) d' y, hxy]
  obtain ⟨r, ⟨hrs, hrt⟩, -⟩ := huniq W' a' b' hab
  have hdxy : d' ≫ x = d' ≫ y := by
    rw [← ha', ← hb', ← hrs, ← hrt, Category.assoc, Category.assoc, hπ]
  apply Over.OverMorphism.ext
  exact (cancel_epi d).mp (congrArg CommaMorphism.left hdxy)

omit hst in
/-- The factorization `e` is injective on the points of every locally noetherian test. -/
lemma injective_app {Q : Over S} {π : Z ⟶ Q} {e : (schemeYoneda S).obj Q ⟶ G.obj}
    (he : (schemeYoneda S).map π ≫ e = ζ) (hπ : s ≫ π = t ≫ π)
    [Flat π.left] [Surjective π.left] [LocallyOfFinitePresentation π.left]
    (T : Over S) [IsLocallyNoetherian T.left] :
    Function.Injective (e.app (op T)) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  have : IsLocallyNoetherian (pullback (pullback.fst x.left π.left ≫ y.left) π.left) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst (pullback.fst x.left π.left ≫ y.left) π.left ≫ pullback.fst x.left π.left)
  have : Epi (pullback.fst (pullback.fst x.left π.left ≫ y.left) π.left ≫
      pullback.fst x.left π.left) := Flat.epi_of_flat_of_surjective _
  refine congrArg ULift.up (eq_of_cover huniq he hπ
    (pullback.fst (pullback.fst x.left π.left ≫ y.left) π.left ≫ pullback.fst x.left π.left)
    (pullback.fst (pullback.fst x.left π.left ≫ y.left) π.left ≫ pullback.snd x.left π.left)
    (pullback.snd (pullback.fst x.left π.left ≫ y.left) π.left) ?_ ?_ hxy)
  · rw [Category.assoc, ← pullback.condition, Category.assoc]
  · rw [← pullback.condition, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
omit hst in
/-- The factorization `e` is surjective on the points of every locally noetherian test. -/
lemma surjective_app {Q : Over S} {π : Z ⟶ Q} {e : (schemeYoneda S).obj Q ⟶ G.obj}
    (he : (schemeYoneda S).map π ≫ e = ζ) (hπ : s ≫ π = t ≫ π)
    (hζ : Presheaf.IsLocallySurjective (fppfTopology S) ζ)
    (T : Over S) [IsLocallyNoetherian T.left] :
    Function.Surjective (e.app (op T)) := by
  intro g
  let Pr : Presieve T := fun ⦃V⦄ (f : V ⟶ T) =>
    (Presheaf.imageSieve ζ g).arrows f ∧ LocallyOfFiniteType f.left
  have hPr : Sieve.generate Pr ∈ fppfTopology S T := by
    have h₀ : Presheaf.imageSieve ζ g ∈ fppfTopology S T :=
      Presheaf.imageSieve_mem (J := fppfTopology S) ζ g
    have : (@Flat ⊓ @LocallyOfFinitePresentation :
        MorphismProperty Scheme.{u}).IsMultiplicative :=
      { id_mem := fun _ ↦ ⟨inferInstance, inferInstance⟩
        comp_mem := fun f g hf hg ↦ by
          have := hf.1
          have := hf.2
          have := hg.1
          have := hg.2
          exact ⟨inferInstance, inferInstance⟩ }
    rw [GrothendieckTopology.mem_over_iff] at h₀ ⊢
    obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff
      (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))).mp h₀
    refine (Scheme.mem_grothendieckTopology_iff
      (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))).mpr
      ⟨𝒰, ?_⟩
    rintro _ _ ⟨j⟩
    have hj := h𝒰 _ _ (Presieve.ofArrows.mk j)
    rw [Sieve.overEquiv_iff] at hj ⊢
    have hprop : Flat (𝒰.f j) ∧ LocallyOfFinitePresentation (𝒰.f j) := 𝒰.map_prop j
    have := hprop.2
    exact Sieve.le_generate Pr _ _ ⟨hj, inferInstanceAs (LocallyOfFiniteType (𝒰.f j))⟩
  have hQ : Presieve.IsSheafFor ((schemeYoneda S).obj Q) Pr := by
    rw [Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).mp ((schemeSheaf S).obj Q).property) _ hPr
  have hG : Presieve.IsSeparatedFor G.obj Pr := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact (((isSheaf_iff_isSheaf_of_type _ _).mp G.property) _ hPr).isSeparatedFor
  let lift : ∀ ⦃V : Over S⦄ (f : V ⟶ T), Pr f → (V ⟶ Z) := fun V f hf => hf.1.choose.down
  have hlift : ∀ ⦃V : Over S⦄ (f : V ⟶ T) (hf : Pr f),
      ζ.app (op V) (ULift.up (lift f hf) : ULift.{u + 1} (V ⟶ Z)) = G.obj.map f.op g :=
    fun V f hf => hf.1.choose_spec
  let fam : Presieve.FamilyOfElements ((schemeYoneda S).obj Q) Pr :=
    fun V f hf => (ULift.up (lift f hf ≫ π) : ULift.{u + 1} (V ⟶ Q))
  have hfam : fam.Compatible := by
    rw [Presieve.pullbackCompatible_iff]
    intro V₁ V₂ f₁ f₂ h₁ h₂
    have : LocallyOfFiniteType f₁.left := h₁.2
    have : LocallyOfFiniteType f₂.left := h₂.2
    have : LocallyOfFiniteType (pullback.fst f₁ f₂).left :=
      MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback f₁ f₂).map (Over.forget S)).flip h₂.2
    have : IsLocallyNoetherian (pullback f₁ f₂).left :=
      LocallyOfFiniteType.isLocallyNoetherian ((pullback.fst f₁ f₂).left ≫ f₁.left)
    have hζ₁₂ : ζ.app (op (pullback f₁ f₂)) (ULift.up (pullback.fst f₁ f₂ ≫ lift f₁ h₁) :
          ULift.{u + 1} (pullback f₁ f₂ ⟶ Z)) =
        ζ.app (op (pullback f₁ f₂)) (ULift.up (pullback.snd f₁ f₂ ≫ lift f₂ h₂) :
          ULift.{u + 1} (pullback f₁ f₂ ⟶ Z)) := by
      rw [app_comp (ζ := ζ) (pullback.fst f₁ f₂) (lift f₁ h₁),
        app_comp (ζ := ζ) (pullback.snd f₁ f₂) (lift f₂ h₂), hlift f₁ h₁, hlift f₂ h₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
        pullback.condition]
    obtain ⟨r, ⟨hrs, hrt⟩, -⟩ := huniq _ _ _ hζ₁₂
    apply ULift.ext
    change pullback.fst f₁ f₂ ≫ lift f₁ h₁ ≫ π = pullback.snd f₁ f₂ ≫ lift f₂ h₂ ≫ π
    rw [← Category.assoc, ← hrs, ← Category.assoc, ← hrt, Category.assoc, Category.assoc, hπ]
  obtain ⟨x, hx, -⟩ := hQ fam hfam
  refine ⟨x, hG.ext fun V f hf => ?_⟩
  rw [← NatTrans.naturality_apply e f.op x, hx f hf]
  exact (fac_app he (lift f hf)).trans (hlift f hf)

end General

section Main

/-- The effective quotient theorem for flat proper equivalence relations implies the
representability on locally noetherian tests of fppf sheaves with such a presentation. -/
theorem fppfQuotientLocallyNoetherianReduction :
    FppfQuotientLocallyNoetherianReductionStatement.{u} := by
  intro hc A _ _ G Z R ζ s t hZ hζ hst huniq hflat hprop
  have : LocallyOfFiniteType Z.hom := by
    obtain ⟨n, i, hi, -, hip⟩ := hZ
    rw [← hip]
    infer_instance
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian R.left := LocallyOfFiniteType.isLocallyNoetherian s.left
  have h : s.left ≫ Z.hom = t.left ≫ Z.hom := by rw [Over.w s, Over.w t]
  obtain ⟨Q₀, q, π₀, hQ, hπq, hπflat, hπsurj, hπprop, hπlfp, hpb⟩ :=
    hc A Z.hom s.left t.left h hZ
      (mono_of_fst_snd hst huniq _ (pullback.lift_fst _ _ h) (pullback.lift_snd _ _ h))
      (equivalence hst huniq) hflat hprop
  let Q : Over (Spec (CommRingCat.of A)) := Over.mk q
  let π : Z ⟶ Q := Over.homMk π₀ hπq
  have : Flat π.left := hπflat
  have : Surjective π.left := hπsurj
  have : LocallyOfFinitePresentation π.left := hπlfp
  have hpb' : IsPullback s t π π := IsPullback.of_map_of_faithful (F := Over.forget _) hpb
  obtain ⟨e, he⟩ := QuasiAffineApproximation.exists_fac_of_kernelPair π hpb' ζ hst
  exact ⟨Q, π, e, hQ, he, fun T _ => ⟨injective_app huniq he hpb'.w T,
    surjective_app huniq he hpb'.w hζ T⟩, hπflat, hπsurj, hπprop, hπlfp⟩

end Main

end Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReduction
