import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentBridge
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit

/-! # Descent of line bundles along direct limits and to finitely presented quotients

The ported FLT theorem
`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`
descends line bundles along an arbitrary directed system of rings with a direct limit. Here it is
put in pullback-square form for directed systems of `A₀`-algebras, and applied to the system of
quotients `D ⧸ J` of an `A₀`-algebra `D` by the finitely generated ideals `J` contained in a given
ideal `I`, whose direct limit is `D ⧸ I`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard

/-- Let `A` be the direct limit of a directed system `G` of `A₀`-algebras. A locally free
rank-one module on a base change `X` to `Spec A` of a quasi-compact, quasi-separated scheme `X₀`
over `Spec A₀` comes, up to isomorphism, from a locally free rank-one module on the chosen base
change of `X₀` to `Spec (G j)` for some index `j`, along every morphism compatible with both
projections. -/
theorem exists_lineBundle_descent_of_isDirectLimit {A₀ : Type u} [CommRing A₀]
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] [∀ i, Algebra A₀ (G i)]
    (φ : ∀ i j : ι, i ≤ j → G i →+* G j) [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {A : Type u} [CommRing A] [Algebra A₀ A] (g : ∀ i, G i →+* A)
    (hA : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (hφ : ∀ i j (h : i ≤ j), (φ i j h).comp (algebraMap A₀ (G i)) = algebraMap A₀ (G j))
    (hg : ∀ i, (g i).comp (algebraMap A₀ (G i)) = algebraMap A₀ A)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f₀]
    [QuasiSeparated f₀] {X : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ Spec (CommRingCat.of A))
    (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (M : X.Modules) (hM : IsLocallyFreeRankOne M) :
    ∃ (j : ι) (M₀ : (pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (G j))))).Modules),
      IsLocallyFreeRankOne M₀ ∧
      ∀ c : X ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (G j)))),
        c ≫ pullback.fst _ _ = a →
        c ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (g j)) →
        Nonempty ((Scheme.Modules.pullback c).obj M₀ ≅ M) := by
  have spec_g : ∀ i, Spec.map (CommRingCat.ofHom (g i)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₀ (G i))) =
        Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := fun i ↦ by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  have spec_φ : ∀ i j (h : i ≤ j), Spec.map (CommRingCat.ofHom (φ i j h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₀ (G i))) =
        Spec.map (CommRingCat.ofHom (algebraMap A₀ (G j))) := fun i j h ↦ by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have spec_gφ : ∀ i j (h : i ≤ j), Spec.map (CommRingCat.ofHom (g j)) ≫
      Spec.map (CommRingCat.ofHom (φ i j h)) = Spec.map (CommRingCat.ofHom (g i)) :=
    fun i j h ↦ by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact hA.compatibility i j h x
  let i : ι := Classical.arbitrary ι
  let ι₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ (G i)))
  -- `e : P ⟶ X` from the base change `P` of `X₀ ×_{A₀} Spec (G i)` to `Spec A`, and a section.
  have hw : (pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) ≫
      pullback.fst f₀ ι₀) ≫ f₀ =
      pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, spec_g]
  obtain ⟨e, he₁, he₂⟩ : ∃ e : pullback (pullback.snd f₀ ι₀)
      (Spec.map (CommRingCat.ofHom (g i))) ⟶ X,
      e ≫ a = pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) ≫
        pullback.fst f₀ ι₀ ∧
      e ≫ f = pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) :=
    ⟨hpb.lift _ _ hw, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have hw' : a ≫ f₀ = (f ≫ Spec.map (CommRingCat.ofHom (g i))) ≫ ι₀ := by
    rw [hpb.w, Category.assoc, spec_g]
  obtain ⟨e', he'₁, he'₂⟩ : ∃ e' : X ⟶ pullback (pullback.snd f₀ ι₀)
      (Spec.map (CommRingCat.ofHom (g i))),
      e' ≫ pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) =
        pullback.lift a (f ≫ Spec.map (CommRingCat.ofHom (g i))) hw' ∧
      e' ≫ pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) = f :=
    ⟨pullback.lift _ f (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have he : e' ≫ e = 𝟙 X := by
    apply hpb.hom_ext
    · rw [Category.assoc, he₁, ← Category.assoc, he'₁, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, he₂, he'₂, Category.id_comp]
  -- Descend the pullback of `M` along `e` to a stage `j`.
  obtain ⟨j, hij, Lj, hLj, hj⟩ :=
    Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
      φ g hA i (pullback.snd f₀ ι₀) ((Scheme.Modules.pullback e).obj M)
      ((isInvertible_of_isLocallyFreeRankOne hM).pullback e)
  -- `u` from the chosen base change of `X₀` to `Spec (G j)` to the base change of
  -- `X₀ ×_{A₀} Spec (G i)`.
  have hu : pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (G j)))) ≫ f₀ =
      (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (G j)))) ≫
        Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ ι₀ := by
    rw [pullback.condition, Category.assoc, spec_φ]
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u : pullback f₀
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ (G j)))) ⟶
      pullback (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (φ i j hij))),
      u ≫ pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (φ i j hij))) =
        pullback.lift _ _ hu ∧
      u ≫ pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (φ i j hij))) =
        pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (G j)))) :=
    ⟨pullback.lift _ _ (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  refine ⟨j, (Scheme.Modules.pullback u).obj Lj,
    isLocallyFreeRankOne_of_isInvertible (hLj.pullback u), ?_⟩
  intro c hc₁ hc₂
  have h₁ : (e ≫ c ≫ u) ≫
      pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (φ i j hij))) =
      pullback.fst (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, reassoc_of% hu₁, pullback.lift_fst]
      rw [hc₁, he₁]
    · simp only [Category.assoc, reassoc_of% hu₁, pullback.lift_snd]
      rw [← Category.assoc c, hc₂]
      simp only [Category.assoc]
      rw [← Category.assoc e, he₂, spec_gφ]
      exact pullback.condition.symm
  have h₂ : (e ≫ c ≫ u) ≫
      pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (φ i j hij))) =
      pullback.snd (pullback.snd f₀ ι₀) (Spec.map (CommRingCat.ofHom (g i))) ≫
        Spec.map (CommRingCat.ofHom (g j)) := by
    simp only [Category.assoc, hu₂]
    rw [hc₂, ← Category.assoc, he₂]
  obtain ⟨ψ⟩ := nonempty_iso_pullback_of_section he (c ≫ u) (hj (e ≫ c ≫ u) h₁ h₂)
  exact ⟨(Scheme.Modules.pullbackComp c u).app Lj ≪≫ ψ⟩

section Quotient

variable {D : Type u} [CommRing D]

/-- The finitely generated ideals of `D` contained in the ideal `I`, ordered by inclusion. -/
abbrev FGQuotIndex (I : Ideal D) : Type u :=
  {J : Ideal D // J.FG ∧ J ≤ I}

variable {I : Ideal D}

/-- The ring at an index: the quotient by the finitely generated ideal. -/
abbrev FGQuotStage (J : FGQuotIndex I) : Type u :=
  D ⧸ J.1

instance FGQuotIndex.instNonempty : Nonempty (FGQuotIndex I) :=
  ⟨⟨⊥, Submodule.fg_bot, bot_le⟩⟩

instance FGQuotIndex.instIsDirected : IsDirected (FGQuotIndex I) (· ≤ ·) :=
  ⟨fun S T => ⟨⟨S.1 ⊔ T.1, Submodule.FG.sup S.2.1 T.2.1, sup_le S.2.2 T.2.2⟩,
    (le_sup_left : S.1 ≤ S.1 ⊔ T.1), (le_sup_right : T.1 ≤ S.1 ⊔ T.1)⟩⟩

/-- The quotient map between the stages of two comparable finitely generated ideals. -/
def quotTransition (S T : FGQuotIndex I) (h : S ≤ T) : FGQuotStage S →+* FGQuotStage T :=
  Ideal.Quotient.factor (show S.1 ≤ T.1 from h)

/-- The quotient map from a stage to `D ⧸ I`. -/
def quotToLimit (T : FGQuotIndex I) : FGQuotStage T →+* D ⧸ I :=
  Ideal.Quotient.factor T.2.2

instance quotDirectedSystem :
    DirectedSystem (FGQuotStage (I := I)) fun S T h => ⇑(quotTransition S T h) where
  map_self _ x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_map _ _ _ _ _ x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- `D ⧸ I` is the direct limit of the quotients of `D` by the finitely generated ideals
contained in `I`. -/
theorem quotIsDirectLimit :
    IsDirectLimit (fun S T h => ⇑(quotTransition (I := I) S T h))
      fun T => ⇑(quotToLimit T) where
  surj m := by
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective m
    exact ⟨⟨⊥, Submodule.fg_bot, bot_le⟩, Ideal.Quotient.mk _ d, rfl⟩
  inj S T x y h := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hxy : x - y ∈ I := Ideal.Quotient.eq.mp h
    refine ⟨⟨S.1 ⊔ T.1 ⊔ Ideal.span {x - y}, Submodule.FG.sup (Submodule.FG.sup S.2.1 T.2.1)
      (Submodule.fg_span_singleton _),
      sup_le (sup_le S.2.2 T.2.2) ((Ideal.span_singleton_le_iff_mem _).mpr hxy)⟩,
      (le_sup_left.trans le_sup_left : S.1 ≤ S.1 ⊔ T.1 ⊔ Ideal.span {x - y}),
      (le_sup_right.trans le_sup_left : T.1 ≤ S.1 ⊔ T.1 ⊔ Ideal.span {x - y}), ?_⟩
    change Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ y
    exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  compatibility _ _ _ x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

variable {A₀ : Type u} [CommRing A₀] [Algebra A₀ D]

/-- A locally free rank-one module on a base change `X` to `Spec (D ⧸ I)` of a quasi-compact,
quasi-separated scheme `X₀` over `Spec A₀` comes, up to isomorphism, from a locally free rank-one
module on the chosen base change of `X₀` to `Spec (D ⧸ J)`, for a finitely generated ideal
`J ≤ I`, along every morphism compatible with both projections. -/
theorem exists_lineBundle_quotient_descent (I : Ideal D)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f₀]
    [QuasiSeparated f₀] {X : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ Spec (CommRingCat.of (D ⧸ I)))
    (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (D ⧸ I)))))
    (M : X.Modules) (hM : IsLocallyFreeRankOne M) :
    ∃ (J : Ideal D) (_ : J.FG) (hJ : J ≤ I)
      (M₀ : (pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (D ⧸ J))))).Modules),
      IsLocallyFreeRankOne M₀ ∧
      ∀ c : X ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (D ⧸ J)))),
        c ≫ pullback.fst _ _ = a →
        c ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)) →
        Nonempty ((Scheme.Modules.pullback c).obj M₀ ≅ M) := by
  obtain ⟨J, M₀, hM₀, hJ⟩ := exists_lineBundle_descent_of_isDirectLimit (A₀ := A₀)
    (G := FGQuotStage (I := I)) quotTransition quotToLimit quotIsDirectLimit
    (fun _ _ _ ↦ RingHom.ext fun _ ↦ rfl) (fun _ ↦ RingHom.ext fun _ ↦ rfl) f₀ a f hpb M hM
  exact ⟨J.1, J.2.1, J.2.2, M₀, hM₀, hJ⟩

end Quotient

end Langlands.AlgebraicGeometry.NoetherianApproximation
