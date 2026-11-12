import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount

/-! # Fibre products of schemes over an algebraic space

For maps `a : h_U ⟶ X` and `b : h_V ⟶ X` from schemes over `S` to an algebraic space `X`, the
fibre product `U ×_X V` is represented by a scheme over `S`. When `X` is separated, the pairing
`U ×_X V ⟶ U ×_S V` of the two projections is a closed immersion.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
  (a : (schemeYoneda S).obj U ⟶ X.presheaf) (b : (schemeYoneda S).obj V ⟶ X.presheaf)

/-- The scheme `U ×_X V` over `S` representing the fibre product of `a` and `b`. -/
abbrev spacePullback : Over S := (X.representable_from_scheme a).pullback b

/-- The projection `U ×_X V ⟶ U`. -/
abbrev spacePullbackFst : spacePullback a b ⟶ U :=
  Functor.relativelyRepresentable.fst' (X.representable_from_scheme a) b

/-- The projection `U ×_X V ⟶ V`. -/
abbrev spacePullbackSnd : spacePullback a b ⟶ V := (X.representable_from_scheme a).snd b

theorem spacePullback_isPullback :
    IsPullback ((schemeYoneda S).map (spacePullbackFst a b))
      ((schemeYoneda S).map (spacePullbackSnd a b)) a b :=
  Functor.relativelyRepresentable.isPullback' _ b

theorem spacePullback_w :
    (schemeYoneda S).map (spacePullbackFst a b) ≫ a =
      (schemeYoneda S).map (spacePullbackSnd a b) ≫ b :=
  (spacePullback_isPullback a b).w

variable {a b}

/-- The point of `U ×_X V` given by points of `U` and `V` with the same image in `X`. -/
abbrev spacePullbackLift {T : Over S} (y₁ : T ⟶ U) (y₂ : T ⟶ V)
    (h : (schemeYoneda S).map y₁ ≫ a = (schemeYoneda S).map y₂ ≫ b) : T ⟶ spacePullback a b :=
  Functor.relativelyRepresentable.lift' (X.representable_from_scheme a) y₁ y₂ h

@[reassoc (attr := simp)]
theorem spacePullbackLift_fst {T : Over S} (y₁ : T ⟶ U) (y₂ : T ⟶ V)
    (h : (schemeYoneda S).map y₁ ≫ a = (schemeYoneda S).map y₂ ≫ b) :
    spacePullbackLift y₁ y₂ h ≫ spacePullbackFst a b = y₁ :=
  Functor.relativelyRepresentable.lift'_fst _ _ _ _

@[reassoc (attr := simp)]
theorem spacePullbackLift_snd {T : Over S} (y₁ : T ⟶ U) (y₂ : T ⟶ V)
    (h : (schemeYoneda S).map y₁ ≫ a = (schemeYoneda S).map y₂ ≫ b) :
    spacePullbackLift y₁ y₂ h ≫ spacePullbackSnd a b = y₂ :=
  Functor.relativelyRepresentable.lift'_snd _ _ _ _

theorem spacePullback_hom_ext {T : Over S} {f g : T ⟶ spacePullback a b}
    (h₁ : f ≫ spacePullbackFst a b = g ≫ spacePullbackFst a b)
    (h₂ : f ≫ spacePullbackSnd a b = g ≫ spacePullbackSnd a b) : f = g :=
  Functor.relativelyRepresentable.hom_ext' _ h₁ h₂

variable (a b)

/-- If the diagonal of `X` is representable with projections in a property `P` of
monomorphisms respecting isomorphisms, the pairing `U ×_X V ⟶ U ×_S V` of the two projections
is in `P`. -/
theorem spacePullbackLift_mem_of_relative_diag (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (hmono : ∀ ⦃A B : Scheme.{u}⦄ (f : A ⟶ B), P f → Mono f)
    (hX : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
      (diag X.presheaf)) :
    P (lift (spacePullbackFst a b) (spacePullbackSnd a b)).left := by
  obtain ⟨Z, ι, hι, himm⟩ := exists_representsEqualizer_of_relative_diag hX
    (uliftYonedaEquiv.{u + 1} ((schemeYoneda S).map (fst U V) ≫ a))
    (uliftYonedaEquiv.{u + 1} ((schemeYoneda S).map (snd U V) ≫ b))
  have : Mono ι.left := hmono _ himm
  have : Mono ι := Over.mono_of_mono_left ι
  obtain ⟨φ, hφ⟩ : ∃ φ : spacePullback a b ⟶ Z,
      φ ≫ ι = lift (spacePullbackFst a b) (spacePullbackSnd a b) := by
    apply (hι _).2
    rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
    congr 1
    simp only [Quiver.Hom.unop_op, ← Functor.map_comp_assoc, lift_fst, lift_snd]
    exact (spacePullback_isPullback a b).w
  have hw : (schemeYoneda S).map (ι ≫ fst U V) ≫ a =
      (schemeYoneda S).map (ι ≫ snd U V) ≫ b := by
    have := (hι ι).1 ⟨𝟙 _, Category.id_comp _⟩
    rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality] at this
    simpa [Functor.map_comp_assoc] using uliftYonedaEquiv.injective this
  let ψ : Z ⟶ spacePullback a b := spacePullbackLift _ _ hw
  have hψ₁ : ψ ≫ spacePullbackFst a b = ι ≫ fst U V := spacePullbackLift_fst _ _ _
  have hψ₂ : ψ ≫ spacePullbackSnd a b = ι ≫ snd U V := spacePullbackLift_snd _ _ _
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply spacePullback_hom_ext
    · rw [Category.assoc, hψ₁, reassoc_of% hφ, lift_fst, Category.id_comp]
    · rw [Category.assoc, hψ₂, reassoc_of% hφ, lift_snd, Category.id_comp]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono ι, Category.assoc, hφ, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, hψ₁]
    · rw [Category.assoc, lift_snd, hψ₂]
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have : IsIso φ.left := (Over.forget _).map_isIso φ
  rw [← hφ, Over.comp_left]
  exact (MorphismProperty.cancel_left_of_respectsIso P φ.left ι.left).mpr himm

/-- **Fibre products are closed in products**: if `X` is separated, the pairing
`U ×_X V ⟶ U ×_S V` of the two projections is a closed immersion. -/
theorem isClosedImmersion_spacePullbackLift (hX : IsSeparated X) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (lift (spacePullbackFst a b) (spacePullbackSnd a b)).left :=
  spacePullbackLift_mem_of_relative_diag a b @_root_.AlgebraicGeometry.IsClosedImmersion
    (fun _ _ _ _ => inferInstance) hX

theorem etale_spacePullbackFst (hb : IsEtale b) : Etale (spacePullbackFst a b).left :=
  hb.projection a _ _ (spacePullback_isPullback a b).flip

theorem etale_spacePullbackSnd (ha : IsEtale a) : Etale (spacePullbackSnd a b).left :=
  ha.projection b _ _ (spacePullback_isPullback a b)

theorem surjective_spacePullbackFst (hb : IsSurjective b) :
    Surjective (spacePullbackFst a b).left :=
  hb.projection a _ _ (spacePullback_isPullback a b).flip

theorem surjective_spacePullbackSnd (ha : IsSurjective a) :
    Surjective (spacePullbackSnd a b).left :=
  ha.projection b _ _ (spacePullback_isPullback a b)

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
