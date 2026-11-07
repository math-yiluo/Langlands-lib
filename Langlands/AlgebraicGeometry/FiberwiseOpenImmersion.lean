import Langlands.AlgebraicGeometry.FiberwiseFlatness
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # The fibrewise criterion for open immersions -/

universe u

open CategoryTheory Limits

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

namespace FiberwiseOpenImmersion

variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)

/-- Pulling back to a residue field carries the diagonal of `f` to the diagonal of the
fibre of `f`, up to the pullback comparison map. -/
lemma pullback_map_diagonal (s : S) :
    (Over.pullback (S.fromSpecResidueField s)).map (pullback.diagonal f) ≫
        pullbackComparison (Over.pullback (S.fromSpecResidueField s)) f f =
      pullback.diagonal ((Over.pullback (S.fromSpecResidueField s)).map f) := by
  apply pullback.hom_ext <;>
    simp [← Functor.map_comp]

/-- If the fibre of `f` at `s` is a monomorphism, the fibre of the diagonal of `f` at `s` is
an isomorphism. -/
lemma isIso_pullback_map_diagonal (s : S)
    [Mono ((Over.pullback (S.fromSpecResidueField s)).map f).left] :
    IsIso ((Over.pullback (S.fromSpecResidueField s)).map (pullback.diagonal f)) := by
  have : Mono ((Over.pullback (S.fromSpecResidueField s)).map f) :=
    Over.mono_of_mono_left _
  have : IsIso (pullback.diagonal ((Over.pullback (S.fromSpecResidueField s)).map f)) :=
    (pullback.isIso_diagonal_iff _).mpr inferInstance
  have h := pullback_map_diagonal f s
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

/-- The structure map of the self-fibre product of `f` is locally of finite presentation when
`X` is and `Y` is locally of finite type. -/
lemma locallyOfFinitePresentation_pullback_hom [LocallyOfFinitePresentation X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFinitePresentation (pullback f f).hom := by
  have : LocallyOfFinitePresentation f.left :=
    have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    locallyOfFinitePresentation_of_comp f.left Y.hom
  have hP : IsPullback (pullback.fst f f).left (pullback.snd f f).left f.left f.left :=
    (IsPullback.of_hasPullback f f).map (Over.forget S)
  have : LocallyOfFinitePresentation (pullback.fst f f).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hP.flip inferInstance
  rw [← Over.w (pullback.fst f f)]
  infer_instance

end FiberwiseOpenImmersion

open FiberwiseOpenImmersion in
/-- The fibrewise criterion for open immersions: let `X` be flat and locally of finite
presentation over `S` and `Y` locally of finite type over `S`. A morphism `f : X ⟶ Y` over `S`
whose fibre over every residue field of `S` is an open immersion is an open immersion. -/
theorem isOpenImmersion_of_fiberwise {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (hf : ∀ s : S, IsOpenImmersion ((Over.pullback (S.fromSpecResidueField s)).map f).left) :
    IsOpenImmersion f.left := by
  have : LocallyOfFinitePresentation f.left :=
    have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    locallyOfFinitePresentation_of_comp f.left Y.hom
  have hflat : Flat f.left :=
    fiberwiseFlatness S X Y f inferInstance inferInstance inferInstance fun s => by
      have := hf s
      infer_instance
  -- The diagonal of `f` is flat, by the fibrewise flatness criterion over `S`.
  let Δ : X ⟶ pullback f f := pullback.diagonal f
  have : LocallyOfFinitePresentation (pullback f f).hom :=
    locallyOfFinitePresentation_pullback_hom f
  have hΔfib : ∀ s : S, IsIso ((Over.pullback (S.fromSpecResidueField s)).map Δ).left := by
    intro s
    have := hf s
    have := isIso_pullback_map_diagonal f s
    exact Functor.map_isIso (Over.forget (Spec (S.residueField s)))
      ((Over.pullback (S.fromSpecResidueField s)).map Δ)
  have hΔflat : Flat Δ.left :=
    fiberwiseFlatness S X (pullback f f) Δ inferInstance inferInstance inferInstance fun s => by
      have := hΔfib s
      infer_instance
  have hΔlfp : LocallyOfFinitePresentation Δ.left :=
    have : LocallyOfFinitePresentation (Δ.left ≫ (pullback f f).hom) := by
      rw [Over.w Δ]; infer_instance
    locallyOfFinitePresentation_of_comp Δ.left (pullback f f).hom
  have hΔmono : Mono Δ.left := by
    have h : Δ.left ≫ (pullback.fst f f).left = 𝟙 X.left := by
      rw [← Over.comp_left, pullback.diagonal_fst, Over.id_left]
    exact mono_of_mono_fac h
  have hΔopen : IsOpenImmersion Δ.left := IsOpenImmersion.of_flat_of_mono Δ.left
  -- The diagonal is surjective, since it is so on every fibre.
  have hΔsurj : Surjective Δ.left := by
    refine ⟨fun w => ?_⟩
    let s : S := (pullback f f).hom w
    obtain ⟨w', hw', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (pullback f f).hom) (g := S.fromSpecResidueField s) w
      (IsLocalRing.closedPoint (S.residueField s)) (Scheme.fromSpecResidueField_apply _ _).symm
    have := hΔfib s
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (S.fromSpecResidueField s)).map Δ).left).surjective w'
    have key : pullback.fst X.hom (S.fromSpecResidueField s) ≫ Δ.left =
        ((Over.pullback (S.fromSpecResidueField s)).map Δ).left ≫
          pullback.fst (pullback f f).hom (S.fromSpecResidueField s) := by
      exact (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst X.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hw', ← hx', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, key]
  have : IsIso Δ.left := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hΔopen, hΔsurj⟩
  have : IsIso ((Over.forget S).map Δ) := ‹IsIso Δ.left›
  have : IsIso Δ := isIso_of_reflects_iso Δ (Over.forget S)
  have : Mono f := (pullback.isIso_diagonal_iff _).mp this
  exact IsOpenImmersion.of_flat_of_mono f.left

end Langlands.AlgebraicGeometry
