import Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibrePower
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Fibre powers of affine charts of separated algebraic spaces are affine

Let `X` be an algebraic space over an affine scheme `S` whose diagonal is a representable
closed immersion, and let `a : h_V → X` be a chart from an affine scheme `V`. Every finite fibre
power `V ×_X ⋯ ×_X V` constructed in `ChartFibrePower` is affine. The new factor of the
recursive construction is the locus in `P ×_S V` where two maps to `X` agree, a closed
subscheme of an affine scheme.
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ChartFibrePower

variable {S : Scheme.{u}} {X : Presheaf S} {V : Over S} {a : (schemeYoneda S).obj V ⟶ X}

/-- A morphism of represented presheaves corresponds to a section. -/
theorem map_uliftYonedaEquiv {T U : Over S} (g : T ⟶ U) (α : (schemeYoneda S).obj U ⟶ X) :
    X.map g.op (uliftYonedaEquiv α) = uliftYonedaEquiv ((schemeYoneda S).map g ≫ α) :=
  uliftYonedaEquiv_naturality α g.op

/-- **Affine new factor.** If the diagonal of `X` is a representable closed immersion and the
schemes `S`, `V` and `P` are affine, the next fibre power is affine. -/
theorem succ_isAffine (hX : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).relative
        (schemeYoneda S) (diag X))
    (ha : (schemeYoneda S).relativelyRepresentable a) {n : ℕ}
    (P : ChartFibrePower a (Fin (n + 1))) [IsAffine S] [IsAffine V.left] [IsAffine P.obj.left] :
    IsAffine (succ ha P).obj.left := by
  let U : Over S := Over.mk (Limits.pullback.fst P.obj.hom V.hom ≫ P.obj.hom)
  have : IsAffine U.left := inferInstanceAs (IsAffine (Limits.pullback P.obj.hom V.hom))
  let πP : U ⟶ P.obj := Over.homMk (Limits.pullback.fst P.obj.hom V.hom) rfl
  let πV : U ⟶ V := Over.homMk (Limits.pullback.snd P.obj.hom V.hom) (Limits.pullback.condition).symm
  obtain ⟨Z, j, hj, hcl⟩ := exists_representsEqualizer_of_relative_diag hX
    (uliftYonedaEquiv ((schemeYoneda S).map πP ≫ P.toBase))
    (uliftYonedaEquiv ((schemeYoneda S).map πV ≫ a))
  have hZ : IsAffine Z.left := by
    have : IsAffineHom j.left := inferInstance
    exact isAffine_of_isAffineHom j.left
  have hjmono : Mono j := by
    have : Mono j.left := inferInstance
    exact Over.mono_of_mono_left _
  -- the map from the new factor to `P ×_S V`
  let m : (succObj ha P) ⟶ U := Over.homMk
    (Limits.pullback.lift (succSnd ha P).left (succFst ha P).left
      ((Over.w (succSnd ha P)).trans (Over.w (succFst ha P)).symm))
    (by
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ ≫ P.obj.hom = _
      rw [Limits.pullback.lift_fst_assoc]
      exact Over.w (succSnd ha P))
  have hmP : m ≫ πP = succSnd ha P := Over.OverMorphism.ext (Limits.pullback.lift_fst _ _ _)
  have hmV : m ≫ πV = succFst ha P := Over.OverMorphism.ext (Limits.pullback.lift_snd _ _ _)
  have hme : (schemeYoneda S).map m ≫ (schemeYoneda S).map πP ≫ P.toBase =
      (schemeYoneda S).map m ≫ (schemeYoneda S).map πV ≫ a := by
    rw [← (schemeYoneda S).map_comp_assoc m πP, ← (schemeYoneda S).map_comp_assoc m πV, hmP, hmV]
    exact (succ_isPullback ha P).w.symm
  obtain ⟨r, hr⟩ := (hj m).2 (by
    rw [map_uliftYonedaEquiv, map_uliftYonedaEquiv]
    exact congrArg uliftYonedaEquiv hme)
  have hjeq : (schemeYoneda S).map (j ≫ πV) ≫ a =
      (schemeYoneda S).map (j ≫ πP) ≫ P.toBase := by
    have h := (hj j).1 ⟨𝟙 _, Category.id_comp _⟩
    rw [map_uliftYonedaEquiv, map_uliftYonedaEquiv] at h
    rw [(schemeYoneda S).map_comp_assoc, (schemeYoneda S).map_comp_assoc]
    exact (uliftYonedaEquiv.injective h).symm
  let s : Z ⟶ succObj ha P := Functor.relativelyRepresentable.lift' ha (j ≫ πV) (j ≫ πP) hjeq
  have hsm : s ≫ m = j := by
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · change (s ≫ m ≫ πP).left = (j ≫ πP).left
      rw [hmP]
      exact congrArg CommaMorphism.left (Functor.relativelyRepresentable.lift'_snd _ _ _ _)
    · change (s ≫ m ≫ πV).left = (j ≫ πV).left
      rw [hmV]
      exact congrArg CommaMorphism.left (Functor.relativelyRepresentable.lift'_fst _ _ _ _)
  have hrs : r ≫ s = 𝟙 _ := by
    apply Functor.relativelyRepresentable.hom_ext' ha
    · rw [Category.assoc, Functor.relativelyRepresentable.lift'_fst, ← Category.assoc, hr, hmV,
        Category.id_comp]
    · rw [Category.assoc, Functor.relativelyRepresentable.lift'_snd, ← Category.assoc, hr, hmP,
        Category.id_comp]
  have hsr : s ≫ r = 𝟙 _ := by
    rw [← cancel_mono j, Category.assoc, hr, hsm, Category.id_comp]
  let e : succObj ha P ≅ Z := ⟨r, s, hrs, hsr⟩
  exact @IsAffine.of_isIso _ _ ((Over.forget S).mapIso e).hom (Iso.isIso_hom _) hZ

/-- All fibre powers `fin` of an affine étale chart of a space with closed-immersion diagonal are
affine. -/
theorem fin_isAffine (hX : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).relative
        (schemeYoneda S) (diag X))
    (ha : (schemeYoneda S).relativelyRepresentable a) [IsAffine S] [IsAffine V.left] :
    ∀ n : ℕ, IsAffine (fin ha n).obj.left
  | 0 => inferInstanceAs (IsAffine V.left)
  | n + 1 => by
    have := fin_isAffine hX ha n
    exact succ_isAffine hX ha (fin ha n)

/-- **Affine fibre powers.** Every finite nonempty index type has a separated affine fibre
power with étale projections, for an affine étale chart of a space whose diagonal is a
representable closed immersion over an affine base. -/
theorem exists_of_finite_affine (hX : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).relative
        (schemeYoneda S) (diag X))
    (ha : IsEtale a) [IsSeparated V.hom] [IsAffine S] [IsAffine V.left] (ι : Type v) [Finite ι]
    [Nonempty ι] : ∃ P : ChartFibrePower a ι, IsSeparated P.obj.hom ∧
      (∀ i, Etale (P.pr i).left) ∧ IsAffine P.obj.left := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain _ | n := n
  · exact (IsEmpty.false (e (Classical.arbitrary ι))).elim
  obtain ⟨h₁, h₂⟩ := fin_properties ha n
  exact ⟨(fin ha.1 n).reindex e, h₁, fun i => h₂ (e i), fin_isAffine hX ha.1 n⟩

end ChartFibrePower

end Langlands.AlgebraicGeometry.AlgebraicSpace
