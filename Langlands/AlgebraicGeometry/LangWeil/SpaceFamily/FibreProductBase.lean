import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.SchemeBase
import Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibreProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointTopologyIso
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective

/-!
# The uniform Lang–Weil estimate over a scheme chart of the base

Let `f : Y → B` be a separated, quasi-compact, surjective morphism of algebraic spaces over
`Spec ℤ` with geometrically connected fibres and an étale chart square `a : U → Y`,
`b : V → B`, `φ : U → V` with `φ` smooth of relative dimension `d`. For an affine scheme `M`
locally of finite type over `ℤ` and any morphism `t : M → B`, the fibre product
`X = Y ×_B M` is a separated algebraic space (`ChartFibre.space`) whose projection
`g : X → M` satisfies the hypotheses of `uniformLangWeil_schemeBase`:

* `X` has an affine étale surjective chart `O → X` lying over a morphism `π : O → M` that is
  smooth of relative dimension `d` (the chart `U ×_V (V ×_B M)` refined by finitely many affine
  opens over a quasi-compact chart of `X`);
* `π` is surjective, since `f` is;
* the points of every fibre of `g` over a field point of `M` form a connected space, since
  these fibres are fibres of `f`.

Assuming the uniform Lang–Weil estimate and the uniform upper bound in families of schemes,
the number of `κ`-points of `Y` over the `κ`-point `t ∘ m` of `B`, for `m` a `κ`-point of `M`,
therefore differs from `(#κ) ^ d` by at most `C (#κ) ^ (d - 1/2)`, with one constant `C`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- An étale surjective chart of a presheaf `F` lying over a morphism `π : O → M` hits every
point of `M` over which `F` has a point. -/
theorem surjective_of_exists_point {F : Presheaf S0.{u}} {M : Scheme.{u}}
    (g : F ⟶ (schemeYoneda S0).obj (toOver M)) {O : Over S0.{u}}
    (aO : (schemeYoneda S0).obj O ⟶ F) (hs : IsSurjective aO) (π : O.left ⟶ M)
    (hg : aO ≫ g = (schemeYoneda S0).map (overHom π))
    (hpt : ∀ y : M, ∃ (T : Over S0.{u}) (z : (schemeYoneda S0).obj T ⟶ F) (s : T.left ⟶ M)
      (τ : T.left), z ≫ g = (schemeYoneda S0).map (overHom s) ∧ s τ = y) :
    Function.Surjective π := by
  intro y
  obtain ⟨T, z, s, τ, hz, hτ⟩ := hpt y
  obtain ⟨o, ho⟩ := surjective_chartPointMap aO hs (chartPointMap z τ)
  obtain ⟨T', g₁, g₂, τ', hg₁₂, h₁, h₂⟩ := (chartPointMap_eq_iff_sameImage₂ aO z o τ).mp ho
  have h : g₁ ≫ overHom π = g₂ ≫ overHom s := by
    apply (schemeYoneda S0).map_injective
    rw [Functor.map_comp, Functor.map_comp, ← hg, ← hz, ← Category.assoc, hg₁₂,
      Category.assoc]
  have h' := congrArg (fun φ => φ.left τ') h
  simp only [Over.comp_left, overHom_left, Scheme.Hom.comp_apply] at h'
  subst h₁ h₂ hτ
  exact ⟨g₁.left τ', h'⟩

/-- Refining an étale surjective chart `P → F` smooth of relative dimension `d` over `M` by
finitely many affine opens over a quasi-compact étale surjective chart `Q → F` gives an affine
étale surjective chart, still smooth of relative dimension `d` over `M`. -/
theorem exists_affine_chart {F : Presheaf S0.{u}} {M : Scheme.{u}}
    (g : F ⟶ (schemeYoneda S0).obj (toOver M)) {P : Scheme.{u}}
    (aP : (schemeYoneda S0).obj (toOver P) ⟶ F) (π : P ⟶ M)
    (haPe : IsEtale aP) (haPs : IsSurjective aP) {d : ℕ} [SmoothOfRelativeDimension d π]
    (hg : aP ≫ g = (schemeYoneda S0).map (toOverHom π))
    {Q : Over S0.{u}} [CompactSpace Q.left] (aQ : (schemeYoneda S0).obj Q ⟶ F)
    (haQe : IsEtale aQ) (haQs : IsSurjective aQ) :
    ∃ (O : Scheme.{u}) (aO : (schemeYoneda S0).obj (toOver O) ⟶ F) (πO : O ⟶ M),
      IsAffine O ∧ IsEtale aO ∧ IsSurjective aO ∧ SmoothOfRelativeDimension d πO ∧
        aO ≫ g = (schemeYoneda S0).map (toOverHom πO) := by
  have hr : IsRepresentableMorphism aP := haPe.representable
  let W : Over S0.{u} := hr.pullback aQ
  let wP : W ⟶ toOver P := Functor.relativelyRepresentable.fst' hr aQ
  let wQ : W ⟶ Q := hr.snd aQ
  have hW : IsPullback ((schemeYoneda S0).map wP) ((schemeYoneda S0).map wQ) aP aQ :=
    Functor.relativelyRepresentable.isPullback' hr aQ
  have hwQe : Etale wQ.left := haPe.projection aQ _ wQ hW
  have hwQs : Surjective wQ.left := haPs.projection aQ _ wQ hW
  have hwPe : Etale wP.left := haQe.projection aP _ wP hW.flip
  let 𝒰 := W.left.affineCover
  have hopen : ∀ i, IsOpen (Set.range (𝒰.f i ≫ wQ.left)) := fun i =>
    (𝒰.f i ≫ wQ.left).isOpenMap.isOpen_range
  have hcover : Set.univ ⊆ ⋃ i, Set.range (𝒰.f i ≫ wQ.left) := by
    intro q _
    obtain ⟨w, rfl⟩ := hwQs.surj q
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq w
    exact Set.mem_iUnion.mpr ⟨i, x, by rw [Scheme.Hom.comp_apply]⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  let Xs : s → Scheme.{u} := fun i => 𝒰.X i.1
  have : ∀ i, IsAffine (Xs i) := fun i => inferInstanceAs (IsAffine (𝒰.X i.1))
  let J : ∐ Xs ⟶ W.left := Sigma.desc fun i => 𝒰.f i.1
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hJ : Etale J := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  have hJs : Function.Surjective (J ≫ wQ.left) := by
    intro q
    have hq := hs (Set.mem_univ q)
    simp only [Set.mem_iUnion] at hq
    obtain ⟨i, hi, x, hx⟩ := hq
    refine ⟨Sigma.ι Xs ⟨i, hi⟩ x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Sigma.ι_comp_desc]
    exact hx
  have hπ1 : SmoothOfRelativeDimension d (wP.left ≫ π) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + d) (wP.left ≫ π))
    rwa [Nat.zero_add] at h
  have hπ2 : SmoothOfRelativeDimension d (J ≫ wP.left ≫ π) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + d) (J ≫ wP.left ≫ π))
    rwa [Nat.zero_add] at h
  refine ⟨∐ Xs, (schemeYoneda S0).map (homOver (Y := W) J) ≫ (schemeYoneda S0).map wP ≫ aP,
    J ≫ wP.left ≫ π, inferInstance, ?_, ?_, hπ2, ?_⟩
  · exact (isEtale_map _ hJ).comp ((isEtale_map _ hwPe).comp haPe)
  · rw [hW.w, ← Category.assoc, ← Functor.map_comp]
    exact SpaceProductPoints.IsSurjective.comp
      (SpaceProductPoints.isSurjective_map _ ⟨hJs⟩) haQs
  · rw [Category.assoc, Category.assoc, hg, ← Functor.map_comp, ← Functor.map_comp]
    congr 1

section FibreProduct

variable {B Y : AlgebraicSpace S0.{u}} (f : Y ⟶ B) {M : Scheme.{u}}
  (t : (schemeYoneda S0).obj (toOver M) ⟶ B.presheaf)

/-- The fibre product `Y ×_B M` has an étale surjective chart smooth of relative dimension `d`
over `M`: the scheme `U ×_V (V ×_B M)` built from a chart square of `f`. -/
theorem exists_smooth_chart {U V : Over S0.{u}} (a : (schemeYoneda S0).obj U ⟶ Y.presheaf)
    (b : (schemeYoneda S0).obj V ⟶ B.presheaf) (φ : U ⟶ V)
    (hae : IsEtale a) (has : IsSurjective a) (hbe : IsEtale b) {d : ℕ}
    (hφ : SmoothOfRelativeDimension d φ.left)
    (hsq : a ≫ hom f = (schemeYoneda S0).map φ ≫ b) :
    ∃ (P : Scheme.{u}) (aP : (schemeYoneda S0).obj (toOver P) ⟶ ChartFibre.fibre (hom f) t)
      (π : P ⟶ M), IsEtale aP ∧ IsSurjective aP ∧ SmoothOfRelativeDimension d π ∧
        aP ≫ ChartFibre.snd (hom f) t = (schemeYoneda S0).map (toOverHom π) := by
  have hbr : IsRepresentableMorphism b := hbe.representable
  let V' : Over S0.{u} := hbr.pullback t
  let fV : V' ⟶ V := Functor.relativelyRepresentable.fst' hbr t
  let sV : V' ⟶ toOver M := hbr.snd t
  have hV : IsPullback ((schemeYoneda S0).map fV) ((schemeYoneda S0).map sV) b t :=
    Functor.relativelyRepresentable.isPullback' hbr t
  have hsVe : Etale sV.left := hbe.projection t _ sV hV
  have : SmoothOfRelativeDimension d (pullback.snd φ.left fV.left) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension d) _ _ hφ
  let π : pullback φ.left fV.left ⟶ M := pullback.snd φ.left fV.left ≫ sV.left
  have hπ : SmoothOfRelativeDimension d π := by
    have h := (inferInstance : SmoothOfRelativeDimension (d + 0)
      (pullback.snd φ.left fV.left ≫ sV.left))
    exact h
  have hA : IsPullback ((schemeYoneda S0).map (homOver (Y := U) (pullback.fst φ.left fV.left)))
      ((schemeYoneda S0).map (homOver (Y := V') (pullback.snd φ.left fV.left)))
      ((schemeYoneda S0).map φ) ((schemeYoneda S0).map fV) := by
    have hO : IsPullback (homOver (Y := U) (pullback.fst φ.left fV.left))
        (homOver (Y := V') (pullback.snd φ.left fV.left)) φ fV := by
      apply IsPullback.of_map_of_faithful (Over.forget S0)
      exact IsPullback.of_hasPullback φ.left fV.left
    exact hO.map (schemeYoneda S0)
  have hcomp : homOver (Y := V') (pullback.snd φ.left fV.left) ≫ sV = toOverHom π := by
    ext; rfl
  have hw : ((schemeYoneda S0).map (homOver (Y := U) (pullback.fst φ.left fV.left)) ≫ a) ≫
      hom f = (schemeYoneda S0).map (toOverHom π) ≫ t := by
    calc ((schemeYoneda S0).map (homOver (Y := U) (pullback.fst φ.left fV.left)) ≫ a) ≫ hom f
        = ((schemeYoneda S0).map (homOver (Y := U) (pullback.fst φ.left fV.left)) ≫
            (schemeYoneda S0).map φ) ≫ b := by rw [Category.assoc, hsq, Category.assoc]
      _ = ((schemeYoneda S0).map (homOver (Y := V') (pullback.snd φ.left fV.left)) ≫
            (schemeYoneda S0).map fV) ≫ b := by rw [hA.w]
      _ = (schemeYoneda S0).map (homOver (Y := V') (pullback.snd φ.left fV.left)) ≫
            (schemeYoneda S0).map sV ≫ t := by rw [Category.assoc, hV.w]
      _ = (schemeYoneda S0).map (toOverHom π) ≫ t := by
        rw [← Category.assoc, ← Functor.map_comp, hcomp]
  have hsq2 : IsPullback ((schemeYoneda S0).map (homOver (Y := U) (pullback.fst φ.left fV.left)))
      ((ChartFibre.isPullback (hom f) t).lift _ _ hw) a (ChartFibre.fst (hom f) t) := by
    refine IsPullback.of_bot ?_ (IsPullback.lift_fst _ _ _ _).symm (ChartFibre.isPullback (hom f) t)
    rw [IsPullback.lift_snd, hsq, ← hcomp, Functor.map_comp]
    exact hA.paste_vert hV
  refine ⟨pullback φ.left fV.left, (ChartFibre.isPullback (hom f) t).lift _ _ hw, π, ?_, ?_, hπ,
    IsPullback.lift_snd _ _ _ _⟩
  · exact MorphismProperty.of_isPullback (P := (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget S0)).relative (schemeYoneda S0)) hsq2 hae
  · exact MorphismProperty.of_isPullback (P := (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget S0)).relative (schemeYoneda S0)) hsq2 has

/-- The points of the fibres of `Y ×_B M → M` over field points of `M` form connected spaces
when `f` has geometrically connected fibres: these fibres are fibres of `f`. -/
theorem connectedSpace_fib (hconn : HasGeometricallyConnectedFibres f) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ M) :
    @ConnectedSpace (Points (fib (ChartFibre.snd (hom f) t) s)) (pointTopology _) := by
  have hpb := (IsPullback.of_hasPullback (ChartFibre.snd (hom f) t)
    ((schemeYoneda S0).map (toOverHom s))).paste_horiz (ChartFibre.isPullback (hom f) t)
  have h := hconn K (specULiftZIsTerminal.from _) ((schemeYoneda S0).map (toOverHom s) ≫ t)
  let := pointTopology (fib (ChartFibre.snd (hom f) t) s)
  let := pointTopology (pullback (hom f) ((schemeYoneda S0).map (toOverHom s) ≫ t))
  exact (Points.isoHomeomorph hpb.isoPullback).symm.connectedSpace_iff.mp h

/-- The `κ`-points of `Y ×_B M` over a `κ`-point `m` of `M` are the `κ`-points of `Y` over the
`κ`-point `t ∘ m` of `B`. -/
def fibreEquiv (κ : Type u) [Field κ] (m : Spec (CommRingCat.of κ) ⟶ M) :
    {z : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ ChartFibre.fibre (hom f) t //
        z ≫ ChartFibre.snd (hom f) t = (schemeYoneda S0).map (toOverHom m)} ≃
      {y : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ Y.presheaf //
        y ≫ hom f = (schemeYoneda S0).map (toOverHom m) ≫ t} where
  toFun z := ⟨z.1 ≫ ChartFibre.fst (hom f) t, by
    rw [Category.assoc, (ChartFibre.isPullback (hom f) t).w, ← Category.assoc, z.2]⟩
  invFun y := ⟨(ChartFibre.isPullback (hom f) t).lift y.1 _ y.2, IsPullback.lift_snd _ _ _ _⟩
  left_inv z := Subtype.ext ((ChartFibre.isPullback (hom f) t).hom_ext
    (IsPullback.lift_fst _ _ _ _) (by rw [IsPullback.lift_snd, z.2]))
  right_inv y := Subtype.ext (IsPullback.lift_fst _ _ _ _)

end FibreProduct

/-- **The uniform Lang–Weil estimate over a scheme chart of the base.** Let `f : Y → B` be a
separated, quasi-compact, surjective morphism of algebraic spaces over `Spec ℤ` with
geometrically connected fibres and an étale chart square with a scheme map `φ` smooth of
relative dimension `d`, and let `t : M → B` be a morphism from an affine scheme locally of
finite type over `ℤ`. Assuming the uniform Lang–Weil estimate and the uniform upper bound for
point counts in families of schemes, there is `C > 0` such that for every finite field `κ` and
every `κ`-point `m` of `M`, the number `N` of `κ`-points of `Y` over `t ∘ m` satisfies
`|N - (#κ) ^ d| ≤ C (#κ) ^ (d - 1/2)`. -/
theorem uniformLangWeil_fibreProduct (hFLW : FamilyLangWeilStatement.{u})
    (hFPU : FamilyPointUpperBoundStatement.{u}) {B Y : AlgebraicSpace S0.{u}} (f : Y ⟶ B)
    (d : ℕ) {U V : Over S0.{u}} (a : (schemeYoneda S0).obj U ⟶ Y.presheaf)
    (b : (schemeYoneda S0).obj V ⟶ B.presheaf) (φ : U ⟶ V)
    (hae : IsEtale a) (has : IsSurjective a) (hbe : IsEtale b)
    (hφ : SmoothOfRelativeDimension d φ.left) (hsq : a ≫ hom f = (schemeYoneda S0).map φ ≫ b)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f)
    (M : Scheme.{u}) [IsAffine M] [LocallyOfFiniteType (specULiftZIsTerminal.from M)]
    (t : (schemeYoneda S0).obj (toOver M) ⟶ B.presheaf) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] (m : Spec (CommRingCat.of κ) ⟶ M),
      |(Nat.card {y : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ Y.presheaf //
          y ≫ hom f = (schemeYoneda S0).map (toOverHom m) ≫ t} : ℝ) - (Nat.card κ : ℝ) ^ d| ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := by
  have : IsAffine (toOver M).left := ‹IsAffine M›
  have : _root_.AlgebraicGeometry.IsSeparated (toOver M).hom := inferInstance
  let X : AlgebraicSpace S0.{u} := ChartFibre.space f t hsep hqc
  let g : X.presheaf ⟶ (schemeYoneda S0).obj (toOver M) := ChartFibre.snd (hom f) t
  obtain ⟨P, aP, πP, haPe, haPs, hπP, hgP⟩ := exists_smooth_chart f t a b φ hae has hbe hφ hsq
  obtain ⟨Q, aQ, hQc, haQe, haQs⟩ := ChartFibre.exists_atlas_fibre f t hqc
  obtain ⟨O, aO, πO, hO, haOe, haOs, hπO, hgO⟩ :=
    exists_affine_chart g aP πP haPe haPs (d := d) hgP aQ haQe haQs
  obtain ⟨R, tR, sR, hpb, htR, hsR⟩ := exists_kernelPair haOe
  let c : SepChart.{u} := ⟨X, ChartFibre.isSeparated_space f t hsep hqc, toOver O, hO, aO,
    haOe, haOs, R, tR, sR, hpb, htR, hsR⟩
  have hpt : ∀ y : M, ∃ (T : Over S0.{u}) (z : (schemeYoneda S0).obj T ⟶ X.presheaf)
      (s : T.left ⟶ M) (τ : T.left), z ≫ g = (schemeYoneda S0).map (overHom s) ∧ s τ = y := by
    intro y
    obtain ⟨q, hq⟩ := hsurj (chartPointMap t y)
    obtain ⟨u, rfl⟩ := surjective_chartPointMap a has q
    have hu : chartPointMap (a ≫ hom f) u = chartPointMap t y := by
      rw [← hq]
      exact Points.map_comp a (hom f) (schemePoint U u)
    obtain ⟨T, g₁, g₂, τ, hg, h₁, h₂⟩ :=
      (chartPointMap_eq_iff_sameImage₂ (a ≫ hom f) t u y).mp hu
    refine ⟨T, (ChartFibre.isPullback (hom f) t).lift ((schemeYoneda S0).map g₁ ≫ a)
      ((schemeYoneda S0).map g₂) (by rw [Category.assoc, hg]), g₂.left, τ, ?_, h₂⟩
    rw [IsPullback.lift_snd]
    congr 1
  have hπs : Function.Surjective πO := surjective_of_exists_point g aO haOs πO hgO hpt
  obtain ⟨C, hC, hb⟩ := uniformLangWeil_schemeBase hFLW hFPU c g πO (d := d) hπs hgO
    (fun K _ s => connectedSpace_fib f t hconn K s)
  refine ⟨C, hC, fun κ _ _ m => ?_⟩
  rw [← Nat.card_congr (fibreEquiv f t κ m)]
  exact hb κ m

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
