import Langlands.GroupScheme.Torus.EtalePermutationCoefficientCocycle
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Restriction and finite affine refinement of permutation atlases -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.EtalePermutationAtlas

variable {S U U' V V' W : Scheme.{u}} {D : GroupScheme S}
  {I J : Type u} [Finite I] [Finite J]

/-- Original-group coordinates of a restricted chart equal the original chart
coordinates after composing the test map. -/
theorem coordinates_restrictChart (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (a : V ⟶ U) (r : V ⟶ S) (h : a ≫ f = r)
    {T : Scheme.{u}} (t : T ⟶ V) (x : T ⟶ D.X.left)
    (hx : x ≫ D.X.hom = t ≫ r) :
    coordinates r (restrictChart f e a r h) t x hx =
      coordinates f e (t ≫ a) x (by rw [Category.assoc, h]; exact hx) := by
  let p : Over.mk (t ≫ r) ⟶ D.X := Over.homMk x hx
  let y := (GroupScheme.baseChangePointsEquiv r D (Over.mk t)).symm p
  have hy : y.left ≫ pullback.fst D.X.hom r = x :=
    congrArg Over.Hom.left ((GroupScheme.baseChangePointsEquiv r D (Over.mk t)).apply_symm_apply p)
  have hc := restrictChart_coordinates f e a r h (Over.mk t) y
  change splitTorus.pointsEquiv I (Over.mk t)
    (y ≫ (restrictChart f e a r h).hom.hom.hom) = _
  rw [hc]
  have hx' : x ≫ D.X.hom = (t ≫ a) ≫ f := by rw [Category.assoc, h]; exact hx
  have hy' : (y.left ≫ pullback.fst D.X.hom r) ≫ D.X.hom = (t ≫ a) ≫ f :=
    (congrArg (fun k => k ≫ D.X.hom) hy).trans hx'
  exact coordinates_congr f e hy' hx' rfl hy

/-- Original-group coordinate equations on every test imply agreement of the
normalized charts. -/
theorem AgreeBy.of_coordinates (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : W ⟶ U) (q' : W ⟶ U') (r : W ⟶ S)
    (h : q ≫ f = r) (h' : q' ≫ g = r) (σ : J ≃ I)
    (H : ∀ (T : Over W) (x : T.left ⟶ D.X.left)
      (hx : x ≫ D.X.hom = T.hom ≫ r) (j : J),
      EtalePermutationAtlas.coordinates g e' (T.hom ≫ q') x
          (by rw [Category.assoc, h']; exact hx) j =
        EtalePermutationAtlas.coordinates f e (T.hom ≫ q) x
          (by rw [Category.assoc, h]; exact hx) (σ j)) :
    AgreeBy f g e e' q q' r h h' σ := by
  intro T x j
  rw [restrictChart_coordinates, restrictChart_coordinates]
  apply H
  have hw : x.left ≫ pullback.snd D.X.hom r = T.hom := Over.w x
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

set_option maxHeartbeats 600000 in
/-- Locally permuting transitions persist when either chart is restricted along
an arbitrary scheme morphism, using the canonical normalized restricted charts. -/
theorem LocallyPermutes.restrict (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e')
    (a : V ⟶ U) (b : V' ⟶ U') (r : V ⟶ S) (s : V' ⟶ S)
    (ha : a ≫ f = r) (hb : b ≫ g = s) :
    LocallyPermutes r s (restrictChart f e a r ha) (restrictChart g e' b s hb) := by
  let m : pullback r s ⟶ pullback f g :=
    pullback.lift (pullback.fst r s ≫ a) (pullback.snd r s ≫ b) (by
      simp only [Category.assoc, ha, hb, pullback.condition])
  intro w
  obtain ⟨O, hw, σ, Hσ⟩ := H (m w)
  let P : (pullback r s).Opens := m ⁻¹ᵁ O
  let k : (P : Scheme.{u}) ⟶ (O : Scheme.{u}) :=
    IsOpenImmersion.lift O.ι (P.ι ≫ m) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact p.2)
  have hk : k ≫ O.ι = P.ι ≫ m := IsOpenImmersion.lift_fac _ _ _
  refine ⟨P, hw, σ, ?_⟩
  apply AgreeBy.of_coordinates
  intro T x hx j
  rw [coordinates_restrictChart, coordinates_restrictChart]
  let Z : Over (O : Scheme.{u}) := Over.mk (T.hom ≫ k)
  have ht : Z.hom ≫ (O.ι ≫ pullback.fst f g) =
      (T.hom ≫ (P.ι ≫ pullback.fst r s)) ≫ a := by
    change (T.hom ≫ k) ≫ (O.ι ≫ pullback.fst f g) = _
    calc
      _ = T.hom ≫ (k ≫ O.ι) ≫ pullback.fst f g := by simp only [Category.assoc]
      _ = T.hom ≫ (P.ι ≫ m) ≫ pullback.fst f g := by rw [hk]
      _ = _ := by simp only [Category.assoc, m, pullback.lift_fst]
  have ht' : Z.hom ≫ (O.ι ≫ pullback.snd f g) =
      (T.hom ≫ (P.ι ≫ pullback.snd r s)) ≫ b := by
    change (T.hom ≫ k) ≫ (O.ι ≫ pullback.snd f g) = _
    calc
      _ = T.hom ≫ (k ≫ O.ι) ≫ pullback.snd f g := by simp only [Category.assoc]
      _ = T.hom ≫ (P.ι ≫ m) ≫ pullback.snd f g := by rw [hk]
      _ = _ := by simp only [Category.assoc, m, pullback.lift_snd]
  have hxZ : x ≫ D.X.hom = Z.hom ≫ (O.ι ≫ pullback.fst f g ≫ f) := by
    calc
      _ = T.hom ≫ (P.ι ≫ pullback.fst r s ≫ r) := hx
      _ = ((T.hom ≫ (P.ι ≫ pullback.fst r s)) ≫ a) ≫ f := by
        simp only [Category.assoc, ha]
      _ = (Z.hom ≫ (O.ι ≫ pullback.fst f g)) ≫ f := by rw [ht]
      _ = _ := by simp only [Category.assoc]
  have hc := Hσ.coordinates f g e e' (O.ι ≫ pullback.fst f g)
    (O.ι ≫ pullback.snd f g) (O.ι ≫ pullback.fst f g ≫ f) _ _ σ Z x hxZ j
  simpa only [ht, ht'] using hc

end Langlands.GroupScheme.EtalePermutationAtlas

namespace Langlands.GroupScheme

open EtalePermutationAtlas

/-- Over a compact base, an arbitrary small étale permutation atlas has a finite
affine refinement retaining actual normalized split charts and locally permuting
transitions. -/
theorem HasEtalePermutationAtlas.exists_finiteAffine
    {S : Scheme.{u}} [CompactSpace S] {D : GroupScheme S}
    (hD : HasEtalePermutationAtlas D) :
    ∃ (𝒱 : Scheme.AffineCover.{u} @Etale S) (_ : Finite 𝒱.I₀)
      (I : 𝒱.I₀ → Type u) (hI : ∀ a, Finite (I a)),
      letI : ∀ a, Finite (I a) := hI
      ∃ e : ∀ a, (GroupScheme.baseChange (𝒱.f a)).obj D ≅ splitTorus (𝒱.cover.X a) (I a),
        ∀ a b, LocallyPermutes (𝒱.f a) (𝒱.f b) (e a) (e b) := by
  obtain ⟨𝒰, I, hI, hchart⟩ := hD
  letI : ∀ a, Finite (I a) := hI
  obtain ⟨e, hperm⟩ := hchart
  haveI (a : 𝒰.I₀) : Etale (𝒰.f a) := 𝒰.map_prop a
  haveI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun a => (𝒰.f a).isOpenMap)
  obtain ⟨𝒱, m, hfin, hm⟩ :
      ∃ (𝒱 : Scheme.AffineCover.{u} @Etale S) (m : 𝒱.cover ⟶ 𝒰),
        Finite 𝒱.I₀ ∧ ∀ a, IsOpenImmersion (m.h₀ a) :=
    QuasiCompactCover.exists_hom 𝒰
  refine ⟨𝒱, hfin, (fun a => I (m.s₀ a)), (fun a => hI (m.s₀ a)), ?_⟩
  refine ⟨(fun a => restrictChart (𝒰.f (m.s₀ a)) (e (m.s₀ a))
    (m.h₀ a) (𝒱.f a) (m.w₀ a)), ?_⟩
  intro a b
  exact (hperm (m.s₀ a) (m.s₀ b)).restrict
    (𝒰.f (m.s₀ a)) (𝒰.f (m.s₀ b)) (e (m.s₀ a)) (e (m.s₀ b))
    (m.h₀ a) (m.h₀ b) (𝒱.f a) (𝒱.f b) (m.w₀ a) (m.w₀ b)

/-- A finite affine étale permutation atlas, retaining the actual split charts
and their local all-test coordinate equations. -/
structure FiniteAffinePermutationAtlas {S : Scheme.{u}} (D : GroupScheme S) where
  cover : Scheme.AffineCover.{u} @Etale S
  finiteCover : Finite cover.I₀
  coordinates : cover.I₀ → Type u
  finiteCoordinates : ∀ a, Finite (coordinates a)
  chart : letI : ∀ a, Finite (coordinates a) := finiteCoordinates
    ∀ a, (GroupScheme.baseChange (cover.f a)).obj D ≅
      splitTorus (cover.cover.X a) (coordinates a)
  permutes : letI : ∀ a, Finite (coordinates a) := finiteCoordinates
    ∀ a b, LocallyPermutes (cover.f a) (cover.f b) (chart a) (chart b)

/-- Choose the actual finite affine refinement of a small permutation atlas. -/
def HasEtalePermutationAtlas.finiteAffine
    {S : Scheme.{u}} [CompactSpace S] {D : GroupScheme S}
    (hD : HasEtalePermutationAtlas D) : FiniteAffinePermutationAtlas D := by
  apply Classical.choice
  obtain ⟨𝒱, hfin, I, hI, e, H⟩ := hD.exists_finiteAffine
  exact ⟨⟨𝒱, hfin, I, hI, e, H⟩⟩

end Langlands.GroupScheme
