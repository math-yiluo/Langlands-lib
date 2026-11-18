import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily

/-! # Testing étale algebraic-space morphisms on finite-type affine schemes -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SchemeOpenChart

variable {S : Scheme.{u}} {U : Over S} (𝒰 : Scheme.OpenCover.{v} U.left)

/-- A member of a scheme open cover, retaining its map to the fixed base. -/
def obj (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ U.hom)

/-- The cover map over the fixed base. -/
def map (i : 𝒰.I₀) : obj 𝒰 i ⟶ U := Over.homMk (𝒰.f i)

instance (i : 𝒰.I₀) : _root_.AlgebraicGeometry.IsOpenImmersion (map 𝒰 i).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (𝒰.f i))

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back an open cover in the over category covers its actual source. -/
def pullbackOpenCover {W : Over S} (r : W ⟶ U) : W.left.OpenCover := by
  let R i := Limits.pullback r (map 𝒰 i)
  let p i : R i ⟶ W := pullback.fst r (map 𝒰 i)
  let : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (p i).left := fun i =>
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback r (map 𝒰 i)).map (Over.forget S)).flip)
      (show _root_.AlgebraicGeometry.IsOpenImmersion (map 𝒰 i).left from inferInstance)
  apply Scheme.Cover.mkOfCovers
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}) 𝒰.I₀
    (fun i => (R i).left) (fun i => (p i).left)
  intro x
  obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq (𝒰.pullback₁ r.left) x
  let e := PreservesPullback.iso (Over.forget S) r (map 𝒰 i)
  refine ⟨i, e.inv y, ?_⟩
  exact (congrArg (fun f : Limits.pullback r.left (map 𝒰 i).left ⟶ W.left => f y)
    (PreservesPullback.iso_inv_fst (Over.forget S) r (map 𝒰 i))).trans hy

set_option backward.isDefEq.respectTransparency false in
/-- Relative étaleness can be checked on a scheme open cover of its source. -/
theorem isEtale_of_cover {F : Presheaf S} (hF : HasRepresentableDiagonal F)
    (a : (schemeYoneda S).obj U ⟶ F)
    (ha : ∀ i, IsEtale ((schemeYoneda S).map (map 𝒰 i) ≫ a)) : IsEtale a := by
  refine ⟨Functor.relativelyRepresentable.of_diag hF a, ?_⟩
  intro T W g b q h
  obtain ⟨r, rfl⟩ := (schemeYoneda S).map_surjective b
  apply IsZariskiLocalAtSource.of_openCover (P := @_root_.AlgebraicGeometry.Etale.{u})
    (pullbackOpenCover 𝒰 r)
  intro i
  change 𝒰.I₀ at i
  have hp := ((IsPullback.of_hasPullback r (map 𝒰 i)).flip).map (schemeYoneda S)
  have hi := hp.paste_vert h
  exact (ha i).projection g
    ((schemeYoneda S).map (pullback.snd r (map 𝒰 i)))
    (pullback.fst r (map 𝒰 i) ≫ q) (by
      simpa only [Functor.map_comp] using hi)

end SchemeOpenChart

open PointTopology

/-- For a source locally of finite type, finite-type affine test points detect
étale algebraic-space morphisms. No separatedness hypothesis is needed. -/
theorem isEtaleMorphism_iff_finiteTypeAffineTests
    {K : Type u} [NontriviallyNormedField K]
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX' : LocallyOfFiniteTypeOverBase X') :
    IsEtaleMorphism f ↔
      ∀ (A : Type u) [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
        (x : RingPoints K X' A),
        IsEtale (uliftYonedaEquiv.{u + 1}.symm x) →
          IsEtale (uliftYonedaEquiv.{u + 1}.symm x ≫ hom f) := by
  constructor
  · intro hf A _ _ _ x hx
    exact hf (ringTest K A) _ hx
  · intro hf U a ha
    apply SchemeOpenChart.isEtale_of_cover U.left.affineCover X.hasRepresentableDiagonal
    intro i
    let V := SchemeOpenChart.obj U.left.affineCover i
    let j : V ⟶ U := SchemeOpenChart.map U.left.affineCover i
    have hj : Etale j.left := inferInstance
    have hb : IsEtale ((schemeYoneda _).map j ≫ a) := (isEtale_map j hj).comp ha
    let b := (schemeYoneda _).map j ≫ a
    let : IsAffine V.left := inferInstanceAs (IsAffine (U.left.affineCover.X i))
    let : LocallyOfFiniteType V.hom := locallyOfFiniteType_of_isEtale hX' b hb
    let A := AffineCoordinateRing K V
    let e := affineSchemeOverIso K V
    let c := (schemeYoneda _).map e.inv ≫ b
    let x : RingPoints K X' A := uliftYonedaEquiv c
    have hc : IsEtale c := hb.iso_comp ((schemeYoneda _).mapIso e.symm)
    have hx : IsEtale (uliftYonedaEquiv.{u + 1}.symm x) := by
      simpa only [x, Equiv.symm_apply_apply] using hc
    have hx' := hf A x hx
    have hbc : IsEtale ((schemeYoneda _).map e.hom ≫
        (uliftYonedaEquiv.{u + 1}.symm x ≫ hom f)) :=
      hx'.iso_comp ((schemeYoneda _).mapIso e)
    simp only [x, Equiv.symm_apply_apply] at hbc
    have he : (schemeYoneda _).map e.hom ≫ c = b := by
      dsimp only [c]
      rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc, he] at hbc
    simpa only [b, Category.assoc] using hbc

end Langlands.AlgebraicGeometry.AlgebraicSpace
