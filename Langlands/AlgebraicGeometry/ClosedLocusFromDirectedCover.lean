import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Gluing closed loci on a locally directed open cover -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.AlgebraicGeometry.ClosedLocusFromDirectedCover

variable {X : Scheme.{u}} (P : ∀ ⦃Y : Scheme.{u}⦄, (Y ⟶ X) → Prop)
    (𝒰 : X.OpenCover)

/-- Closed charts for one property of actual morphisms into the base. -/
structure Data where
  Z : 𝒰.I₀ → Scheme.{u}
  ι : ∀ i, Z i ⟶ 𝒰.X i
  closed : ∀ i, IsClosedImmersion (ι i)
  chart_iff : ∀ i ⦃Y : Scheme.{u}⦄ (g : Y ⟶ 𝒰.X i),
    (∃ k : Y ⟶ Z i, k ≫ ι i = g) ↔ P (g ≫ 𝒰.f i)

attribute [instance] Data.closed

namespace Data

variable {P 𝒰} (D : Data P 𝒰)

/-- The local closed inclusion viewed as a morphism into the original base. -/
abbrev emb (i : 𝒰.I₀) : D.Z i ⟶ X := D.ι i ≫ 𝒰.f i

lemma prop_emb (i : 𝒰.I₀) : P (D.emb i) :=
  (D.chart_iff i (D.ι i)).mp ⟨𝟙 _, Category.id_comp _⟩

variable [Category 𝒰.I₀] [𝒰.LocallyDirected]

/-- Transitions are forced by the common factorization property. -/
def transition {i j : 𝒰.I₀} (f : i ⟶ j) : D.Z i ⟶ D.Z j :=
  ((D.chart_iff j (D.ι i ≫ 𝒰.trans f)).mpr (by
    simpa only [Category.assoc, Scheme.Cover.trans_map] using D.prop_emb i)).choose

@[reassoc (attr := simp)]
lemma transition_ι {i j : 𝒰.I₀} (f : i ⟶ j) :
    D.transition f ≫ D.ι j = D.ι i ≫ 𝒰.trans f :=
  ((D.chart_iff j (D.ι i ≫ 𝒰.trans f)).mpr (by
    simpa only [Category.assoc, Scheme.Cover.trans_map] using D.prop_emb i)).choose_spec

/-- The diagram of local closed subschemes. -/
def functor : 𝒰.I₀ ⥤ Scheme.{u} where
  obj := D.Z
  map := D.transition
  map_id i := by
    rw [← cancel_mono (D.ι i)]
    simp only [transition_ι, Scheme.Cover.trans_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    rw [← cancel_mono (D.ι _)]
    simp only [transition_ι, transition_ι_assoc, Category.assoc, Scheme.Cover.trans_comp]

/-- The local closed inclusions as a natural transformation. -/
def natTrans : D.functor ⟶ 𝒰.functorOfLocallyDirected where
  app := D.ι
  naturality _ _ f := D.transition_ι f

variable (hcomp : ∀ ⦃Y Y' : Scheme.{u}⦄ (f : Y' ⟶ Y) (g : Y ⟶ X),
  P g → P (f ≫ g))

include hcomp in
lemma equifibered : D.natTrans.Equifibered := by
  intro i j f
  let lift (s : PullbackCone (D.ι j) (𝒰.trans f)) : s.pt ⟶ D.Z i :=
    ((D.chart_iff i s.snd).mpr (by
      have h := hcomp s.fst (D.emb j) (D.prop_emb j)
      change P (s.fst ≫ (D.ι j ≫ 𝒰.f j)) at h
      rw [← Category.assoc, s.condition, Category.assoc, Scheme.Cover.trans_map] at h
      exact h)).choose
  have lift_snd (s : PullbackCone (D.ι j) (𝒰.trans f)) : lift s ≫ D.ι i = s.snd :=
    ((D.chart_iff i s.snd).mpr (by
      have h := hcomp s.fst (D.emb j) (D.prop_emb j)
      change P (s.fst ≫ (D.ι j ≫ 𝒰.f j)) at h
      rw [← Category.assoc, s.condition, Category.assoc, Scheme.Cover.trans_map] at h
      exact h)).choose_spec
  have lift_fst (s : PullbackCone (D.ι j) (𝒰.trans f)) :
      lift s ≫ D.transition f = s.fst := by
    rw [← cancel_mono (D.ι j), Category.assoc, D.transition_ι, ← Category.assoc,
      lift_snd, s.condition]
  refine IsPullback.of_isLimit' ⟨D.transition_ι f⟩
    (PullbackCone.IsLimit.mk _ lift lift_fst lift_snd ?_)
  intro s m _ hm
  apply (cancel_mono (D.ι i)).mp
  exact (show m ≫ D.ι i = s.snd from hm).trans (lift_snd s).symm

/-- Relative gluing of the closed charts, with its actual cartesian transitions. -/
def gluingData : 𝒰.RelativeGluingData where
  functor := D.functor
  natTrans := D.natTrans
  equifibered := D.equifibered hcomp

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/-- The actual glued closed locus. -/
def scheme : Scheme.{u} := (D.gluingData hcomp).glued

/-- The actual inclusion of the glued locus into the base. -/
def inclusion : D.scheme hcomp ⟶ X := (D.gluingData hcomp).toBase

/-- The local pieces are exactly the pullbacks of the global inclusion. -/
lemma isPullback (i : 𝒰.I₀) :
    IsPullback (D.ι i) ((D.gluingData hcomp).cover.f i) (𝒰.f i)
      (D.inclusion hcomp) :=
  (D.gluingData hcomp).isPullback_natTrans_ι_toBase i

instance : IsClosedImmersion (D.inclusion hcomp) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒰
  intro i
  change IsClosedImmersion (pullback.snd (D.inclusion hcomp) (𝒰.f i))
  rw [← (D.isPullback hcomp i).flip.isoPullback_inv_snd]
  infer_instance

variable (hloc : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X),
  (∀ i : 𝒰.I₀, P ((𝒰.pullback₁ g : Y.OpenCover).f i ≫ g)) → P g)

include hloc in
lemma prop_inclusion : P (D.inclusion hcomp) := by
  apply hloc
  intro i
  let sq := (D.isPullback hcomp i).flip
  let a := sq.isoPullback.inv
  have h := hcomp a (D.emb i) (D.prop_emb i)
  change P (a ≫ (D.ι i ≫ 𝒰.f i)) at h
  rw [← Category.assoc, sq.isoPullback_inv_snd, ← pullback.condition] at h
  exact h

include hloc in
/-- Factorization through the glued closed locus is exactly the original property. -/
theorem factors_iff {Y : Scheme.{u}} (g : Y ⟶ X) :
    (∃ k : Y ⟶ D.scheme hcomp, k ≫ D.inclusion hcomp = g) ↔ P g := by
  constructor
  · rintro ⟨k, rfl⟩
    exact hcomp k (D.inclusion hcomp) (D.prop_inclusion hcomp hloc)
  · intro hg
    let 𝒱 : Y.OpenCover := 𝒰.pullback₁ g
    have hlocal (i : 𝒰.I₀) :
        ∃ k : 𝒱.X i ⟶ D.Z i, k ≫ D.ι i = pullback.snd g (𝒰.f i) := by
      apply (D.chart_iff i _).mpr
      rw [← pullback.condition]
      exact hcomp (𝒱.f i) g hg
    let k (i : 𝒰.I₀) : 𝒱.X i ⟶ D.scheme hcomp :=
      (hlocal i).choose ≫ (D.gluingData hcomp).cover.f i
    have hk (i : 𝒰.I₀) : k i ≫ D.inclusion hcomp = 𝒱.f i ≫ g := by
      dsimp only [k]
      rw [Category.assoc]
      change (hlocal i).choose ≫
        (colimit.ι (D.gluingData hcomp).functor i ≫ (D.gluingData hcomp).toBase) = _
      rw [Scheme.Cover.RelativeGluingData.ι_toBase]
      change (hlocal i).choose ≫ (D.ι i ≫ 𝒰.f i) = pullback.fst g (𝒰.f i) ≫ g
      rw [← Category.assoc, (hlocal i).choose_spec, ← pullback.condition]
    have hcompat {i j : 𝒱.I₀} (f : i ⟶ j) : 𝒱.trans f ≫ k j = k i := by
      rw [← cancel_mono (D.inclusion hcomp), Category.assoc, hk, ← Category.assoc,
        Scheme.Cover.trans_map, hk]
    refine ⟨𝒱.glueMorphismsOfLocallyDirected k hcompat, ?_⟩
    apply 𝒱.hom_ext
    intro i
    rw [Scheme.OpenCover.map_glueMorphismsOfLocallyDirected_assoc, hk]

end Data

end Langlands.AlgebraicGeometry.ClosedLocusFromDirectedCover
