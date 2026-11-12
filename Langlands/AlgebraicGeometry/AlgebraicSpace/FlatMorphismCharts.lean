import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitFlatnessDimensionDescentStatement
import Langlands.CommutativeAlgebra.EtaleFlatLocalDescentProof
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Testing flat morphisms on arbitrary etale chart squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- A flat composite with an etale second morphism has flat first morphism. -/
theorem flat_of_comp_etale {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    [Etale g] [Flat (f ≫ g)] : Flat f := by
  have h : MorphismProperty.HasOfPostcompProperty (@Flat.{u}) (@Etale.{u}) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro X Y φ hφ
    let := hφ
    change Flat (pullback.diagonal φ)
    infer_instance
  exact h.of_postcomp f g inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Flatness descends along a surjective flat morphism of the source. -/
theorem flat_of_surjective_flat_comp {U V W : Scheme.{u}} (p : U ⟶ V) (f : V ⟶ W)
    [Surjective p] [Flat p] [Flat (p ≫ f)] : Flat f := by
  apply Flat.of_stalkMap
  intro v
  obtain ⟨u, rfl⟩ := p.surjective v
  let := (f.stalkMap (p u)).hom.toAlgebra
  let := (p.stalkMap u).hom.toAlgebra
  let := (f.stalkMap (p u) ≫ p.stalkMap u).hom.toAlgebra
  have : IsScalarTower (W.presheaf.stalk (f (p u)))
      (V.presheaf.stalk (p u)) (U.presheaf.stalk u) := .of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat (V.presheaf.stalk (p u)) (U.presheaf.stalk u) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap p u) (p.toLRSHom.prop u)
  have hc := Flat.stalkMap (p ≫ f) u
  rw [Scheme.Hom.stalkMap_comp] at hc
  have : Module.Flat (W.presheaf.stalk (f (p u))) (U.presheaf.stalk u) := hc
  exact Langlands.CommutativeAlgebra.flat_of_flat_of_faithfullyFlat
    (W.presheaf.stalk (f (p u))) (V.presheaf.stalk (p u)) (U.presheaf.stalk u)

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A flat morphism of spaces is flat on every commuting etale scheme-chart square.
The source chart in the tested square need not be surjective. -/
theorem IsFlatMorphism.flat_chart {f : X ⟶ Y} (hf : IsFlatMorphism f)
    {U' V' : Over S} (a' : (schemeYoneda S).obj U' ⟶ X.presheaf)
    (b' : (schemeYoneda S).obj V' ⟶ Y.presheaf) (ψ : U' ⟶ V')
    (ha' : IsEtale a') (hb' : IsEtale b')
    (hw' : a' ≫ hom f = (schemeYoneda S).map ψ ≫ b') : Flat ψ.left := by
  obtain ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  let F := schemeYoneda S
  let T := ha.representable.pullback a'
  let q : T ⟶ U := Functor.relativelyRepresentable.fst' ha.representable a'
  let p : T ⟶ U' := ha.representable.snd a'
  have hT : IsPullback (F.map q) (F.map p) a a' :=
    Functor.relativelyRepresentable.isPullback' ha.representable a'
  have hq : Etale q.left := ha'.projection a (F.map p) q hT.flip
  have hp : Etale p.left := ha.projection a' (F.map q) p hT
  have hps : Surjective p.left := hs.projection a' (F.map q) p hT
  let R := hb.representable.pullback b'
  let r : R ⟶ V := Functor.relativelyRepresentable.fst' hb.representable b'
  let s : R ⟶ V' := hb.representable.snd b'
  have hR : IsPullback (F.map r) (F.map s) b b' :=
    Functor.relativelyRepresentable.isPullback' hb.representable b'
  have hr : Etale r.left := hb'.projection b (F.map s) r hR.flip
  have hs' : Etale s.left := hb.projection b' (F.map r) s hR
  have ht : F.map (q ≫ φ) ≫ b = F.map (p ≫ ψ) ≫ b' := by
    rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc, ← hw, ← hw',
      ← Category.assoc, hT.w, Category.assoc]
  let t : T ⟶ R := F.preimage (hR.lift (F.map (q ≫ φ)) (F.map (p ≫ ψ)) ht)
  have htr : t ≫ r = q ≫ φ := by
    apply F.map_injective
    rw [F.map_comp, Functor.map_preimage]
    exact hR.lift_fst _ _ _
  have hts : t ≫ s = p ≫ ψ := by
    apply F.map_injective
    rw [F.map_comp, Functor.map_preimage]
    exact hR.lift_snd _ _ _
  have : Etale q.left := hq
  have : Etale p.left := hp
  have : Surjective p.left := hps
  have : Etale r.left := hr
  have : Etale s.left := hs'
  have : Flat φ.left := hφ
  have : Flat (t.left ≫ r.left) := by
    change Flat (t ≫ r).left
    rw [htr]
    change Flat (q.left ≫ φ.left)
    infer_instance
  have : Flat t.left := flat_of_comp_etale t.left r.left
  have : Flat (p.left ≫ ψ.left) := by
    change Flat (p ≫ ψ).left
    rw [← hts]
    change Flat (t.left ≫ s.left)
    infer_instance
  exact flat_of_surjective_flat_comp p.left ψ.left

/-- Any commuting etale chart square with surjective source tests flatness exactly. -/
theorem isFlatMorphism_iff_flat_chart {f : X ⟶ Y}
    {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V)
    (ha : IsEtale a) (hs : IsSurjective a) (hb : IsEtale b)
    (hw : a ≫ hom f = (schemeYoneda S).map φ ≫ b) :
    IsFlatMorphism f ↔ Flat φ.left :=
  ⟨fun hf => hf.flat_chart a b φ ha hb hw,
    fun hφ => ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩⟩

/-- Flatness can be tested on any commuting etale chart square whose source
chart is surjective. -/
def FlatMorphismChartComparisonStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (U V : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V),
    IsEtale a → IsSurjective a → IsEtale b →
      a ≫ hom f = (schemeYoneda S).map φ ≫ b →
      (IsFlatMorphism f ↔ Flat φ.left)

/-- The chart-independence equivalence with its complete quantifiers. -/
theorem flatMorphismChartComparison : FlatMorphismChartComparisonStatement.{u} := by
  intro S X Y f U V a b φ ha hs hb hw
  exact isFlatMorphism_iff_flat_chart a b φ ha hs hb hw

end Langlands.AlgebraicGeometry.AlgebraicSpace
