import Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationStatement
import Langlands.GroupScheme.SimplyConnected.CommutingProductGeneration
import Langlands.GroupScheme.SimplyConnected.DirectFactors
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementStatement
import Langlands.GroupScheme.Reductive.Noncommutativity
import Langlands.GroupScheme.Lie.DimensionInduction
import Mathlib.Algebra.Group.Submonoid.Membership

/-! # Reduction of rational generation to semisimple normal complements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem range_eq_top_of_isIso {S : Scheme.{u}} {H G : GroupScheme S}
    (j : H ⟶ G) [IsIso j] : SubgroupFunctor.range j = ⊤ := by
  have : IsIso j.hom.hom := (Grp.forget (Over S)).map_isIso j
  apply SubgroupFunctor.ext
  intro T
  apply top_unique
  intro x _
  refine ⟨x ≫ inv j.hom.hom, ?_⟩
  change (x ≫ inv j.hom.hom) ≫ j.hom.hom = x
  simp

/-- Rational generation follows by dimension induction once normal semisimple
complements are available. -/
theorem simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement
    (hcomp : SemisimpleNormalIsogenyComplementStatement.{u}) :
    SimplyConnectedAlmostSimpleRationalGenerationStatement.{u} := by
  classical
  intro k _ G hG
  let P : GroupScheme (Spec (CommRingCat.of k)) → Prop := fun G =>
    IsSimplyConnected G →
      ∀ L : Subgroup (rationalPoints G),
        (∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
          IsAlmostSimple A → IsClosedSubgroup a → (SubgroupFunctor.range a).IsNormal →
          (rationalPoints.map a).range ≤ L) → L = ⊤
  have : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  have : ConnectedSpace G.X.left := hG.isSemisimple.isConnectedReductive.connectedSpace
  suffices h : P G from h hG
  apply smoothConnectedAffineGroup_lieDimension_induction P ?_ G
  intro G _ _ _ ih hG L hL
  by_cases htriv : SubgroupFunctor.range (𝟙 G) = ⊥
  · apply top_unique
    intro g _
    have hg : g ∈ (SubgroupFunctor.range (𝟙 G)).carrier _ :=
      ⟨g, Category.comp_id g⟩
    rw [htriv, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hg
    rw [hg]
    exact L.one_mem
  by_cases hAS : IsAlmostSimple G
  · apply top_unique
    intro g _
    apply hL G (𝟙 G) hAS (by change IsClosedImmersion (𝟙 G.X.left); infer_instance)
      (by
        intro T x y _ _
        apply SubgroupFunctor.mem_range.mpr
        exact ⟨x * y * x⁻¹, Category.comp_id _⟩)
    exact ⟨g, Category.comp_id g⟩
  have hbad : ¬ ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range j).IsNormal →
      SubgroupFunctor.range j = ⊥ ∨ SubgroupFunctor.range j = ⊤ := by
    intro h
    exact hAS ⟨hG.isSemisimple, hG.isSemisimple.noncommutative_of_nontrivial htriv, h⟩
  push Not at hbad
  obtain ⟨H, j, hj, hsH, hcH, hnH, hntH, hfullH⟩ := hbad
  obtain ⟨hH, K, i, hK, hi, _hnK, hprod, hc, hm⟩ :=
    hcomp k G H hG.isSemisimple j hj hsH hcH hnH
  let m := commutingSubgroupMultiplicationHom j i hc
  have : IsIso m := hG.central_isogeny_isIso (H ⊗ K) m hprod hm
  have hscProd : IsSimplyConnected (H ⊗ K) := hG.of_iso (asIso m)
  have hscH : IsSimplyConnected H := hscProd.of_tensor_left hH hK
  have hscK : IsSimplyConnected K := hscProd.of_tensor_right hH hK
  have : Smooth H.X.hom := hsH
  have : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
  have : ConnectedSpace H.X.left := hcH
  have : Smooth K.X.hom := hK.isConnectedReductive.smooth
  have : IsAffineHom K.X.hom := hK.isConnectedReductive.isAffineHom
  have : ConnectedSpace K.X.left := hK.isConnectedReductive.connectedSpace
  have hjproper : ¬ IsIso j := fun h => hfullH (by
    have := h
    exact range_eq_top_of_isIso j)
  have hiproper : ¬ IsIso i := fun h => hntH (by
    have := h
    exact range_left_eq_bot_of_isIso_right_commutingMultiplication j i hc)
  have hdimH : Lie.dimension H < Lie.dimension G :=
    Lie.dimension_lt_of_proper_closedSubgroup j hj hjproper
  have hdimK : Lie.dimension K < Lie.dimension G :=
    Lie.dimension_lt_of_proper_closedSubgroup i hi hiproper
  have hLH : L.comap (rationalPoints.map j) = ⊤ := by
    apply ih H hdimH hscH
    intro A a hA ha hn
    rintro z ⟨x, rfl⟩
    have hz : rationalPoints.map (a ≫ j) x ∈ L :=
      hL A (a ≫ j) hA (ha.comp hj)
        (hn.range_comp_left_of_isIso_commutingMultiplication j i hc) ⟨x, rfl⟩
    simpa only [Subgroup.mem_comap, rationalPoints.map_apply, Grp.comp_hom_hom,
      Category.assoc] using hz
  have hLK : L.comap (rationalPoints.map i) = ⊤ := by
    apply ih K hdimK hscK
    intro A a hA ha hn
    rintro z ⟨x, rfl⟩
    have hz : rationalPoints.map (a ≫ i) x ∈ L :=
      hL A (a ≫ i) hA (ha.comp hi)
        (hn.range_comp_right_of_isIso_commutingMultiplication j i hc) ⟨x, rfl⟩
    simpa only [Subgroup.mem_comap, rationalPoints.map_apply, Grp.comp_hom_hom,
      Category.assoc] using hz
  apply rationalPoints.subgroup_eq_top_of_isIso_commutingMultiplication j i hc L
  · rintro z ⟨x, rfl⟩
    have hx : x ∈ L.comap (rationalPoints.map j) := by rw [hLH]; exact Subgroup.mem_top _
    exact hx
  · rintro z ⟨x, rfl⟩
    have hx : x ∈ L.comap (rationalPoints.map i) := by rw [hLK]; exact Subgroup.mem_top _
    exact hx

/-- Rational points that belong to the image of a closed normal almost-simple
subgroup scheme. -/
def almostSimpleRationalGenerators {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Set (rationalPoints G) :=
  {g | ∃ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
    IsAlmostSimple A ∧ IsClosedSubgroup a ∧ (SubgroupFunctor.range a).IsNormal ∧
      g ∈ (rationalPoints.map a).range}

/-- Under the explicit complement premise, every rational point is a finite
product of points from closed normal almost-simple subgroup schemes. -/
theorem exists_almostSimpleRationalWord_of_normalIsogenyComplement
    (hcomp : SemisimpleNormalIsogenyComplementStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSimplyConnected G) (g : rationalPoints G) :
    ∃ l : List (rationalPoints G),
      (∀ x ∈ l, x ∈ almostSimpleRationalGenerators G) ∧ l.prod = g := by
  let S := almostSimpleRationalGenerators G
  have hinv : ∀ {x}, x ∈ Submonoid.closure S → x⁻¹ ∈ Submonoid.closure S := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨A, a, hA, ha, hn, y, rfl⟩ := hx
      exact Submonoid.subset_closure ⟨A, a, hA, ha, hn, y⁻¹, map_inv _ _⟩
    | one => simpa only [inv_one] using (Submonoid.closure S).one_mem
    | mul x y _ _ ihx ihy =>
      simpa only [mul_inv_rev] using (Submonoid.closure S).mul_mem ihy ihx
  let L : Subgroup (rationalPoints G) :=
    { Submonoid.closure S with inv_mem' := hinv }
  have hL : L = ⊤ :=
    simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement hcomp
      k G hG L (by
        intro A a hA ha hn x hx
        exact Submonoid.subset_closure ⟨A, a, hA, ha, hn, hx⟩)
  have hg : g ∈ Submonoid.closure S := by
    change g ∈ L
    rw [hL]
    exact Subgroup.mem_top g
  exact Submonoid.exists_list_of_mem_closure hg

/-- Choose a finite word in rational points of closed normal almost-simple
subgroups. Normal semisimple complements remain an explicit premise. -/
def almostSimpleRationalWord_of_normalIsogenyComplement
    (hcomp : SemisimpleNormalIsogenyComplementStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSimplyConnected G) (g : rationalPoints G) :
    {l : List (rationalPoints G) //
      (∀ x ∈ l, x ∈ almostSimpleRationalGenerators G) ∧ l.prod = g} :=
  ⟨Classical.choose (exists_almostSimpleRationalWord_of_normalIsogenyComplement hcomp hG g),
    Classical.choose_spec
      (exists_almostSimpleRationalWord_of_normalIsogenyComplement hcomp hG g)⟩

end Langlands.GroupScheme
