import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationChart

/-! # Cartesian comparison of chart relations

An endpoint-preserving morphism induces a morphism between compatible charts.
If the original morphism is cartesian and the square of chart objects is a
pullback, then the induced relation morphism is cartesian as well.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Chart

variable {E F : EtaleEquivalenceRelation.{u}}
  {f : E.U ⟶ F.U} {g : E.R ⟶ F.R}
  {V W : Scheme.{u}} (a : V ⟶ E.U) (b : W ⟶ F.U) (k : V ⟶ W)
  (ht : g ≫ F.t = E.t ≫ f) (hs : g ≫ F.s = E.s ≫ f)
  (w : a ≫ f = k ≫ b)

/-- The map on arrows induced by an endpoint-preserving morphism and a
commuting square of chart objects. -/
noncomputable def hom : arrows E a ⟶ arrows F b :=
  lift F b (t E a ≫ k) (s E a ≫ k) (map E a ≫ g)
    (by rw [Category.assoc, ht, ← Category.assoc, map_t,
      Category.assoc, w, ← Category.assoc])
    (by rw [Category.assoc, hs, ← Category.assoc, map_s,
      Category.assoc, w, ← Category.assoc])

@[reassoc (attr := simp)]
lemma hom_t : hom a b k ht hs w ≫ t F b = t E a ≫ k := by
  exact lift_t _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma hom_s : hom a b k ht hs w ≫ s F b = s E a ≫ k := by
  exact lift_s _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma hom_map : hom a b k ht hs w ≫ map F b = map E a ≫ g := by
  exact lift_map _ _ _ _ _ _ _

variable {a b k}

/-- Restricting a cartesian morphism to pullback chart objects preserves the
source pullback square. -/
lemma isPullback_hom_s (h : IsCartesianHom E F f g)
    (hv : IsPullback a k f b) :
    IsPullback (hom a b k h.1 h.2.w hv.w) (s E a) (s F b) k := by
  refine IsPullback.mk' (hom_s _ _ _ _ _ _) ?_ ?_
  · intro T x y hx hxy
    have hr : x ≫ map E a = y ≫ map E a := by
      apply h.2.hom_ext
      · simpa only [Category.assoc, hom_map] using
          congrArg (fun z => z ≫ map F b) hx
      · simpa only [Category.assoc, map_s] using
          congrArg (fun z => z ≫ a) hxy
    apply hom_ext E a
    · apply hv.hom_ext
      · simpa only [Category.assoc, map_t] using
          congrArg (fun z => z ≫ E.t) hr
      · simpa only [Category.assoc, hom_t] using
          congrArg (fun z => z ≫ t F b) hx
    · exact hxy
  · intro T r₀ v hw
    have hrw : (r₀ ≫ map F b) ≫ F.s = (v ≫ a) ≫ f := by
      calc
        (r₀ ≫ map F b) ≫ F.s = (r₀ ≫ s F b) ≫ b := by
          rw [Category.assoc, map_s, ← Category.assoc]
        _ = (v ≫ k) ≫ b := by rw [hw]
        _ = (v ≫ a) ≫ f := by rw [Category.assoc, ← hv.w, ← Category.assoc]
    let r : T ⟶ E.R := h.2.lift (r₀ ≫ map F b) (v ≫ a) hrw
    have hrg : r ≫ g = r₀ ≫ map F b := h.2.lift_fst _ _ _
    have hrs : r ≫ E.s = v ≫ a := h.2.lift_snd _ _ _
    have huw : (r ≫ E.t) ≫ f = (r₀ ≫ t F b) ≫ b := by
      calc
        (r ≫ E.t) ≫ f = (r ≫ g) ≫ F.t := by
          rw [Category.assoc, ← h.1, ← Category.assoc]
        _ = (r₀ ≫ map F b) ≫ F.t := by rw [hrg]
        _ = (r₀ ≫ t F b) ≫ b := by
          rw [Category.assoc, map_t, ← Category.assoc]
    let v' : T ⟶ V := hv.lift (r ≫ E.t) (r₀ ≫ t F b) huw
    have hv'a : v' ≫ a = r ≫ E.t := hv.lift_fst _ _ _
    have hv'k : v' ≫ k = r₀ ≫ t F b := hv.lift_snd _ _ _
    let l := lift E a v' v r hv'a.symm hrs
    refine ⟨l, ?_, lift_s _ _ _ _ _ _ _⟩
    apply hom_ext F b
    · simp only [Category.assoc, hom_t, lift_t_assoc, l, hv'k]
    · simp only [Category.assoc, hom_s, lift_s_assoc, l, ← hw]

/-- Cartesian morphisms restrict to cartesian morphisms of étale charts
whose object square is a pullback. -/
lemma isCartesianHom [Etale a] [Etale b] (h : IsCartesianHom E F f g)
    (hv : IsPullback a k f b) :
    IsCartesianHom (E.chart a) (F.chart b) k (hom a b k h.1 h.2.w hv.w) :=
  ⟨hom_t _ _ _ _ _ _, isPullback_hom_s h hv⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Chart
