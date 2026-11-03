import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Pullback of concrete ordinary-open affinoid sections -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.OpenSections

open CategoryTheory TopologicalSpace Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem arrow_unique {d e : RationalChart K B} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance f g

private theorem finite_gluing {d : RationalChart K B} {n : ℕ}
    (D : Fin n → RationalChart K B) (f : ∀ i, D i ⟶ d)
    (hc : ∀ x ∈ d.locus, ∃ i, x ∈ (D i).locus)
    (s : ∀ i, (D i).algebra)
    (hs : ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
      (interRight (D i) (D j)).restriction (s j)) :
    ∃! a : d.algebra, ∀ i, (f i).restriction a = s i := by
  obtain ⟨a, ha, hu⟩ := finiteRationalGluing K B d (ULift.{u} (Fin n))
    (fun i => D i.down) (fun i => f i.down)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := hc x hx
      exact ⟨⟨i⟩, hi⟩)
    (fun i => s i.down) (fun i j => hs i.down j.down)
  exact ⟨a, fun i => ha ⟨i⟩, fun b hb => hu b (fun i => hb i.down)⟩

private theorem finite_ext {d : RationalChart K B} {n : ℕ}
    (D : Fin n → RationalChart K B) (f : ∀ i, D i ⟶ d)
    (hc : ∀ x ∈ d.locus, ∃ i, x ∈ (D i).locus)
    {a b : d.algebra} (hab : ∀ i, (f i).restriction a = (f i).restriction b) :
    a = b := by
  have hs : ∀ i j,
      (interLeft (D i) (D j)).restriction ((f i).restriction a) =
        (interRight (D i) (D j)).restriction ((f j).restriction a) := by
    intro i j
    exact congrArg (fun h : (D i).inter (D j) ⟶ d => h.restriction a)
      (arrow_unique (interLeft (D i) (D j) ≫ f i) (interRight (D i) (D j) ≫ f j))
  obtain ⟨z, _, hz⟩ := finite_gluing D f hc (fun i => (f i).restriction a) hs
  exact (hz a (fun _ => rfl)).trans (hz b (fun i => (hab i).symm)).symm

/-- Refine an actual target rational chart by preimages of source rational
interior neighborhoods contained in the specified ordinary open. -/
def pullbackRefinement (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' (U : Set _))) :
    FiniteOpenRefinement e.val
      (fun d : ChartIn (U : Set _) =>
        {x : e.val.locus | BanachSpectrum.comap φ.toBoundedRingHom x.val ∈
          interior d.val.locus}) :=
  FiniteOpenRefinement.ofOpenCover e.val _
    (fun d => isOpen_interior.preimage
      ((BanachSpectrum.comapContinuous φ.toBoundedRingHom).continuous.comp
        continuous_subtype_val))
    (by
      intro x
      obtain ⟨d, hd, hsub⟩ := exists_rational_neighborhood
        (BanachSpectrum.comap φ.toBoundedRingHom x.val) (U : Set _)
        (U.isOpen.mem_nhds (e.property x.property))
      exact ⟨⟨d, hsub⟩, mem_interior_iff_mem_nhds.mpr hd⟩)

/-- Every chosen refinement component has its actual bounded map to the
pulled-back source quotient. -/
def pullbackRefinementMap (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' (U : Set _)))
    (i : Fin (pullbackRefinement φ U e).size) :
    (pullbackRefinement φ U e).chart i ⟶
      RationalChart.pullback φ ((pullbackRefinement φ U e).label i).val :=
  restrictionOfSubset _ _ (by
    rw [pullback_locus]
    intro x hx
    have hi : BanachSpectrum.comap φ.toBoundedRingHom x ∈
        interior ((pullbackRefinement φ U e).label i).val.locus :=
      (pullbackRefinement φ U e).subordinate_point i x hx
    change BanachSpectrum.comap φ.toBoundedRingHom x ∈
      ((pullbackRefinement φ U e).label i).val.locus
    exact interior_subset hi)

private theorem transported_restriction (φ : BoundedAlgHom K A B)
    {U : Set (BanachSpectrum A)} (s : Sections U)
    {d e : ChartIn U} (h : d.val ⟶ e.val) {w : RationalChart K B}
    (f : w ⟶ RationalChart.pullback φ d.val)
    (g : w ⟶ RationalChart.pullback φ e.val) :
    g.restriction (pullbackMap φ e.val (s.val e)) =
      f.restriction (pullbackMap φ d.val (s.val d)) := by
  rw [arrow_unique g (f ≫ pullbackRestriction φ h)]
  change f.restriction ((pullbackRestriction φ h).restriction
    (pullbackMap φ e.val (s.val e))) = _
  have hn := congrArg (fun k : BoundedAlgHom K e.val.algebra
    (RationalChart.pullback φ d.val).algebra => k.toAlgHom (s.val e))
      (pullbackRestriction_comp_pullbackMap φ h)
  change (pullbackRestriction φ h).restriction (pullbackMap φ e.val (s.val e)) =
    pullbackMap φ d.val (h.restriction (s.val e)) at hn
  exact congrArg (fun a => f.restriction a)
    (hn.trans (congrArg (fun a => pullbackMap φ d.val a) (s.property d e h)))

private theorem transported_compatible (φ : BoundedAlgHom K A B)
    {U : Set (BanachSpectrum A)} (s : Sections U)
    (d e : ChartIn U) (w : RationalChart K B)
    (f : w ⟶ RationalChart.pullback φ d.val)
    (g : w ⟶ RationalChart.pullback φ e.val) :
    f.restriction (pullbackMap φ d.val (s.val d)) =
      g.restriction (pullbackMap φ e.val (s.val e)) := by
  let t : ChartIn U :=
    ⟨d.val.inter e.val, (interLeft d.val e.val).subset.trans d.property⟩
  let q : w ⟶ RationalChart.pullback φ t.val :=
    restrictionOfSubset _ _ (by
      rw [pullback_locus, show t.val = d.val.inter e.val from rfl, locus_inter]
      intro x hx
      have hf := f.subset hx
      have hg := g.subset hx
      rw [pullback_locus] at hf hg
      exact ⟨hf, hg⟩)
  exact (transported_restriction φ s (interLeft d.val e.val) q f).trans
    (transported_restriction φ s (interRight d.val e.val) q g).symm

private def refinementValue (φ : BoundedAlgHom K A B)
    {U : Opens (BanachSpectrum A)} (s : Sections (U : Set (BanachSpectrum A)))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' (U : Set (BanachSpectrum A))))
    (i : Fin (pullbackRefinement φ U e).size) :
    ((pullbackRefinement φ U e).chart i).algebra :=
  (pullbackRefinementMap φ U e i).restriction
    (pullbackMap φ ((pullbackRefinement φ U e).label i).val
      (s.val ((pullbackRefinement φ U e).label i)))

private theorem refinementValue_compatible (φ : BoundedAlgHom K A B)
    {U : Opens (BanachSpectrum A)} (s : Sections (U : Set (BanachSpectrum A)))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' (U : Set (BanachSpectrum A)))) :
    ∀ i j,
      (interLeft ((pullbackRefinement φ U e).chart i)
        ((pullbackRefinement φ U e).chart j)).restriction (refinementValue φ s e i) =
      (interRight ((pullbackRefinement φ U e).chart i)
        ((pullbackRefinement φ U e).chart j)).restriction (refinementValue φ s e j) := by
  intro i j
  exact transported_compatible φ s _ _ _
    (interLeft _ _ ≫ pullbackRefinementMap φ U e i)
    (interRight _ _ ≫ pullbackRefinementMap φ U e j)

/-- Pull back a section to one actual rational target algebra by finite
descent of its actual quotient transports. -/
def pullbackElement (φ : BoundedAlgHom K A B)
    {U : Opens (BanachSpectrum A)} (s : Sections (U : Set (BanachSpectrum A)))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' (U : Set (BanachSpectrum A)))) :
    e.val.algebra :=
  (finite_gluing (pullbackRefinement φ U e).chart (pullbackRefinement φ U e).map
    (pullbackRefinement φ U e).covers (refinementValue φ s e)
    (refinementValue_compatible φ s e)).choose

private theorem pullbackElement_refinement (φ : BoundedAlgHom K A B)
    {U : Opens (BanachSpectrum A)} (s : Sections (U : Set (BanachSpectrum A)))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' (U : Set (BanachSpectrum A))))
    (i : Fin (pullbackRefinement φ U e).size) :
    ((pullbackRefinement φ U e).map i).restriction (pullbackElement φ s e) =
      refinementValue φ s e i :=
  (finite_gluing (pullbackRefinement φ U e).chart (pullbackRefinement φ U e).map
    (pullbackRefinement φ U e).covers (refinementValue φ s e)
    (refinementValue_compatible φ s e)).choose_spec.1 i

/-- On every actual target subchart mapping into a source chart, pullback
agrees with the bounded transport of that source component. -/
theorem pullbackElement_local (φ : BoundedAlgHom K A B)
    {U : Opens (BanachSpectrum A)} (s : Sections (U : Set (BanachSpectrum A)))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' (U : Set (BanachSpectrum A))))
    (d : ChartIn (U : Set (BanachSpectrum A))) (w : RationalChart K B)
    (f : w ⟶ e.val) (g : w ⟶ RationalChart.pullback φ d.val) :
    f.restriction (pullbackElement φ s e) =
      g.restriction (pullbackMap φ d.val (s.val d)) := by
  let c := pullbackRefinement φ U e
  apply finite_ext (fun i => w.inter (c.chart i))
    (fun i => interLeft w (c.chart i)) (by
      intro x hx
      obtain ⟨i, hi⟩ := c.covers x (f.subset hx)
      exact ⟨i, (locus_inter w (c.chart i)).symm ▸ ⟨hx, hi⟩⟩)
  intro i
  calc
    (interLeft w (c.chart i)).restriction
        (f.restriction (pullbackElement φ s e)) =
      (interRight w (c.chart i)).restriction
        ((c.map i).restriction (pullbackElement φ s e)) :=
      congrArg (fun h : w.inter (c.chart i) ⟶ e.val =>
        h.restriction (pullbackElement φ s e))
        (arrow_unique (interLeft w (c.chart i) ≫ f)
          (interRight w (c.chart i) ≫ c.map i))
    _ = (interRight w (c.chart i)).restriction (refinementValue φ s e i) :=
      congrArg (fun a => (interRight w (c.chart i)).restriction a)
        (pullbackElement_refinement φ s e i)
    _ = (interLeft w (c.chart i)).restriction
        (g.restriction (pullbackMap φ d.val (s.val d))) :=
      transported_compatible φ s (c.label i) d (w.inter (c.chart i))
        (interRight w (c.chart i) ≫ pullbackRefinementMap φ U e i)
        (interLeft w (c.chart i) ≫ g)

/-- The descended target elements form a compatible family under every
actual bounded rational restriction. -/
theorem pullbackElement_restriction (φ : BoundedAlgHom K A B)
    {U : Opens (BanachSpectrum A)} (s : Sections (U : Set (BanachSpectrum A)))
    (d e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
      (U : Set (BanachSpectrum A)))) (h : d.val ⟶ e.val) :
    h.restriction (pullbackElement φ s e) = pullbackElement φ s d := by
  let c := pullbackRefinement φ U d
  apply finite_ext c.chart c.map c.covers
  intro i
  exact (pullbackElement_local φ s e (c.label i) (c.chart i)
    (c.map i ≫ h) (pullbackRefinementMap φ U d i)).trans
    (pullbackElement_refinement φ s d i).symm

private def refinementHom (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
      (U : Set (BanachSpectrum A))))
    (i : Fin (pullbackRefinement φ U e).size) :
    Sections (U : Set (BanachSpectrum A)) →ₐ[K]
      ((pullbackRefinement φ U e).chart i).algebra :=
  (pullbackRefinementMap φ U e i).restriction.toAlgHom.comp
    ((pullbackMap φ ((pullbackRefinement φ U e).label i).val).toAlgHom.comp
      (evaluation (U : Set (BanachSpectrum A)) ((pullbackRefinement φ U e).label i)))

/-- Finite separation proves the algebra laws for the descended element. -/
def pullbackElementHom (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
      (U : Set (BanachSpectrum A)))) :
    Sections (U : Set (BanachSpectrum A)) →ₐ[K] e.val.algebra where
  toFun s := pullbackElement φ s e
  map_zero' := by
    apply finite_ext (pullbackRefinement φ U e).chart
      (pullbackRefinement φ U e).map (pullbackRefinement φ U e).covers
    intro i
    rw [pullbackElement_refinement,
      map_zero ((pullbackRefinement φ U e).map i).restriction.toAlgHom]
    exact map_zero (refinementHom φ U e i)
  map_one' := by
    apply finite_ext (pullbackRefinement φ U e).chart
      (pullbackRefinement φ U e).map (pullbackRefinement φ U e).covers
    intro i
    rw [pullbackElement_refinement,
      map_one ((pullbackRefinement φ U e).map i).restriction.toAlgHom]
    exact map_one (refinementHom φ U e i)
  map_add' s t := by
    apply finite_ext (pullbackRefinement φ U e).chart
      (pullbackRefinement φ U e).map (pullbackRefinement φ U e).covers
    intro i
    rw [map_add ((pullbackRefinement φ U e).map i).restriction.toAlgHom,
      pullbackElement_refinement, pullbackElement_refinement, pullbackElement_refinement]
    exact map_add (refinementHom φ U e i) s t
  map_mul' s t := by
    apply finite_ext (pullbackRefinement φ U e).chart
      (pullbackRefinement φ U e).map (pullbackRefinement φ U e).covers
    intro i
    rw [map_mul ((pullbackRefinement φ U e).map i).restriction.toAlgHom,
      pullbackElement_refinement, pullbackElement_refinement, pullbackElement_refinement]
    exact map_mul (refinementHom φ U e i) s t
  commutes' a := by
    apply finite_ext (pullbackRefinement φ U e).chart
      (pullbackRefinement φ U e).map (pullbackRefinement φ U e).covers
    intro i
    rw [pullbackElement_refinement,
      ((pullbackRefinement φ U e).map i).restriction.toAlgHom.commutes]
    exact (refinementHom φ U e i).commutes a

/-- The actual pullback algebra homomorphism on concrete ordinary-open
compatible-family sections. -/
def pullback (φ : BoundedAlgHom K A B) (U : Opens (BanachSpectrum A)) :
    Sections (U : Set (BanachSpectrum A)) →ₐ[K]
      Sections (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
        (U : Set (BanachSpectrum A))) :=
  (AlgHom.pi (pullbackElementHom φ U)).codRestrict (compatibleAlgebra _)
    (fun s => pullbackElement_restriction φ s)

@[simp]
theorem pullback_apply (φ : BoundedAlgHom K A B) (U : Opens (BanachSpectrum A))
    (s : Sections (U : Set (BanachSpectrum A)))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
      (U : Set (BanachSpectrum A)))) :
    (pullback φ U s).val e = pullbackElement φ s e := rfl

/-- The constructed pullback is characterized on every actual rational
quotient lying over a source chart. -/
theorem pullback_local (φ : BoundedAlgHom K A B) (U : Opens (BanachSpectrum A))
    (s : Sections (U : Set (BanachSpectrum A)))
    (e : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
      (U : Set (BanachSpectrum A))))
    (d : ChartIn (U : Set (BanachSpectrum A)))
    (g : e.val ⟶ RationalChart.pullback φ d.val) :
    (pullback φ U s).val e = g.restriction (pullbackMap φ d.val (s.val d)) :=
  pullbackElement_local φ s e d e.val (𝟙 _) g

/-- Pullback commutes with restriction along every inclusion of ordinary
opens of the actual source spectrum. -/
theorem pullback_restriction (φ : BoundedAlgHom K A B)
    {U V : Opens (BanachSpectrum A)}
    (h : (U : Set (BanachSpectrum A)) ⊆ (V : Set (BanachSpectrum A))) :
    (restriction (Set.preimage_mono h)).comp (pullback φ V) =
      (pullback φ U).comp (restriction h) := by
  apply AlgHom.ext
  intro s
  apply ext
  intro e
  let e' : ChartIn (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
      (V : Set (BanachSpectrum A))) :=
    ⟨e.val, e.property.trans (Set.preimage_mono h)⟩
  change pullbackElement φ s e' = pullbackElement φ (restriction h s) e
  let c := pullbackRefinement φ U e
  apply finite_ext c.chart c.map c.covers
  intro i
  exact (pullbackElement_local φ s e'
    ⟨(c.label i).val, (c.label i).property.trans h⟩ (c.chart i)
    (c.map i) (pullbackRefinementMap φ U e i)).trans
    (pullbackElement_refinement φ (restriction h s) e i).symm

@[simp]
theorem pullback_fromBase (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A)) (a : A) :
    pullback φ U (fromBase (U : Set (BanachSpectrum A)) a) =
      fromBase (BanachSpectrum.comap φ.toBoundedRingHom ⁻¹'
        (U : Set (BanachSpectrum A))) (φ a) := by
  apply ext
  intro e
  change pullbackElement φ (fromBase (U : Set (BanachSpectrum A)) a) e =
    e.val.baseMap (φ a)
  let c := pullbackRefinement φ U e
  apply finite_ext c.chart c.map c.covers
  intro i
  rw [pullbackElement_refinement]
  change (pullbackRefinementMap φ U e i).restriction
    (pullbackMap φ (c.label i).val ((c.label i).val.baseMap a)) =
      (c.map i).restriction (e.val.baseMap (φ a))
  rw [pullbackMap_baseMap]
  exact congrArg (fun k : BoundedAlgHom K B (c.chart i).algebra => k (φ a))
    ((pullbackRefinementMap φ U e i).comp_baseMap.trans
      (c.map i).comp_baseMap.symm)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.OpenSections
