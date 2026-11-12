import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyFunctorial
import Langlands.AlgebraicGeometry.PointTopology.SchemeFiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Finite products for the etale-chart point topology

A full-presheaf limiting fan of quasi-separated algebraic spaces locally of
finite type induces the product topology on rational points over a henselian
nontrivially normed field.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest schemePointTopology IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

namespace FiniteProductCharts

private theorem overBinaryProduct_property
    {C : Type*} [Category C] [HasFiniteLimits C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {S : C} (X Y : Over S) (hX : P X.hom) (hY : P Y.hom) :
    P (X ⨯ Y).hom := by
  have hp : P (prod.fst : X ⨯ Y ⟶ X).left :=
    P.of_isPullback
      (Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) (prodIsProd X Y)).flip hY
  simpa only [Over.w] using P.comp_mem _ _ hp hX

/-- Stable structural properties of relative schemes are preserved by
finite products. -/
theorem overFiniteProduct_property
    {C : Type*} [Category C] [HasFiniteLimits C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    [P.ContainsIdentities] [P.RespectsIso]
    {S : C} {ι : Type*} [Finite ι] (U : ι → Over S) (hU : ∀ i, P (U i).hom) :
    P (∏ᶜ U).hom := by
  let Q : ObjectProperty (Over S) := P.overObj
  have : Q.IsClosedUnderBinaryProducts := {
    limitsOfShape_le := by
      rintro X ⟨p⟩
      exact Q.prop_of_iso
        (IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
          ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
        (overBinaryProduct_property P _ _
          (p.prop_diag_obj ⟨.left⟩) (p.prop_diag_obj ⟨.right⟩)) }
  have : Q.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := {
    limitsOfShape_le := by
      rintro X ⟨p⟩
      have hX : IsTerminal X :=
        (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
          (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
      exact Q.prop_of_iso (Over.mkIdTerminal.uniqueUpToIso hX) (P.id_mem S) }
  have : Q.IsClosedUnderFiniteProducts := .mk'
  exact Q.prop_product hU

/-- A finite product of schemes locally of finite type over the fixed base
is locally of finite type. -/
theorem locallyOfFiniteType_pi {S : Scheme.{u}} {ι : Type u} [Finite ι]
    (U : ι → Over S) [∀ i, LocallyOfFiniteType (U i).hom] :
    LocallyOfFiniteType (∏ᶜ U).hom := by
  have : MorphismProperty.ContainsIdentities
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) := ⟨fun _ => inferInstance⟩
  have : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  exact overFiniteProduct_property (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    U (fun _ => inferInstance)

end FiniteProductCharts

section Points

variable {K : Type u} [Field K] {ι : Type u}
  {W : AlgebraicSpace (Spec (CommRingCat.of K))}
  (X : ι → AlgebraicSpace (Spec (CommRingCat.of K)))
  (π : ∀ i, W ⟶ X i)
  (h : IsLimit (Fan.mk W.presheaf (fun i => hom (π i))))

include h

/-- A full-presheaf product fan gives the actual rational point equivalence. -/
def finiteProductSpacePointsEquiv :
    RingPoints K W K ≃ (∀ i, RingPoints K (X i) K) := by
  let E := (evaluation (Over (Spec (CommRingCat.of K)))ᵒᵖ
    (Type (u + 1))).obj (op (ringTest K K))
  let hp := isLimitFanMkObjOfIsLimit E (fun i => (X i).presheaf) (fun i => hom (π i)) h
  exact (IsLimit.conePointUniqueUpToIso hp
    (Types.productLimitCone.{u, u + 1} (fun i => RingPoints K (X i) K)).isLimit).toEquiv

/-- The point equivalence uses exactly the specified space projections. -/
@[simp]
theorem finiteProductSpacePointsEquiv_apply (w : RingPoints K W K) (i : ι) :
    finiteProductSpacePointsEquiv X π h w i = RingPoints.map (π i) w := by
  let E := (evaluation (Over (Spec (CommRingCat.of K)))ᵒᵖ
    (Type (u + 1))).obj (op (ringTest K K))
  let hp := isLimitFanMkObjOfIsLimit E (fun i => (X i).presheaf) (fun i => hom (π i)) h
  exact ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp hp
      (Types.productLimitCone.{u, u + 1} (fun i => RingPoints K (X i) K)).isLimit ⟨i⟩) w

end Points

section Topology

variable {K : Type u} [NontriviallyNormedField K] {ι : Type u} [Finite ι]
  {W : AlgebraicSpace (Spec (CommRingCat.of K))}
  (X : ι → AlgebraicSpace (Spec (CommRingCat.of K)))
  (π : ∀ i, W ⟶ X i)
  (h : IsLimit (Fan.mk W.presheaf (fun i => hom (π i))))

include h

/-- A finite full-presheaf product is a product for the independently
constructed etale-chart topologies on rational points. -/
def finiteProductSpacePointHomeomorph
    (hK : IsHenselianValuedField K)
    (hW : IsQuasiSeparatedLocallyFiniteType K W)
    (hX : ∀ i, IsQuasiSeparatedLocallyFiniteType K (X i)) :
    letI : TopologicalSpace (RingPoints K W K) := etaleChartTopology K W
    letI : ∀ i, TopologicalSpace (RingPoints K (X i) K) :=
      fun i => etaleChartTopology K (X i)
    RingPoints K W K ≃ₜ (∀ i, RingPoints K (X i) K) := by
  classical
  let : TopologicalSpace (RingPoints K W K) := etaleChartTopology K W
  let (i : ι) : TopologicalSpace (RingPoints K (X i) K) := etaleChartTopology K (X i)
  let E := finiteProductSpacePointsEquiv X π h
  have hforward : Continuous E := by
    apply continuous_pi
    intro i
    exact continuous_ringPointsMap hK (hX i) (π i)
  let C := ∀ i, EtaleFiniteTypeChart K (X i)
  let Q (c : C) (p : ∀ i, RingPoint K (c i).scheme K) : ∀ i, RingPoints K (X i) K :=
    fun i => (c i).pointMap (p i)
  have hcont : ∀ c : C,
      letI : ∀ i, TopologicalSpace (RingPoint K (c i).scheme K) :=
        fun i => schemePointTopology K (c i).scheme K
      Continuous (E.symm ∘ Q c) := by
    intro c
    let U : ι → Over (Spec (CommRingCat.of K)) := fun i => (c i).scheme
    have : ∀ i, LocallyOfFiniteType (U i).hom := fun i => (c i).locallyOfFiniteType
    have := FiniteProductCharts.locallyOfFiniteType_pi U
    let (i : ι) : TopologicalSpace (RingPoint K (U i) K) :=
      schemePointTopology K (U i) K
    let : TopologicalSpace (RingPoint K (∏ᶜ U) K) := schemePointTopology K (∏ᶜ U) K
    let : TopologicalSpace (RingPoint K (limit.cone (Discrete.functor U)).pt K) :=
      schemePointTopology K (limit.cone (Discrete.functor U)).pt K
    let ρ : (schemeYoneda _).obj (∏ᶜ U) ⟶ W.presheaf :=
      h.lift (Fan.mk ((schemeYoneda _).obj (∏ᶜ U)) (fun i =>
        (schemeYoneda _).map (Pi.π U i) ≫ hom (c i).hom))
    let H := PointTopology.schemeFiniteProductPointHomeomorph K K U
      (limit.cone (Discrete.functor U)) (limit.isLimit (Discrete.functor U))
    have hρ (q : RingPoint K (∏ᶜ U) K) (i : ι) :
        E (schemePointsMap ρ q) i = (c i).pointMap (q ≫ Pi.π U i) := by
      rw [finiteProductSpacePointsEquiv_apply]
      exact congrArg (fun f => f.app (op (ringTest K K)) (ULift.up q))
        (h.fac (Fan.mk ((schemeYoneda _).obj (∏ᶜ U)) (fun i =>
          (schemeYoneda _).map (Pi.π U i) ≫ hom (c i).hom)) ⟨i⟩)
    have heq : E.symm ∘ Q c = schemePointsMap ρ ∘ H.symm := by
      funext p
      apply E.injective
      funext i
      rw [Function.comp_apply, Equiv.apply_symm_apply, Function.comp_apply, hρ]
      have hp := congrFun (H.apply_symm_apply p) i
      rw [PointTopology.schemeFiniteProductPointHomeomorph_apply] at hp
      exact congrArg (c i).pointMap hp.symm
    rw [heq]
    exact (continuous_schemePointsMap hK hW.exists_chart ρ).comp H.symm.continuous
  have hcov : ∀ y : ∀ i, RingPoints K (X i) K,
      ∃ (c : C) (p : ∀ i, RingPoint K (c i).scheme K), Q c p = y := by
    intro y
    choose c p hp using fun i => (hX i).exists_chart (y i)
    exact ⟨c, p, funext hp⟩
  have hback : Continuous E.symm := by
    refine ⟨?_⟩
    intro V hV
    have heq : E.symm ⁻¹' V = ⋃ c : C, Q c '' ((E.symm ∘ Q c) ⁻¹' V) := by
      ext y
      constructor
      · intro hy
        obtain ⟨c, p, rfl⟩ := hcov y
        exact Set.mem_iUnion.2 ⟨c, p, hy, rfl⟩
      · intro hy
        obtain ⟨c, p, hp, rfl⟩ := Set.mem_iUnion.1 hy
        exact hp
    rw [heq]
    apply isOpen_iUnion
    intro c
    let (i : ι) : TopologicalSpace (RingPoint K (c i).scheme K) :=
      schemePointTopology K (c i).scheme K
    have hopen : IsOpenMap (Q c) :=
      IsOpenMap.piMap (fun i => (c i).isOpenMap_pointMap hK)
        (Filter.eventually_cofinite.2 (Set.toFinite _))
    exact hopen _ ((hcont c).isOpen_preimage V hV)
  exact Homeomorph.mk E hforward hback

/-- The topological comparison retains all of the specified original
space projections. -/
@[simp]
theorem finiteProductSpacePointHomeomorph_apply
    (hK : IsHenselianValuedField K)
    (hW : IsQuasiSeparatedLocallyFiniteType K W)
    (hX : ∀ i, IsQuasiSeparatedLocallyFiniteType K (X i))
    (w : RingPoints K W K) (i : ι) :
    finiteProductSpacePointHomeomorph X π h hK hW hX w i = RingPoints.map (π i) w :=
  finiteProductSpacePointsEquiv_apply X π h w i

end Topology

end Langlands.AlgebraicGeometry.AlgebraicSpace
