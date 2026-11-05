import Langlands.GroupScheme.SplitExistence.RationalProducts
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Containment of closed subschemes detected on geometric points

Over an arbitrary field `k`, every closed point of a scheme locally of finite type over `k`
is the image of a point with values in any algebraically closed extension `K` of `k`. Hence a
morphism from a reduced scheme locally of finite type factors through a closed immersion as soon
as all its `K`-valued points do. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]

/-- Every closed point of a scheme locally of finite type over `k` is the image of a
`K`-valued point. -/
theorem exists_extPoint_apply {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]
    (x : X.left) (hx : IsClosed {x}) :
    ∃ q : extPoint K ⟶ X, q.left (IsLocalRing.closedPoint K) = x := by
  have : IsClosedImmersion (X.left.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.1 hx
  have hfin : IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.fromSpecResidueField x ≫ X.hom)
  rw [← hφ, IsFinite.SpecMap_iff] at hfin
  let : Algebra k (X.left.residueField x) := φ.hom.toAlgebra
  have : Module.Finite k (X.left.residueField x) := hfin
  have : Algebra.IsAlgebraic k (X.left.residueField x) := inferInstance
  let ψ : X.left.residueField x →ₐ[k] K := IsAlgClosed.lift
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    X.left.fromSpecResidueField x) ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.left.fromSpecResidueField x) ≫ X.hom =
      extMap K
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext a
    exact ψ.commutes a
  · change X.left.fromSpecResidueField x _ = x
    exact Scheme.fromSpecResidueField_apply x _

/-- A morphism from a reduced scheme locally of finite type over `k` factors through a closed
immersion if all its `K`-valued points do. -/
theorem exists_factor_of_extPoints {X Y Z : Over (Spec (CommRingCat.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) (g : Z ⟶ Y) [IsClosedImmersion g.left]
    (h : ∀ x : extPoint K ⟶ X, ∃ z : extPoint K ⟶ Z, z ≫ g = x ≫ f) :
    ∃ a : X ⟶ Z, a ≫ g = f := by
  let p := pullback.fst f.left g.left
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hpclosed : IsClosed (Set.range p) := p.isClosedEmbedding.isClosed_range
  have hppts : closedPoints X.left ⊆ Set.range p := by
    intro x hx
    obtain ⟨q, hq⟩ := exists_extPoint_apply K x hx
    obtain ⟨z, hz⟩ := h q
    rw [Scheme.Pullback.range_fst]
    refine ⟨z.left (IsLocalRing.closedPoint K), ?_⟩
    have he := congrArg (fun r : extPoint K ⟶ Y => r.left (IsLocalRing.closedPoint K)) hz
    change g.left (z.left _) = f.left (q.left _) at he
    rw [he, hq]
  have hprange : Set.range p = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← closure_closedPoints (X := X.left)]
    exact closure_minimal hppts hpclosed
  have : Surjective p := ⟨Set.range_eq_univ.mp hprange⟩
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let a := inv p ≫ pullback.snd f.left g.left
  have ha : a ≫ g.left = f.left := by
    dsimp [a]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
  rw [← Over.w g, ← Category.assoc, ha]
  exact Over.w f

/-- Containment of a reduced subgroup in a closed subgroup is detected on `K`-valued points. -/
theorem range_le_of_extPoints {G H B : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}
    {j : B ⟶ G} [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom] (hj : IsClosedSubgroup j)
    (h : ∀ x : extPoint K ⟶ H.X, ∃ z : extPoint K ⟶ B.X, z ≫ j.hom.hom = x ≫ i.hom.hom) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range j := by
  have : IsClosedImmersion j.hom.hom.left := hj
  obtain ⟨a, ha⟩ := exists_factor_of_extPoints K i.hom.hom j.hom.hom h
  rintro T x ⟨y, rfl⟩
  change T ⟶ H.X at y
  refine ⟨y ≫ a, ?_⟩
  change (y ≫ a) ≫ j.hom.hom = y ≫ i.hom.hom
  rw [Category.assoc, ha]

/-- Two morphisms from a reduced scheme locally of finite type over `k` to a separated scheme
agree if they agree on all `K`-valued points. -/
theorem ext_of_extPoints {X Y : Over (Spec (CommRingCat.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [IsSeparated Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : extPoint K ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply Over.OverMorphism.ext
  obtain ⟨fl, hfl⟩ : ∃ fl : X.left ⟶ Y.left, fl = f.left := ⟨_, rfl⟩
  obtain ⟨gl, hgl⟩ : ∃ gl : X.left ⟶ Y.left, gl = g.left := ⟨_, rfl⟩
  rw [← hfl, ← hgl]
  have hdom : IsDominant (equalizer.ι fl gl) := by
    refine ⟨Dense.mono ?_ (dense_iff_closure_eq.2 closure_closedPoints)⟩
    intro x hx
    obtain ⟨q, hq⟩ := exists_extPoint_apply K x hx
    have hqe : q.left ≫ fl = q.left ≫ gl := by
      rw [hfl, hgl]
      exact congrArg CommaMorphism.left (h q)
    obtain ⟨p, hp⟩ : ∃ p : (extPoint K).left, q.left p = x := ⟨_, hq⟩
    refine ⟨equalizer.lift q.left hqe p, ?_⟩
    rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, hp]
  exact ext_of_isDominant_of_isSeparated Y.hom (by rw [hfl, hgl, Over.w f, Over.w g])
    (equalizer.ι fl gl) (equalizer.condition _ _)

end Langlands.GroupScheme.SplitExistence
