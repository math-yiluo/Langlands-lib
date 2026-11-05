import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceStatement
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.Torus.NormalizerSmoothProof
import Langlands.GroupScheme.Torus.MaximalDescent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation

/-! # Existence of the actual maximal-torus parameter scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace MaximalTorusParameterExistence

section Conjugation

variable {S : Scheme.{u}} {H G G' : GroupScheme S}

/-- Two points whose quotient normalizes a subgroup functor conjugate a given point
into it simultaneously. -/
theorem conj_mem_iff_of_inv_mul_mem_normalizer (F : SubgroupFunctor G) {W : Over S}
    {a₁ a₂ z : W ⟶ G.X} (hn : a₁⁻¹ * a₂ ∈ F.normalizer.carrier W) :
    a₁⁻¹ * z * a₁ ∈ F.carrier W ↔ a₂⁻¹ * z * a₂ ∈ F.carrier W := by
  have key : a₂⁻¹ * z * a₂ = (a₁⁻¹ * a₂)⁻¹ * (a₁⁻¹ * z * a₁) * (a₁⁻¹ * a₂) := by group
  rw [key]
  constructor
  · intro h
    simpa only [Category.id_comp] using (hn W (𝟙 W) _ h).2
  · intro h
    have h' := (hn W (𝟙 W) _ h).1
    simp only [Category.id_comp] at h'
    have e : (a₁⁻¹ * a₂) * ((a₁⁻¹ * a₂)⁻¹ * (a₁⁻¹ * z * a₁) * (a₁⁻¹ * a₂)) *
        (a₁⁻¹ * a₂)⁻¹ = a₁⁻¹ * z * a₁ := by group
    rwa [e] at h'

/-- Membership in the range of a homomorphism followed by an inner automorphism. -/
theorem mem_range_comp_innerIso_iff (f : H ⟶ G) (g : Over.mk (𝟙 S) ⟶ G.X) {V : Over S}
    (y : V ⟶ G.X) :
    y ∈ (SubgroupFunctor.range (f ≫ (G.innerIso g).hom)).carrier V ↔
      (G.constantPoint g V)⁻¹ * y * G.constantPoint g V ∈
        (SubgroupFunctor.range f).carrier V := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    group
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, ht]
    group

/-- Membership in the range of a homomorphism followed by an isomorphism. -/
theorem mem_range_comp_iso_iff (f : H ⟶ G) (e : G ≅ G') {V : Over S} (y : V ⟶ G'.X) :
    y ∈ (SubgroupFunctor.range (f ≫ e.hom)).carrier V ↔
      y ≫ e.inv.hom.hom ∈ (SubgroupFunctor.range f).carrier V := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom e.hom,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, ht, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

end Conjugation

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G : GroupScheme S}

/-- The structure map of a test scheme over `S'`, as a morphism of test schemes over `S`
to the base test object. -/
abbrev baseMap (V : Over S') :
    (Over.map b).obj V ⟶ (Over.map b).obj (Over.mk (𝟙 S')) :=
  (Over.map b).map (Over.homMk V.hom (by simp))

/-- The ground point of a constant family is the restricted ground point. -/
theorem baseChangePointsEquiv_constantPoint_eq
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) (V : Over S') :
    baseChangePointsEquiv b G V (((GroupScheme.baseChange b).obj G).constantPoint g V) =
      baseMap b V ≫ baseChangePointsEquiv b G _ g :=
  baseChangePointsEquiv_naturality b G _ g

/-- Membership in a conjugate of a base-changed range, expressed by ground points. -/
theorem mem_range_baseChange_comp_innerIso_iff {T : GroupScheme S} (j : T ⟶ G)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) {V : Over S'}
    (y : V ⟶ ((GroupScheme.baseChange b).obj G).X) :
    y ∈ (SubgroupFunctor.range ((GroupScheme.baseChange b).map j ≫
        (((GroupScheme.baseChange b).obj G).innerIso g).hom)).carrier V ↔
      (baseMap b V ≫ baseChangePointsEquiv b G _ g)⁻¹ * baseChangePointsEquiv b G V y *
          (baseMap b V ≫ baseChangePointsEquiv b G _ g) ∈
        (SubgroupFunctor.range j).carrier ((Over.map b).obj V) := by
  rw [mem_range_comp_innerIso_iff, SubgroupFunctor.range_baseChangeHom,
    SubgroupFunctor.mem_baseChange, map_mul, map_mul, map_inv,
    baseChangePointsEquiv_constantPoint_eq]

/-- Two base-changed points whose ground quotient normalizes a torus give the same
conjugate of the base-changed torus range. -/
theorem range_conj_eq_of_mem_torusNormalizer {T : CommGroupScheme S} (j : T.toGrp ⟶ G)
    (g₁ g₂ : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hn : (baseChangePointsEquiv b G _ g₁)⁻¹ * baseChangePointsEquiv b G _ g₂ ∈
      (torusNormalizer j).carrier ((Over.map b).obj (Over.mk (𝟙 S')))) :
    SubgroupFunctor.range ((GroupScheme.baseChange b).map j ≫
        (((GroupScheme.baseChange b).obj G).innerIso g₁).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange b).map j ≫
        (((GroupScheme.baseChange b).obj G).innerIso g₂).hom) := by
  ext V y
  rw [mem_range_baseChange_comp_innerIso_iff, mem_range_baseChange_comp_innerIso_iff]
  apply conj_mem_iff_of_inv_mul_mem_normalizer
  have h := (torusNormalizer j).comp_mem (baseMap b V) hn
  rwa [MonObj.comp_mul, GrpObj.comp_inv] at h

open Descent in
/-- A base-changed conjugate of a torus by a point lying over a ground parameter is
invariant on the fpqc overlap, when parameter fibers are normalizer cosets. -/
theorem overlap_range_eq {T : CommGroupScheme S} (j : T.toGrp ⟶ G) {Q : Over S}
    (q : G.X ⟶ Q)
    (hfib : ∀ (U : Over S) (a₁ a₂ : U ⟶ G.X), a₁ ≫ q = a₂ ≫ q →
      a₁⁻¹ * a₂ ∈ (torusNormalizer j).carrier U)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) (x : S ⟶ Q.left)
    (hg : g.left ≫ pullback.fst G.X.hom b ≫ q.left = b ≫ x) :
    SubgroupFunctor.range ((GroupScheme.baseChange (fst b)).map
        ((GroupScheme.baseChange b).map j ≫
          (((GroupScheme.baseChange b).obj G).innerIso g).hom) ≫
        (canonicalOverlap b G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd b)).map
        ((GroupScheme.baseChange b).map j ≫
          (((GroupScheme.baseChange b).obj G).innerIso g).hom)) := by
  ext V y
  rw [mem_range_comp_iso_iff, SubgroupFunctor.range_baseChangeHom,
    SubgroupFunctor.mem_baseChange, SubgroupFunctor.range_baseChangeHom,
    SubgroupFunctor.mem_baseChange, mem_range_baseChange_comp_innerIso_iff,
    mem_range_baseChange_comp_innerIso_iff]
  let w : (Over.map b).obj ((Over.map (snd b)).obj V) ≅
      (Over.map b).obj ((Over.map (fst b)).obj V) :=
    Over.isoMk (Iso.refl _) (by
      simp only [Over.map_obj_hom, Iso.refl_hom, Category.id_comp, Category.assoc]
      rw [pullback.condition])
  have transport : ∀ z : (Over.map b).obj ((Over.map (fst b)).obj V) ⟶ G.X,
      z ∈ (SubgroupFunctor.range j).carrier _ ↔
        w.hom ≫ z ∈ (SubgroupFunctor.range j).carrier _ := fun z =>
    ⟨fun h => (SubgroupFunctor.range j).comp_mem _ h, fun h => by
      simpa only [Iso.inv_hom_id_assoc] using (SubgroupFunctor.range j).comp_mem w.inv h⟩
  rw [transport, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
  have hinv : (canonicalOverlap b G).inv.hom.hom.left ≫
      (canonicalOverlap b G).hom.hom.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
    rfl
  have hZ : w.hom ≫ baseChangePointsEquiv b G _
      (baseChangePointsEquiv (fst b) ((GroupScheme.baseChange b).obj G) V
        (y ≫ (canonicalOverlap b G).inv.hom.hom)) =
      baseChangePointsEquiv b G _
        (baseChangePointsEquiv (snd b) ((GroupScheme.baseChange b).obj G) V y) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, baseChangePointsEquiv_left, w, Over.isoMk_hom_left,
      Iso.refl_hom, Category.id_comp, Category.assoc]
    rw [← canonicalOverlap_fst, reassoc_of% hinv]
  rw [hZ]
  apply conj_mem_iff_of_inv_mul_mem_normalizer
  apply hfib
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, baseChangePointsEquiv_left, w, Over.isoMk_hom_left,
    Iso.refl_hom, Category.id_comp, Category.assoc, Over.map_map_left, Over.homMk_left,
    Over.map_obj_hom]
  rw [hg, pullback.condition_assoc]

end BaseChange

/-- Parameter fibers contained in normalizer cosets give the ground-field torus
compatibility of the parameter map. -/
theorem conjugationCompatible_of_fiber {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} (j₀ : T₀.toGrp ⟶ G)
    (hT₀ : IsTorus T₀.toGrp) (hj₀ : IsClosedSubgroup j₀)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hfib : ∀ (U : Over (Spec (CommRingCat.of k))) (a₁ a₂ : U ⟶ G.X),
      a₁ ≫ q = a₂ ≫ q → a₁⁻¹ * a₂ ∈ (torusNormalizer j₀).carrier U) :
    TorusParameterConjugationCompatible j₀ q := by
  intro x
  have hleft : ∀ g : RationalPoint (AlgebraicClosure k)
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X,
      g ≫ (Over.pullback (toAlgebraicClosure k)).map q =
          geometricRationalPoint (K := AlgebraicClosure k) Q x →
        g.left ≫ pullback.fst G.X.hom (toAlgebraicClosure k) ≫ q.left =
          toAlgebraicClosure k ≫ x.left := by
    intro g hg
    have h := congrArg (fun z => z.left ≫ pullback.fst Q.hom (toAlgebraicClosure k)) hg
    simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst] at h
    rw [h]
    exact geometricRationalPoint_fst Q x
  by_cases hlift : ∃ g : RationalPoint (AlgebraicClosure k)
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X,
      g ≫ (Over.pullback (toAlgebraicClosure k)).map q =
        geometricRationalPoint (K := AlgebraicClosure k) Q x
  · obtain ⟨g, hg⟩ := hlift
    obtain ⟨hsurj, hflat, -⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
    let : Surjective (toAlgebraicClosure k) := hsurj
    let : Flat (toAlgebraicClosure k) := hflat
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have hi : IsClosedSubgroup ((GroupScheme.baseChange (toAlgebraicClosure k)).map j₀ ≫
        (((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).innerIso g).hom) :=
      (hj₀.baseChange (toAlgebraicClosure k)).comp_iso _
    obtain ⟨H₀, j, e, -, hj, he⟩ := hi.exists_descent_of_overlap_range_eq
      (toAlgebraicClosure k)
      (overlap_range_eq (toAlgebraicClosure k) j₀ q hfib g x.left (hleft g hg))
    have hH : IsTorus H₀ :=
      IsTorus.of_baseChange (IsTorus.of_iso e (hT₀.baseChange (K := AlgebraicClosure k)))
    refine ⟨{ H₀ with comm := hH.isCommMonObj }, j, hH, hj, fun g' hg' => ?_⟩
    rw [he, SubgroupFunctor.range_iso_comp]
    apply range_conj_eq_of_mem_torusNormalizer
    apply hfib
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, baseChangePointsEquiv_left, Category.assoc]
    rw [hleft g' hg', hleft g hg]
  · exact ⟨T₀, j₀, hT₀, hj₀, fun g hg => (hlift ⟨g, hg⟩).elim⟩

end MaximalTorusParameterExistence

open MaximalTorusParameterExistence

/-- Every maximal torus in a smooth connected affine group over any field has an actual
parameter scheme: the homogeneous quotient by its smooth closed normalizer. -/
theorem maximalTorusParameterExistence : MaximalTorusParameterExistenceStatement.{u} := by
  intro k _ G _ _ _ T₀ j₀ hmax
  obtain ⟨H, i, hi, hHsmooth, hrep⟩ :=
    torusNormalizerSmoothClosed k G T₀ j₀ hmax.1 hmax.2.1
  obtain ⟨Q, q, hsep, hlft, hqc, hqsm, hqsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G H i hi hHsmooth
  rw [hrep.2] at hfib
  have hQsmooth : Smooth Q.hom := by
    have : Smooth (q.left ≫ Q.hom) := by
      rw [Over.w q]
      infer_instance
    exact Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation q.left Q.hom
  exact ⟨Q, q, ⟨hQsmooth, hsep, hlft, hqc⟩, ⟨hqsm, hqsurj, hqqc⟩, hfib,
    conjugationCompatible_of_fiber j₀ hmax.1 hmax.2.1 q fun U a₁ a₂ h => (hfib U a₁ a₂).mp h⟩

end Langlands.GroupScheme
