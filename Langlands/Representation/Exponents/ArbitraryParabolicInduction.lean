import Langlands.Representation.Exponents.ArbitraryParabolic

/-! # Normalized induction and split-component exponents for represented parabolics

Renard 2026, VII.1.1 (printed pp.220–221/PDF pp.226–227). The literal point images
of a represented parabolic, its Levi and its radical form an actual semidirect
decomposition, which gives normalized parabolic induction `i_P^G`. The generalized
weight spaces and exponents of a split component are defined for an arbitrary smooth
representation of the Levi points (action of `A_M`) and of the whole group (action of
`A_G`). No decomposition, finiteness or comparison theorem is asserted.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {G H P M U : GroupScheme (Spec (CommRingCat.of k))}

section Decomposition

/-- Rational points are functorial. -/
theorem pointMap_comp_apply (j : H ⟶ P) (p : P ⟶ G) (y : rationalPoints H) :
    rationalPoints.map (j ≫ p) y = rationalPoints.map p (rationalPoints.map j y) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

/-- The literal point image of a composite lies in that of the outer map. -/
theorem pointImage_comp_le (p : P ⟶ G) (j : H ⟶ P) : pointImage (j ≫ p) ≤ pointImage p := by
  rintro _ ⟨x, rfl⟩
  exact ⟨rationalPoints.map j x, (pointMap_comp_apply j p x).symm⟩

/-- The whole parabolic image normalizes the radical image, by the radical's all-test
normality. -/
theorem pointImage_le_normalizer_radical (p : P ⟶ G) (r : U ⟶ P)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    pointImage p ≤ Subgroup.normalizer (pointImage (r ≫ p) : Set (rationalPoints G)) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨z, rfl⟩
  have hz : rationalPoints.map r z ∈ (SubgroupFunctor.range r).carrier (Over.mk (𝟙 _)) :=
    ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := hr.1.isNormal (Over.mk (𝟙 _)) x (rationalPoints.map r z)
    (Subgroup.mem_top _) hz
  refine ⟨w, ?_⟩
  change rationalPoints.map p (rationalPoints.map r w) =
    rationalPoints.map p x * rationalPoints.map p (rationalPoints.map r z) *
      (rationalPoints.map p x)⁻¹
  rw [show rationalPoints.map r w = _ from hw, map_mul, map_mul, map_inv]

/-- On rational points the multiplication morphism is `(x, y) ↦ l(x) r(y)`. -/
theorem lift_comp_subgroupMultiplication (l : M ⟶ P) (r : U ⟶ P) (x : rationalPoints M)
    (y : rationalPoints U) :
    lift x y ≫ subgroupMultiplication l r = rationalPoints.map l x * rationalPoints.map r y :=
  comp_subgroupMultiplication l r x y

/-- An isomorphic multiplication morphism makes the point factorization unique. -/
theorem eq_and_eq_of_pointMultiplication (l : M ⟶ P) (r : U ⟶ P)
    (hmul : IsIso (subgroupMultiplication l r))
    {x x' : rationalPoints M} {y y' : rationalPoints U}
    (h : rationalPoints.map l x * rationalPoints.map r y =
      rationalPoints.map l x' * rationalPoints.map r y') :
    x = x' ∧ y = y' := by
  have h2 : lift x y ≫ subgroupMultiplication l r = lift x' y' ≫ subgroupMultiplication l r := by
    rw [lift_comp_subgroupMultiplication, lift_comp_subgroupMultiplication]
    exact h
  have h3 := (cancel_mono (subgroupMultiplication l r)).mp h2
  exact ⟨by simpa using congrArg (· ≫ fst _ _) h3, by simpa using congrArg (· ≫ snd _ _) h3⟩

/-- An isomorphic multiplication morphism factors every rational point. -/
theorem exists_pointMultiplication (l : M ⟶ P) (r : U ⟶ P)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : rationalPoints P) :
    ∃ (x : rationalPoints M) (y : rationalPoints U),
      rationalPoints.map l x * rationalPoints.map r y = q := by
  refine ⟨q ≫ inv (subgroupMultiplication l r) ≫ fst _ _,
    q ≫ inv (subgroupMultiplication l r) ≫ snd _ _, ?_⟩
  rw [← lift_comp_subgroupMultiplication]
  have hlift : lift (q ≫ inv (subgroupMultiplication l r) ≫ fst _ _)
      (q ≫ inv (subgroupMultiplication l r) ≫ snd _ _) =
        q ≫ inv (subgroupMultiplication l r) := by
    ext <;> simp
  rw [hlift, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The literal point images of a closed represented parabolic, its Levi and a represented
radical with isomorphic multiplication form an actual semidirect decomposition. -/
theorem isSemidirectDecomposition_pointImage (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsClosedSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    IsSemidirectDecomposition (pointImage p) (pointImage (l ≫ p)) (pointImage (r ≫ p)) := by
  have : IsClosedImmersion p.hom.hom.left := hp
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  have hinj : Function.Injective (rationalPoints.map p) := fun x y hxy =>
    (cancel_mono p.hom.hom).mp hxy
  refine ⟨pointImage_comp_le p l, pointImage_comp_le p r,
    pointImage_le_normalizer_radical p r hr, ?_⟩
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    rintro ⟨g, hg⟩ hgl hgr
    obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.mp hgl
    obtain ⟨y, hy⟩ := Subgroup.mem_subgroupOf.mp hgr
    have hxy : rationalPoints.map l x * rationalPoints.map r 1 =
        rationalPoints.map l 1 * rationalPoints.map r y := by
      rw [map_one, map_one, mul_one, one_mul]
      apply hinj
      rw [← pointMap_comp_apply, ← pointMap_comp_apply]
      exact hx.trans hy.symm
    have hx1 : x = 1 := (eq_and_eq_of_pointMultiplication l r hmul hxy).1
    apply Subtype.ext
    change g = 1
    rw [← show rationalPoints.map (l ≫ p) x = g from hx, hx1, map_one]
  · refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨q, hq⟩ := g.2
    obtain ⟨x, y, hxy⟩ := exists_pointMultiplication l r hmul q
    refine Set.mem_mul.2 ⟨⟨rationalPoints.map (l ≫ p) x, pointImage_comp_le p l ⟨x, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩,
      ⟨rationalPoints.map (r ≫ p) y, pointImage_comp_le p r ⟨y, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨y, rfl⟩, ?_⟩
    apply Subtype.ext
    change rationalPoints.map (l ≫ p) x * rationalPoints.map (r ≫ p) y = (g : rationalPoints G)
    rw [pointMap_comp_apply, pointMap_comp_apply, ← map_mul, hxy, hq]

end Decomposition

section Topology

variable [TopologicalSpace k] [IsAffineHom G.X.hom]

local instance inductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [NonarchimedeanGroup (rationalPoints G)]

section Induction

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]

/-- Renard's normalized parabolic induction `i_P^G` for the specified represented
parabolic, Levi and radical: smooth induction from the literal parabolic image of the
inflation along the actual Levi projection, twisted by `δ_P^{1/2}`. The Levi hypothesis
records the chosen decomposition, as for `jacquetFunctor`. -/
abbrev inductionFunctor (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (_hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p)) ⥤
      SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
  normalizedInductionFunctor
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)

end Induction

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  {AG : CommGroupScheme (Spec (CommRingCat.of k))} {aG : AG.toGrp ⟶ G}

section Levi

variable (j : M ⟶ G)

/-- Renard's `W_ψ`: the compact-open union of uniform generalized character spaces of the
action of `A_M(F)`, through its literal Levi image, on a smooth representation `W` of the
Levi points. -/
def leviWeightSpace (ha : IsSplitComponent a) (W : SmoothRep.{0, u, w} ℂ (pointImage j))
    (ψ : rationalPoints A.toGrp →* ℂˣ) : Subrepresentation W.representation :=
  generalizedWeightSpace W.representation (splitComponentPointsMap j a) ψ
    (splitComponentPointsMap_mem_center j ha)

/-- A smooth character of `A_M(F)` with nonzero generalized weight space in `W`. -/
def IsLeviExponent (ha : IsSplitComponent a) (W : SmoothRep.{0, u, w} ℂ (pointImage j))
    (ψ : rationalPoints A.toGrp →* ℂˣ) : Prop :=
  letI := RationalPointFamily.splitComponentPointTopology ha
  IsGeneralizedWeight W.representation (splitComponentPointsMap j a) ψ
    (splitComponentPointsMap_mem_center j ha)

/-- Renard's `Exp(A_M, W)`. -/
def leviExponents (ha : IsSplitComponent a) (W : SmoothRep.{0, u, w} ℂ (pointImage j)) :
    Set (rationalPoints A.toGrp →* ℂˣ) :=
  {ψ | IsLeviExponent j ha W ψ}

theorem mem_leviExponents (ha : IsSplitComponent a) (W : SmoothRep.{0, u, w} ℂ (pointImage j))
    (ψ : rationalPoints A.toGrp →* ℂˣ) :
    ψ ∈ leviExponents j ha W ↔ IsLeviExponent j ha W ψ :=
  Iff.rfl

theorem isLeviExponent_iff_isOpen_ker_and (ha : IsSplitComponent a)
    (W : SmoothRep.{0, u, w} ℂ (pointImage j)) (ψ : rationalPoints A.toGrp →* ℂˣ) :
    IsLeviExponent j ha W ψ ↔
      @IsOpen _ (RationalPointFamily.splitComponentPointTopology ha)
        (ψ.ker : Set (rationalPoints A.toGrp)) ∧ leviWeightSpace j ha W ψ ≠ ⊥ :=
  Iff.rfl

end Levi

section Group

/-- Renard's `V_χ`: the compact-open union of uniform generalized character spaces of the
action of `A_G(F)` on a smooth representation of `G(F)`. -/
def groupWeightSpace (haG : IsSplitComponent aG)
    (V : SmoothRep.{0, u, w} ℂ (rationalPoints G)) (χ : rationalPoints AG.toGrp →* ℂˣ) :
    Subrepresentation V.representation :=
  generalizedWeightSpace V.representation (rationalPoints.map aG) χ
    haG.isCentralSplitTorus.isCentral.map_mem_center

/-- A smooth character of `A_G(F)` with nonzero generalized weight space in `V`. -/
def IsGroupExponent (haG : IsSplitComponent aG) (V : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (χ : rationalPoints AG.toGrp →* ℂˣ) : Prop :=
  letI := RationalPointFamily.splitComponentPointTopology haG
  IsGeneralizedWeight V.representation (rationalPoints.map aG) χ
    haG.isCentralSplitTorus.isCentral.map_mem_center

/-- Renard's `Exp(A_G, V)`. -/
def groupExponents (haG : IsSplitComponent aG) (V : SmoothRep.{0, u, w} ℂ (rationalPoints G)) :
    Set (rationalPoints AG.toGrp →* ℂˣ) :=
  {χ | IsGroupExponent haG V χ}

theorem mem_groupExponents (haG : IsSplitComponent aG)
    (V : SmoothRep.{0, u, w} ℂ (rationalPoints G)) (χ : rationalPoints AG.toGrp →* ℂˣ) :
    χ ∈ groupExponents haG V ↔ IsGroupExponent haG V χ :=
  Iff.rfl

theorem isGroupExponent_iff_isOpen_ker_and (haG : IsSplitComponent aG)
    (V : SmoothRep.{0, u, w} ℂ (rationalPoints G)) (χ : rationalPoints AG.toGrp →* ℂˣ) :
    IsGroupExponent haG V χ ↔
      @IsOpen _ (RationalPointFamily.splitComponentPointTopology haG)
        (χ.ker : Set (rationalPoints AG.toGrp)) ∧ groupWeightSpace haG V χ ≠ ⊥ :=
  Iff.rfl

/-- Membership in `V_χ` for a smooth representation: one power of every
`π(a) - χ(a)` kills the vector. -/
theorem mem_groupWeightSpace [LocallyCompactSpace (rationalPoints G)]
    (haG : IsSplitComponent aG) (V : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (χ : rationalPoints AG.toGrp →* ℂˣ) (x : V) :
    x ∈ groupWeightSpace haG V χ ↔
      ∃ d : ℕ, ∀ t : rationalPoints AG.toGrp,
        ((V.representation (rationalPoints.map aG t) - (χ t : ℂ) • 1) ^ d) x = 0 :=
  mem_generalizedWeightSpace_of_isSmooth _ χ _ V.isSmooth x

end Group

section Jacquet

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- The normalized Jacquet weight spaces are the Levi weight spaces of `r_P π`. -/
theorem normalizedJacquetWeightSpace_eq_leviWeightSpace (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ =
      leviWeightSpace (l ≫ p) ha ((jacquetFunctor p l r hp hr hl hmul).obj π) χ :=
  rfl

/-- Renard's `Exp(A, r_P π)` is `Exp(A_M, r_P π)` for the Levi representation `r_P π`. -/
theorem normalizedJacquetExponents_eq_leviExponents (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    normalizedJacquetExponents p l r hp hl hr hmul ha π =
      leviExponents (l ≫ p) ha ((jacquetFunctor p l r hp hr hl hmul).obj π) :=
  rfl

end Jacquet

end Topology

end Langlands.Aubert.General.RepresentedParabolic
