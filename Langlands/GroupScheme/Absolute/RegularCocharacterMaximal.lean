import Langlands.GroupScheme.Absolute.RegularCocharacterWeights
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Maximality of dynamic parabolics of regular cocharacters (conditional on structure inputs) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Weight vectors along homomorphisms -/

section WeightMap

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)} {H G : GroupScheme (Spec R)}
  [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

/-- Postcomposition with a homomorphism commutes with change of test algebra on Lie kernels. -/
theorem lieKernelMapLinear_targetMapLinear (h : H ⟶ G) {A B : Type u} [CommRing A]
    [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (X : Additive (lieKernel H A)) :
    lieKernelMapLinear G φ (Lie.targetMapLinear h A X) =
      Lie.targetMapLinear h B (lieKernelMapLinear H φ X) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change Lie.affineMap G _ (X.toMul.val ≫ h.hom.hom) = Lie.affineMap H _ X.toMul.val ≫ h.hom.hom
  rw [Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc]

/-- Postcomposition with a homomorphism `h` intertwines the adjoint actions:
`Ad(h(g)) (dh X) = dh (Ad(g) X)`. -/
theorem adjoint_comp_targetMapLinear (h : H ⟶ G) {A : Type u} [CommRing A] [Algebra R A]
    (g : Lie.AffinePoints H A) (X : Additive (lieKernel H A)) :
    adjoint G A (g ≫ h.hom.hom) (Lie.targetMapLinear h A X) =
      Lie.targetMapLinear h A (adjoint H A g X) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  have hc : Lie.constant G (g ≫ h.hom.hom) = Lie.constant H g ≫ h.hom.hom := by
    rw [Lie.constant, Lie.constant, Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc]
  change Lie.constant G (g ≫ h.hom.hom) * (X.toMul.val ≫ h.hom.hom) *
      (Lie.constant G (g ≫ h.hom.hom))⁻¹ =
    (Lie.constant H g * X.toMul.val * (Lie.constant H g)⁻¹) ≫ h.hom.hom
  rw [hc, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]

/-- A homomorphism `h : H ⟶ G` maps the weight space of `χ` for `f : T ⟶ H` into the weight
space of `χ` for `f ≫ h`. -/
theorem targetMapLinear_mem_weightSpace (f : T.toGrp ⟶ H) (h : H ⟶ G) {χ : characterLattice T}
    {X : Additive (lieKernel H R)} (hX : X ∈ weightSpace f χ) :
    Lie.targetMapLinear h R X ∈ weightSpace (f ≫ h) χ := by
  intro A _ _ t
  have key := congrArg (Lie.targetMapLinear h A) (hX A t)
  rw [LinearMap.map_smul, ← adjoint_comp_targetMapLinear, ← lieKernelMapLinear_targetMapLinear,
    Category.assoc] at key
  rw [Grp.comp_hom_hom]
  exact key

end WeightMap

/-! ### Root symmetry from relative-root negation -/

section RootSymmetry

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Assuming `RelativeRootNegationStatement`, the roots of a split maximal torus of a connected
reductive group are stable under negation. -/
theorem neg_mem_roots_of_relativeRootNegation (hNeg : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (hj : IsMaximalTorus j) :
    haveI := hG.isAffineHom
    ∀ α ∈ roots j, -α ∈ roots j := by
  have := hG.isAffineHom
  intro α hα
  rw [← relativeRoots_eq_roots] at hα ⊢
  exact hNeg k G hG T j (hj.isMaximalSplitTorus hT) α hα

end RootSymmetry

/-! ### Lie algebras of solvable subgroups containing `P(ν)` -/

section Maximal

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Let `j = f ≫ i` factor through `i : H ⟶ G`, with `T` split and `H` affine and locally of
finite type, and let `ν` be a cocharacter of `T`. Assume that the roots of `j` are stable under
negation, that the image of `Lie(H)` contains every weight space `𝔤_α` with `⟨α, ν⟩ > 0`, and
that for no root `α` do both `𝔤_α` and `𝔤_{-α}` contain a nonzero element of that image. Then
the image of `Lie(H)` lies in the nonnegative weight span of `ν`. -/
theorem targetMapLinear_mem_nonnegativeWeightSpan {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] (hT : IsSplitTorus T.toGrp)
    (i : H ⟶ G) (f : T.toGrp ⟶ H) (ν : cocharacterLattice T)
    (hneg : ∀ α ∈ roots (f ≫ i), -α ∈ roots (f ≫ i))
    (hpos : ∀ α : characterLattice T, 0 < latticePairing T α ν → ∀ X ∈ weightSpace (f ≫ i) α,
      ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val)
    (hobs : ∀ α ∈ roots (f ≫ i), ¬ ((∃ X ∈ weightSpace (f ≫ i) α, X ≠ 0 ∧
        ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val) ∧
      (∃ X ∈ weightSpace (f ≫ i) (-α), X ≠ 0 ∧
        ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val)))
    (Y : Additive (lieKernel H k)) :
    Lie.targetMapLinear i k Y ∈ nonnegativeWeightSpan (f ≫ i) ν := by
  classical
  have hint := isInternal_weightSpace_of_isSplitTorus k H T hT f
  have hY : Y ∈ ⨆ χ, weightSpace f χ := by
    rw [hint.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction
    (motive := fun Y => Lie.targetMapLinear i k Y ∈ nonnegativeWeightSpan (f ≫ i) ν) _ hY
    ?_ ?_ ?_
  · intro χ Y hYχ
    have hX := targetMapLinear_mem_weightSpace f i hYχ
    by_cases hχ : 0 ≤ latticePairing T χ ν
    · rw [nonnegativeWeightSpan_def]
      exact (le_iSup₂ (f := fun χ (_ : 0 ≤ latticePairing T χ ν) => weightSpace (f ≫ i) χ)
        χ hχ) hX
    · by_cases hX0 : Lie.targetMapLinear i k Y = 0
      · rw [hX0]
        exact zero_mem _
      · exfalso
        have hχ0 : χ ≠ 0 := by
          rintro rfl
          simp at hχ
        have hroot : χ ∈ roots (f ≫ i) := by
          refine ⟨hχ0, fun hbot => hX0 ?_⟩
          rw [hbot] at hX
          exact (Submodule.mem_bot _).1 hX
        obtain ⟨X', hX', hX'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hneg χ hroot).2
        have hpos' : 0 < latticePairing T (-χ) ν := by
          rw [map_neg, LinearMap.neg_apply]
          omega
        exact hobs χ hroot ⟨⟨_, hX, hX0, Y.toMul, rfl⟩, ⟨X', hX', hX'0, hpos _ hpos' X' hX'⟩⟩
  · rw [map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

/-- Assuming `DynamicLieStatement`, if `i : B ⟶ G` represents `P(ν ≫ j)` for a cocharacter `ν`
of a split torus `T`, every element of the nonnegative weight span of `ν` in `Lie(G)` is the image
of an element of `Lie(B)`. -/
theorem exists_lieKernel_of_mem_nonnegativeWeightSpan (hLie : DynamicLieStatement.{u})
    [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {B : GroupScheme (Spec (CommRingCat.of k))} (i : B ⟶ G)
    (hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i)
    (X : Additive (lieKernel G k)) (hX : X ∈ nonnegativeWeightSpan j ν) :
    ∃ Z : lieKernel B k, Z.val ≫ i.hom.hom = X.toMul.val := by
  have : Mono i.hom.hom := hrep.1
  have h1 : X.toMul.val ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier _ := by
    rw [(hLie k G _ X.toMul).2.1, iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan hT]
    exact hX
  rw [← hrep.2] at h1
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 h1
  refine ⟨⟨z, mem_lieKernel_of_comp i z ?_⟩, hz⟩
  rw [hz]
  exact X.toMul.property

/-- **Maximality of `P(ν)` among solvable subgroups, conditional on structure inputs.** Let `G`
be a smooth affine group over a field, `j : T ⟶ G` a homomorphism from a split torus whose
roots are stable under negation, and `ν` a cocharacter of `T`. Let `i : B ⟶ G` be a closed
subgroup representing `P(ν ≫ j)`, and `i' : B' ⟶ G` a smooth connected closed subgroup with
`f ≫ i' = i`. If for no root `α` of `j` do both `𝔤_α` and `𝔤_{-α}` contain a nonzero element
of the image of `Lie(B')`, then `f` is an isomorphism. -/
theorem isIso_of_comp_eq_of_isRepresentedBy_parabolic (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hEq : LieSubgroupEqualityStatement.{u})
    [Smooth G.X.hom] (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hneg : ∀ α ∈ roots j, -α ∈ roots j) {B B' : GroupScheme (Spec (CommRingCat.of k))}
    (i : B ⟶ G) (hic : IsClosedSubgroup i)
    (hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i)
    (i' : B' ⟶ G) (f : B ⟶ B') (hi'c : IsClosedSubgroup i') [Smooth B'.X.hom]
    [ConnectedSpace B'.X.left]
    (hobs : ∀ α ∈ roots j, ¬ ((∃ X ∈ weightSpace j α, X ≠ 0 ∧
        ∃ Y : lieKernel B' k, Y.val ≫ i'.hom.hom = X.toMul.val) ∧
      (∃ X ∈ weightSpace j (-α), X ≠ 0 ∧
        ∃ Y : lieKernel B' k, Y.val ≫ i'.hom.hom = X.toMul.val)))
    (hf : f ≫ i' = i) : IsIso f := by
  have : Mono i.hom.hom := hrep.1
  have : IsClosedImmersion i'.hom.hom.left := hi'c
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom B'.X.hom := by
    rw [← Over.w i'.hom.hom]
    infer_instance
  have : IsClosedImmersion i.hom.hom.left := hic
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth B.X.hom := (hSm k G _ B i).1 hrep
  have hfc : IsClosedSubgroup f := by
    have : IsClosedImmersion (f.hom.hom.left ≫ i'.hom.hom.left) := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, hf]
      exact hic
    exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left i'.hom.hom.left
  -- The torus factors through `B`.
  have hjP : SubgroupFunctor.range j ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) :=
    (range_le_centralizer_groupHom_comp j ν).trans (Dynamic.centralizer_le_parabolic _)
  obtain ⟨fT, hfT⟩ : ∃ fT : T.toGrp ⟶ B, fT ≫ i = j := ⟨_, hrep.liftOfLE_comp j hjP⟩
  -- Elements of the nonnegative weight span lift to `Lie(B)`.
  have hP : ∀ X : Additive (lieKernel G k), X ∈ nonnegativeWeightSpan j ν →
      ∃ Z : lieKernel B k, Z.val ≫ i.hom.hom = X.toMul.val :=
    exists_lieKernel_of_mem_nonnegativeWeightSpan hLie hT j ν i hrep
  have hj' : (fT ≫ f) ≫ i' = j := by rw [Category.assoc, hf, hfT]
  have hpos : ∀ α : characterLattice T, 0 < latticePairing T α ν →
      ∀ X ∈ weightSpace ((fT ≫ f) ≫ i') α,
        ∃ Y : lieKernel B' k, Y.val ≫ i'.hom.hom = X.toMul.val := by
    intro α hα X hX
    rw [hj'] at hX
    obtain ⟨Z, hZ⟩ := hP X (by
      rw [nonnegativeWeightSpan_def]
      exact (le_iSup₂ (f := fun χ (_ : 0 ≤ latticePairing T χ ν) => weightSpace j χ)
        α hα.le) hX)
    refine ⟨Lie.targetMap f k Z, ?_⟩
    change (Z.val ≫ f.hom.hom) ≫ i'.hom.hom = X.toMul.val
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    exact hZ
  have hsub : ∀ Y : lieKernel B' k, ∃ Z : lieKernel B k, Z.val ≫ f.hom.hom = Y.val := by
    intro Y
    have hY := targetMapLinear_mem_nonnegativeWeightSpan hT i' (fT ≫ f) ν
      (by rw [hj']; exact hneg) hpos (by rw [hj']; exact hobs) (Additive.ofMul Y)
    rw [hj'] at hY
    obtain ⟨Z, hZ⟩ := hP _ hY
    refine ⟨Z, (cancel_mono i'.hom.hom).1 ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    exact hZ
  have htop : SubgroupFunctor.range f = ⊤ := hEq k B' B f hfc hsub
  -- `f` is surjective on points and `i` is a monomorphism, so `f` is an isomorphism.
  have hi : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  have hi' : (SubgroupFunctor.range i').IsRepresentedBy i' := ⟨inferInstance, rfl⟩
  have hle : SubgroupFunctor.range i' ≤ SubgroupFunctor.range i := by
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hy : y ∈ (SubgroupFunctor.range f).carrier U := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hy
    refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
  have hg := hi.liftOfLE_comp i' hle
  refine ⟨⟨hi.liftOfLE i' hle, ?_, ?_⟩⟩
  · apply SubgroupFunctor.IsRepresentedBy.hom_ext hi
    rw [Category.assoc, hg, hf, Category.id_comp]
  · apply SubgroupFunctor.IsRepresentedBy.hom_ext hi'
    rw [Category.assoc, hf, hg, Category.id_comp]

end Maximal

end Langlands.GroupScheme
