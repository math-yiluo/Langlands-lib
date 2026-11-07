import Langlands.GroupScheme.Rational.RootHeisenbergEquivariant
import Langlands.GroupScheme.Rational.RootPointLieAutomorphisms
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # The Lie algebra of the quotient of a multipliable root group

Let `a` be a nonzero character of a split torus `S` in a smooth affine group `G` over a field,
such that no `n • a` with `n ≥ 3` is a relative root. The differential of the quotient map
`q : U_a → V = U_a / U_{2a}` identifies the weight space of `a` in the Lie algebra of `G` with the
Lie algebra of `V`. Composed with the point-to-Lie comparison of the vector group `V`, this
identifies the rational points of `V` with the weight space of `a`. Both identifications commute
with every action fixing the split torus.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The weight spaces of a nonzero character and of its double are disjoint. -/
theorem disjoint_weightSpace_two_nsmul [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) :
    Disjoint (weightSpace i a) (weightSpace i (2 • a)) := by
  classical
  have hne : a ≠ 2 • a := by
    intro h
    apply ha
    have h' : 2 • a - a = 0 := by rw [← h, sub_self]
    rwa [two_nsmul, add_sub_cancel_right] at h'
  exact (isInternal_weightSpace_of_isSplitTorus k G S hS i).submodule_iSupIndep.pairwiseDisjoint
    hne

variable [Smooth G.X.hom]

/-- The weight space of a positive multiple of a nonzero character lies in the tangent of its
root functor. -/
theorem weightSpace_nsmul_le_tangentSubmodule (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    weightSpace i (n • a) ≤ tangentSubmodule (subgroup i a) := by
  rw [tangentSubmodule_subgroup i a hS ha, semigroupWeightSpan_cyclicTail,
    ← actionWeightSpace_conjugation]
  exact le_iSup (fun m : {m : ℕ // 1 ≤ m ∧ 0 < m} =>
    actionWeightSpace (AutomorphicAction.conjugation i) (m.val • a)) ⟨n, hn, hn⟩

/-- The weight space of a nonzero character lies in the tangent of its root functor. -/
theorem weightSpace_le_tangentSubmodule (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) :
    weightSpace i a ≤ tangentSubmodule (subgroup i a) := by
  simpa only [one_smul] using weightSpace_nsmul_le_tangentSubmodule hS i ha le_rfl

/-- If no `n • a` with `n ≥ 3` is a relative root, the tangent of the root functor of `a` lies in
the sum of the weight spaces of `a` and `2 • a`. -/
theorem tangentSubmodule_le_weightSpace_sup_of_noHigherRoots (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    tangentSubmodule (subgroup i a) ≤ weightSpace i a ⊔ weightSpace i (2 • a) := by
  rw [tangentSubmodule_subgroup i a hS ha, semigroupWeightSpan_cyclicTail]
  refine iSup_le fun n => ?_
  rw [actionWeightSpace_conjugation]
  obtain ⟨n, hn1, hn0⟩ := n
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | hn
  · rw [one_smul]
    exact le_sup_left
  · exact le_sup_right
  · have hbot : weightSpace i (n • a) = ⊥ := by
      by_contra h
      exact hhigh n hn (mem_relativeRoots.mpr ⟨hS.nsmul_ne_zero ha (by omega), h⟩)
    rw [hbot]
    exact bot_le

/-- If no `n • a` with `n ≥ 3` is a relative root, the tangent of the root functor of `a` is the
sum of the weight spaces of `a` and `2 • a`. -/
theorem tangentSubmodule_eq_weightSpace_sup_of_noHigherRoots (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    tangentSubmodule (subgroup i a) = weightSpace i a ⊔ weightSpace i (2 • a) :=
  le_antisymm (tangentSubmodule_le_weightSpace_sup_of_noHigherRoots hS i ha hhigh)
    (sup_le (weightSpace_le_tangentSubmodule hS i ha)
      (weightSpace_nsmul_le_tangentSubmodule hS i ha (by norm_num)))

variable {U U₂ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

namespace DoubleRootCommutatorPairing

variable (C : DoubleRootCommutatorPairing i a hj hj₂)

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] in
/-- The quotient of a root group by its doubled root group is affine. -/
theorem isAffineHom_V : IsAffineHom C.V.X.hom := by
  obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
  exact IsVectorGroupOfDimension.isAffineHom ⟨e, he.1⟩

variable [IsAffineHom C.V.X.hom]

omit [Smooth G.X.hom] in
/-- A tangent vector of the root group lies over the identity of the quotient exactly when its
image in the ambient group is tangent to the doubled root functor. -/
theorem targetMapLinear_q_eq_zero_iff (Y : Additive (lieKernel U k)) :
    Lie.targetMapLinear C.q k Y = 0 ↔
      Lie.targetMapLinear j k Y ∈ tangentSubmodule (subgroup i (2 • a)) := by
  rw [mem_tangentSubmodule]
  change _ ↔ Y.toMul.val ∈ ((subgroup i (2 • a)).comap j).carrier _
  rw [← C.isFppfQuotient.2.2.2, mem_range_kernelι_iff]
  constructor
  · intro hY
    exact congrArg (fun Z : Additive (lieKernel C.V k) => Z.toMul.val) hY
  · intro hY
    apply Additive.toMul.injective
    exact Subtype.ext hY

variable (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)

/-- The differential of the quotient map, read on the weight space of `a` through the root
group: lift a weight vector to the Lie algebra of the root group and apply the differential of
the quotient map. -/
def rootQuotientLieMap : weightSpace i a →ₗ[k] Additive (lieKernel C.V k) :=
  (Lie.targetMapLinear C.q k).comp
    (((representedTangentLinearEquiv (subgroup i a) j hj).symm.toLinearMap).comp
      (Submodule.inclusion (weightSpace_le_tangentSubmodule hS i ha)))

/-- The comparison map is the differential of the quotient map at any tangent vector of the root
group whose image differs from the given weight vector by a tangent vector of the doubled root
functor. -/
theorem rootQuotientLieMap_eq_of_sub_mem (X : weightSpace i a) (Y : Additive (lieKernel U k))
    (h : Lie.targetMapLinear j k Y - X ∈ tangentSubmodule (subgroup i (2 • a))) :
    C.rootQuotientLieMap hS ha X = Lie.targetMapLinear C.q k Y := by
  set Y₁ := (representedTangentLinearEquiv (subgroup i a) j hj).symm
    (Submodule.inclusion (weightSpace_le_tangentSubmodule hS i ha) X) with hY₁
  have hdj : Lie.targetMapLinear j k Y₁ = X :=
    congrArg Subtype.val ((representedTangentLinearEquiv (subgroup i a) j hj).apply_symm_apply
      (Submodule.inclusion (weightSpace_le_tangentSubmodule hS i ha) X))
  have h0 : Lie.targetMapLinear C.q k (Y - Y₁) = 0 := by
    rw [C.targetMapLinear_q_eq_zero_iff, map_sub, hdj]
    exact h
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

variable (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)

include hhigh in
/-- The comparison map is injective: a weight vector of `a` tangent to the doubled root functor
is a weight vector of `2 • a`, hence zero. -/
theorem rootQuotientLieMap_injective : Function.Injective (C.rootQuotientLieMap hS ha) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  have hmem : Lie.targetMapLinear j k 0 - X ∈ tangentSubmodule (subgroup i (2 • a)) ↔
      (X : Additive (lieKernel G k)) ∈ tangentSubmodule (subgroup i (2 • a)) := by
    rw [map_zero, zero_sub, neg_mem_iff]
  have h2 : (X : Additive (lieKernel G k)) ∈ tangentSubmodule (subgroup i (2 • a)) := by
    set Y₁ := (representedTangentLinearEquiv (subgroup i a) j hj).symm
      (Submodule.inclusion (weightSpace_le_tangentSubmodule hS i ha) X)
    have hdj : Lie.targetMapLinear j k Y₁ = X :=
      congrArg Subtype.val ((representedTangentLinearEquiv (subgroup i a) j hj).apply_symm_apply
        (Submodule.inclusion (weightSpace_le_tangentSubmodule hS i ha) X))
    rw [← hdj, ← C.targetMapLinear_q_eq_zero_iff]
    exact hX
  rw [tangentSubmodule_eq_weightSpace_of_noHigherRoots hS i h2a
    (hasNoHigherRoots_two_nsmul hhigh)] at h2
  have hbot := (disjoint_weightSpace_two_nsmul hS i ha).le_bot ⟨X.property, h2⟩
  exact Subtype.ext ((Submodule.mem_bot k).mp hbot)

include hhigh in
/-- The comparison map is surjective: a tangent vector of the quotient lifts through a section of
schemes normalized at the identity, and the weight component of `2 • a` of the lift lies over the
identity of the quotient. -/
theorem rootQuotientLieMap_surjective : Function.Surjective (C.rootQuotientLieMap hS ha) := by
  intro Z
  obtain ⟨M⟩ := nonempty_heisenbergNormalForm C hS ha hhigh
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  let Y : Additive (lieKernel U k) := Additive.ofMul ⟨Z.toMul.val ≫ M.sec, by
    change Lie.reduction U (Z.toMul.val ≫ M.sec) = 1
    have hZ : Lie.reduction C.V Z.toMul.val = 1 := Z.toMul.property
    rw [Lie.reduction, Lie.affineMap_apply] at hZ ⊢
    rw [← Category.assoc, hZ]
    exact M.one_sec _⟩
  have hqY : Lie.targetMapLinear C.q k Y = Z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (Z.toMul.val ≫ M.sec) ≫ C.q.hom.hom = Z.toMul.val
    rw [Category.assoc, M.sec_comp, Category.comp_id]
  have hmem : Lie.targetMapLinear j k Y ∈ weightSpace i a ⊔ weightSpace i (2 • a) := by
    rw [← tangentSubmodule_eq_weightSpace_sup_of_noHigherRoots hS i ha hhigh]
    exact (representedTangentLinearEquiv (subgroup i a) j hj Y).property
  obtain ⟨X₁, hX₁, X₂, hX₂, hsum⟩ := Submodule.mem_sup.mp hmem
  refine ⟨⟨X₁, hX₁⟩, ?_⟩
  rw [C.rootQuotientLieMap_eq_of_sub_mem hS ha ⟨X₁, hX₁⟩ Y, hqY]
  rw [tangentSubmodule_eq_weightSpace_of_noHigherRoots hS i h2a
    (hasNoHigherRoots_two_nsmul hhigh)]
  change Lie.targetMapLinear j k Y - X₁ ∈ _
  rw [← hsum, add_sub_cancel_left]
  exact hX₂

/-- **The Lie algebra of the quotient of a multipliable root group.** The differential of the
quotient map `U_a → U_a / U_{2a}` identifies the weight space of `a` in the Lie algebra of `G`
with the Lie algebra of the quotient. -/
def rootQuotientLieEquiv : weightSpace i a ≃ₗ[k] Additive (lieKernel C.V k) :=
  LinearEquiv.ofBijective (C.rootQuotientLieMap hS ha)
    ⟨C.rootQuotientLieMap_injective hS ha hhigh, C.rootQuotientLieMap_surjective hS ha hhigh⟩

theorem rootQuotientLieEquiv_apply (X : weightSpace i a) :
    C.rootQuotientLieEquiv hS ha hhigh X = C.rootQuotientLieMap hS ha X := rfl

/-- The inverse comparison sends the differential of the quotient map at a tangent vector `Y` of
the root group to the weight component of `a` of the image of `Y` in the Lie algebra of `G`. -/
theorem rootQuotientLieEquiv_symm_apply (Y : Additive (lieKernel U k)) (X : weightSpace i a)
    (h : Lie.targetMapLinear j k Y - X ∈ weightSpace i (2 • a)) :
    (C.rootQuotientLieEquiv hS ha hhigh).symm (Lie.targetMapLinear C.q k Y) = X := by
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  rw [LinearEquiv.symm_apply_eq, rootQuotientLieEquiv_apply]
  rw [← tangentSubmodule_eq_weightSpace_of_noHigherRoots hS i h2a
    (hasNoHigherRoots_two_nsmul hhigh)] at h
  exact (C.rootQuotientLieMap_eq_of_sub_mem hS ha X Y h).symm

omit [Smooth G.X.hom] in
/-- A group endomorphism fixing the torus preserves the weight space of every character. -/
theorem targetMapLinear_mem_weightSpace_of_fixes (σ : G ⟶ G) (hi : i ≫ σ = i)
    {x : Additive (lieKernel G k)} (hx : x ∈ weightSpace i a) :
    Lie.targetMapLinear σ k x ∈ weightSpace i a := by
  have h := lieKernelHomLinear_mem_weightSpace σ i a hx
  rwa [hi] at h

/-- **Naturality.** The comparison commutes with compatible endomorphisms of the ambient group,
of the root group and of the quotient, when the ambient one fixes the torus. -/
theorem rootQuotientLieMap_naturality (σ : G ⟶ G) (hi : i ≫ σ = i) (ρ : U ⟶ U)
    (τ : C.V ⟶ C.V) (hρ : ρ ≫ j = j ≫ σ) (hτ : ρ ≫ C.q = C.q ≫ τ) (X : weightSpace i a) :
    C.rootQuotientLieMap hS ha
        ⟨Lie.targetMapLinear σ k X, targetMapLinear_mem_weightSpace_of_fixes σ hi X.property⟩ =
      Lie.targetMapLinear τ k (C.rootQuotientLieMap hS ha X) := by
  set Y₁ := (representedTangentLinearEquiv (subgroup i a) j hj).symm
    (Submodule.inclusion (weightSpace_le_tangentSubmodule hS i ha) X) with hY₁
  have hdj : Lie.targetMapLinear j k Y₁ = X :=
    congrArg Subtype.val ((representedTangentLinearEquiv (subgroup i a) j hj).apply_symm_apply
      (Submodule.inclusion (weightSpace_le_tangentSubmodule hS i ha) X))
  have hjρ : Lie.targetMapLinear j k (Lie.targetMapLinear ρ k Y₁) =
      Lie.targetMapLinear σ k (Lie.targetMapLinear j k Y₁) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa only [lieKernelHomLinear_val, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : U ⟶ G => Y₁.toMul.val ≫ f.hom.hom) hρ
  have hqρ : Lie.targetMapLinear C.q k (Lie.targetMapLinear ρ k Y₁) =
      Lie.targetMapLinear τ k (Lie.targetMapLinear C.q k Y₁) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa only [lieKernelHomLinear_val, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : U ⟶ C.V => Y₁.toMul.val ≫ f.hom.hom) hτ
  rw [C.rootQuotientLieMap_eq_of_sub_mem hS ha _ (Lie.targetMapLinear ρ k Y₁)
    (by rw [hjρ, hdj, sub_self]; exact zero_mem _), hqρ]
  rfl

include hhigh in
/-- The linear comparison commutes with compatible endomorphisms fixing the torus. -/
theorem rootQuotientLieEquiv_naturality (σ : G ⟶ G) (hi : i ≫ σ = i) (ρ : U ⟶ U)
    (τ : C.V ⟶ C.V) (hρ : ρ ≫ j = j ≫ σ) (hτ : ρ ≫ C.q = C.q ≫ τ) (X : weightSpace i a) :
    C.rootQuotientLieEquiv hS ha hhigh
        ⟨Lie.targetMapLinear σ k X, targetMapLinear_mem_weightSpace_of_fixes σ hi X.property⟩ =
      Lie.targetMapLinear τ k (C.rootQuotientLieEquiv hS ha hhigh X) :=
  C.rootQuotientLieMap_naturality hS ha σ hi ρ τ hρ hτ X

section Action

variable {D : GroupScheme (Spec (CommRingCat.of k))} (b : AutomorphicAction D G)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom C.V.X.hom] in
/-- The constant point at the base coefficient algebra is the rational coefficient point. -/
theorem constantPoint_eq_rationalCoeffEquiv (h : rationalPoints D) :
    D.constantPoint h ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))) =
      GaloisPointComparison.rationalCoeffEquiv k D h := by
  apply Over.OverMorphism.ext
  rw [GaloisPointComparison.rationalCoeffEquiv_left]
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ h.left = h.left
  simp

omit [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom C.V.X.hom] in
include hfix in
/-- The differential of a rational point of a group fixing the torus preserves the weight space
of every character. -/
theorem differential_mem_weightSpace_of_fixes (h : rationalPoints D)
    {x : Additive (lieKernel G k)} (hx : x ∈ weightSpace i a) :
    b.differential (GaloisPointComparison.rationalCoeffEquiv k D h) x ∈ weightSpace i a := by
  have hm := targetMapLinear_mem_weightSpace_of_fixes (b.basePointIso h).hom
    (basePointIso_fixes_torus i b hfix h) hx
  rwa [b.targetMapLinear_basePointIso, constantPoint_eq_rationalCoeffEquiv] at hm

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom C.V.X.hom] in
/-- Evaluated at a rational point, the induced action on the root group lies over the ambient
evaluated automorphism. -/
theorem rootActionBasePointIso_comp (h : rationalPoints D) :
    ((rootActionOfFixesTorus b i hfix a j hj).basePointIso h).hom ≫ j =
      j ≫ (b.basePointIso h).hom := by
  apply Grp.hom_ext
  change ((rootActionOfFixesTorus b i hfix a j hj).basePointIso h).hom.hom.hom ≫ j.hom.hom =
    j.hom.hom ≫ (b.basePointIso h).hom.hom.hom
  have h1 := (rootActionOfFixesTorus b i hfix a j hj).comp_basePointIso_hom h U.X (𝟙 U.X)
  rw [Category.id_comp] at h1
  rw [h1, b.comp_basePointIso_hom, rootActionOfFixesTorus_act_comp, Category.id_comp]

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom C.V.X.hom] in
/-- Evaluated at a rational point, the quotient map intertwines the induced actions on the root
group and on the quotient. -/
theorem rootActionBasePointIso_comp_q (h : rationalPoints D) :
    ((rootActionOfFixesTorus b i hfix a j hj).basePointIso h).hom ≫ C.q =
      C.q ≫ ((C.torusQuotientAction b hfix).basePointIso h).hom := by
  apply Grp.hom_ext
  change ((rootActionOfFixesTorus b i hfix a j hj).basePointIso h).hom.hom.hom ≫ C.q.hom.hom =
    C.q.hom.hom ≫ ((C.torusQuotientAction b hfix).basePointIso h).hom.hom.hom
  have h1 := (rootActionOfFixesTorus b i hfix a j hj).comp_basePointIso_hom h U.X (𝟙 U.X)
  rw [Category.id_comp] at h1
  rw [h1, (C.torusQuotientAction b hfix).comp_basePointIso_hom]
  simpa only [Category.id_comp] using (C.torusQuotientAction_act_comp b hfix _ (𝟙 U.X)).symm

include hhigh in
/-- **Equivariance.** The differential of the quotient map on the weight space of `a` intertwines
the differentials of a rational point of a group fixing the torus, acting on `G` and on the
quotient. -/
theorem rootQuotientLieEquiv_act (h : rationalPoints D) (X : weightSpace i a) :
    C.rootQuotientLieEquiv hS ha hhigh
        ⟨b.differential (GaloisPointComparison.rationalCoeffEquiv k D h) X,
          differential_mem_weightSpace_of_fixes b hfix h X.property⟩ =
      (C.torusQuotientAction b hfix).differential
        (GaloisPointComparison.rationalCoeffEquiv k D h) (C.rootQuotientLieEquiv hS ha hhigh X) := by
  have key := C.rootQuotientLieEquiv_naturality hS ha hhigh (b.basePointIso h).hom
    (basePointIso_fixes_torus i b hfix h) _ _ (rootActionBasePointIso_comp b hfix h)
    (C.rootActionBasePointIso_comp_q b hfix h) X
  have hX : (⟨b.differential (GaloisPointComparison.rationalCoeffEquiv k D h) X,
      differential_mem_weightSpace_of_fixes b hfix h X.property⟩ : weightSpace i a) =
      ⟨Lie.targetMapLinear (b.basePointIso h).hom k X,
        targetMapLinear_mem_weightSpace_of_fixes _ (basePointIso_fixes_torus i b hfix h)
          X.property⟩ :=
    Subtype.ext (by
      change b.differential (GaloisPointComparison.rationalCoeffEquiv k D h) X.val =
        Lie.targetMapLinear (b.basePointIso h).hom k X.val
      rw [b.targetMapLinear_basePointIso, constantPoint_eq_rationalCoeffEquiv])
  rw [hX, key, (C.torusQuotientAction b hfix).targetMapLinear_basePointIso,
    constantPoint_eq_rationalCoeffEquiv]

end Action

/-- **Rational points of the quotient as weight vectors.** The rational points of
`U_a / U_{2a}` are identified with the weight space of `a` in the Lie algebra of `G`, through the
point-to-Lie comparison of a chosen system of weight vector coordinates of the quotient and the
inverse of `rootQuotientLieEquiv`. -/
def rootQuotientPointLieEquiv : Additive (rationalPoints C.V) ≃+ weightSpace i a :=
  ((GaloisPointComparison.rationalCoeffEquiv k C.V).toAdditive.trans
    (vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose
      C.weightVectorStructure.1.choose_spec.choose_spec.1 (CommAlgCat.of k k))).trans
    (C.rootQuotientLieEquiv hS ha hhigh).symm.toAddEquiv

section PointAction

variable {D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom D.X.hom]
    (b : AutomorphicAction D G)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom C.V.X.hom]
  [IsAffineHom D.X.hom] in
/-- The rational coefficient comparison of the quotient carries the action of a rational point
to the action of its coefficient point. -/
theorem rationalCoeffEquiv_torusQuotientAction (h : rationalPoints D) (v : rationalPoints C.V) :
    GaloisPointComparison.rationalCoeffEquiv k C.V ((C.torusQuotientAction b hfix).act h v) =
      (C.torusQuotientAction b hfix).act (GaloisPointComparison.rationalCoeffEquiv k D h)
        (GaloisPointComparison.rationalCoeffEquiv k C.V v) :=
  (C.torusQuotientAction b hfix).naturality
    (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom h v

omit [IsAffineHom D.X.hom] in
include hhigh in
/-- The inverse of the linear comparison intertwines the differentials of a rational point of a
group fixing the torus. -/
theorem rootQuotientLieEquiv_symm_act (h : rationalPoints D) (Z : Additive (lieKernel C.V k)) :
    ((C.rootQuotientLieEquiv hS ha hhigh).symm
        ((C.torusQuotientAction b hfix).differential
          (GaloisPointComparison.rationalCoeffEquiv k D h) Z) : Additive (lieKernel G k)) =
      b.differential (GaloisPointComparison.rationalCoeffEquiv k D h)
        ((C.rootQuotientLieEquiv hS ha hhigh).symm Z) := by
  obtain ⟨X, rfl⟩ := (C.rootQuotientLieEquiv hS ha hhigh).surjective Z
  rw [← C.rootQuotientLieEquiv_act hS ha hhigh b hfix h X, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

include hhigh in
/-- **Equivariance on rational points.** The identification of the rational points of the
quotient with the weight space of `a` carries the action of a rational point of a group fixing
the torus to its differential on the Lie algebra of `G`. -/
theorem rootQuotientPointLieEquiv_act (h : rationalPoints D) (v : rationalPoints C.V) :
    (C.rootQuotientPointLieEquiv hS ha hhigh
        (Additive.ofMul ((C.torusQuotientAction b hfix).act h v)) :
          Additive (lieKernel G k)) =
      b.differential (GaloisPointComparison.rationalCoeffEquiv k D h)
        (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul v)) := by
  have hw := C.weightVectorStructure.1.choose_spec.choose_spec
  have hlin := C.isLinearVectorCoordinates_torusQuotientAction b hfix hS ha hw
  change ((C.rootQuotientLieEquiv hS ha hhigh).symm
      (vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose hw.1 (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k C.V
          ((C.torusQuotientAction b hfix).act h v)))) : Additive (lieKernel G k)) =
    b.differential (GaloisPointComparison.rationalCoeffEquiv k D h)
      ((C.rootQuotientLieEquiv hS ha hhigh).symm
        (vectorPointLieEquiv C.weightVectorStructure.1.choose_spec.choose hw.1
          (CommAlgCat.of k k)
          (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k C.V v))))
  rw [C.rationalCoeffEquiv_torusQuotientAction b hfix h v]
  have hv := vectorPointLieEquiv_act _ hw.1 hlin (CommAlgCat.of k k)
    (GaloisPointComparison.rationalCoeffEquiv k D h)
    (GaloisPointComparison.rationalCoeffEquiv k C.V v)
  refine (congrArg (fun W => ((C.rootQuotientLieEquiv hS ha hhigh).symm W :
    Additive (lieKernel G k))) hv).trans ?_
  exact C.rootQuotientLieEquiv_symm_act hS ha hhigh b hfix h _

end PointAction

end DoubleRootCommutatorPairing

end Langlands.GroupScheme.RelativeRoot
