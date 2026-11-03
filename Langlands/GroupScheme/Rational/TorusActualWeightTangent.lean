import Langlands.GroupScheme.Rational.TorusActualWeightSubgroup
import Langlands.GroupScheme.Rational.TorusWeightTangent
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # The actual tangent image of coordinate weight subgroups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TorusActionCoordinates

attribute [local instance] Lie.coordinateOriginAlgebra

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : AutomorphicAction S.toGrp G)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)

/-- Evaluate the actual identity derivation on a coordinate function. -/
def infinitesimalCoordinate (f : Lie.coordinateAlgebra G) :
    Additive (lieKernel G k) →ₗ[k] k where
  toFun X := Lie.kernelDerivationEquiv G X.toMul f
  map_add' X Y := by
    change Lie.kernelDerivationLinearEquiv G (X + Y) f =
      Lie.kernelDerivationLinearEquiv G X f + Lie.kernelDerivationLinearEquiv G Y f
    rw [map_add, Derivation.add_apply]
  map_smul' c X := by
    change Lie.kernelDerivationLinearEquiv G (c • X) f =
      c • Lie.kernelDerivationLinearEquiv G X f
    rw [map_smul, Derivation.smul_apply]

@[simp] theorem infinitesimalCoordinate_apply (f : Lie.coordinateAlgebra G)
    (X : Additive (lieKernel G k)) :
    infinitesimalCoordinate f X = (Lie.pointCoordinates G X.toMul.val f).snd := rfl

omit [IsAffineHom G.X.hom] in
/-- Actual identity-kernel vectors reduce to the identity in the corepresented functor. -/
theorem affinePointFunctor_reduction (X : Additive (lieKernel G k)) :
    G.affinePointFunctor.map
      (Corepresented.dualReduction (CommAlgCat.of (CommRingCat.of k) k)) X.toMul.val = 1 :=
  X.toMul.property

omit [DecidableEq I] in
/-- Unit-coordinate constants are the original constant torus points. -/
theorem torusPoint_constant {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ) :
    AutomorphicAction.torusPoint e
        (fun i => Units.map
          (TrivSqZeroExt.inlAlgHom (CommRingCat.of k) A A).toMonoidHom (t i)) =
      Lie.constant S.toGrp (AutomorphicAction.torusPoint e t) := by
  exact (AutomorphicAction.torusPoint_naturality e
    (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom (CommRingCat.of k) A A)) t).symm

/-- The coordinate tangent weight condition is exactly the original actual weight condition. -/
theorem isWeightTangent_iff (m : I → ℤ) (X : Additive (lieKernel G k)) :
    Corepresented.IsWeightTangent (b.toCorepresentedTorusAction e) m X.toMul.val ↔
      X ∈ RelativeRoot.actionWeightSpace b (PointedCoordinateWeights.characterEquiv e m) := by
  rw [RelativeRoot.mem_actionWeightSpace_iff]
  constructor
  · intro h A _ _ s
    let t := splitTorus.algebraPointsEquiv I A (s ≫ e.hom.hom.hom)
    have h' := h (CommAlgCat.of (CommRingCat.of k) A) t
    rw [AutomorphicAction.toCorepresentedTorusAction_act, torusPoint_constant] at h'
    have hs : AutomorphicAction.torusPoint e t = s := by
      simp only [t, AutomorphicAction.torusPoint, MulEquiv.symm_apply_apply,
        Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
        Category.comp_id]
    rw [hs] at h'
    have hc := characterValue_torusPoint e (A := CommAlgCat.of (CommRingCat.of k) A) t m
    rw [hs] at hc
    rw [← hc] at h'
    exact h'
  · intro h A t
    have h' := h A (AutomorphicAction.torusPoint e t)
    rw [characterValue_torusPoint] at h'
    rw [AutomorphicAction.toCorepresentedTorusAction_act, torusPoint_constant]
    exact h'

/-- The coordinate derivative of a pure actual weight vector vanishes in every other degree. -/
theorem infinitesimalCoordinate_comp_eq_zero (m n : I → ℤ)
    {X : Additive (lieKernel G k)}
    (hX : X ∈ RelativeRoot.actionWeightSpace b (PointedCoordinateWeights.characterEquiv e n))
    (hmn : m ≠ n) (f : Lie.coordinateAlgebra G) :
    infinitesimalCoordinate
      (Corepresented.comp (corepresentation G) (b.toCorepresentedTorusAction e) m f) X = 0 :=
  Corepresented.snd_comp_eq_zero_of_isWeightTangent (corepresentation G)
    (b.toCorepresentedTorusAction e) ((isWeightTangent_iff b e n X).mpr hX) f hmn

/-- On affine tests the coordinate comparison recovers the original point. -/
theorem affinePointsEquiv_actual (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : G.affinePoints A) :
    Corepresented.affinePointsEquiv G.affinePointFunctor (corepresentation G) A
      (x ≫ (groupSchemeIso G).inv.hom.hom) = x := by
  rw [Corepresented.affinePointsEquiv_apply, groupSchemeIso_inv]
  change (Lie.pointCoordinates G).symm (Lie.pointCoordinates G x) = x
  exact Equiv.symm_apply_apply _ _

/-- On affine tests the all-test range is the original coordinate weight subgroup. -/
theorem mem_range_weightHom_affine (A : AddSubsemigroup (characterLattice S))
    (R' : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints R') :
    x ∈ (SubgroupFunctor.range (weightHom b e A)).carrier
        ((algSpec (CommRingCat.of k)).obj (op R')) ↔
      x ∈ weightSubgroup b e A R' := by
  rw [mem_range_weightHom_iff, ← pointsEquiv_eq_affinizationFactor,
    Corepresented.pointsEquiv_eq_affinePointsEquiv, affinePointsEquiv_actual]
  let h := Corepresented.isCutOutBy_weightIdeal (corepresentation G)
    (b.toCorepresentedTorusAction e) (exponentSemigroup e A)
  constructor
  · intro hx
    have hx' := h.map_mem (Corepresented.affineSectionsIso R').hom hx
    have hc : G.affinePointFunctor.map (Corepresented.affineSectionsIso R').hom
        (G.affinePointFunctor.map (Corepresented.affineSectionsIso R').inv x) = x := by
      change (G.affinePointFunctor.map (Corepresented.affineSectionsIso R').inv ≫
        G.affinePointFunctor.map (Corepresented.affineSectionsIso R').hom) x = x
      rw [← Functor.map_comp, Iso.inv_hom_id, G.affinePointFunctor.map_id]
      rfl
    rwa [hc] at hx'
  · exact h.map_mem (Corepresented.affineSectionsIso R').inv

/-- Actual tangent membership is vanishing of the excluded coordinate derivatives. -/
theorem mem_tangentSubmodule_range_weightHom_iff
    (A : AddSubsemigroup (characterLattice S)) (X : Additive (lieKernel G k)) :
    X ∈ RelativeRoot.tangentSubmodule (SubgroupFunctor.range (weightHom b e A)) ↔
      ∀ m, m ∉ exponentSemigroup e A → ∀ f : Lie.coordinateAlgebra G,
        infinitesimalCoordinate
          (Corepresented.comp (corepresentation G) (b.toCorepresentedTorusAction e) m f) X = 0 := by
  rw [RelativeRoot.mem_tangentSubmodule, mem_range_weightHom_affine,
    Corepresented.mem_weightSubgroup]
  constructor
  · intro h m hm f
    exact congrArg TrivSqZeroExt.snd (h f m hm)
  · intro h f m hm
    have hD : (Corepresented.coord (corepresentation G) X.toMul.val
        (Corepresented.comp (corepresentation G) (b.toCorepresentedTorusAction e) m f)).snd = 0 :=
      h m hm f
    rw [Corepresented.coord_eq_of_reduction (corepresentation G)
      (affinePointFunctor_reduction X), hD,
      TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.algebraMap_eq_inl']

/-- Every ambient weight space indexed by the semigroup lies in the actual tangent image. -/
theorem actionWeightSpace_le_tangentSubmodule_range_weightHom
    (A : AddSubsemigroup (characterLattice S)) (χ : characterLattice S) (hχ : χ ∈ A) :
    RelativeRoot.actionWeightSpace b χ ≤
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range (weightHom b e A)) := by
  obtain ⟨n, rfl⟩ := (PointedCoordinateWeights.characterEquiv e).surjective χ
  intro X hX
  apply (mem_tangentSubmodule_range_weightHom_iff b e A X).2
  intro m hm f
  apply infinitesimalCoordinate_comp_eq_zero b e m n hX
  intro hmn
  exact hm (hmn.symm ▸ hχ)

/-- An excluded pure weight in the actual tangent image is zero. -/
theorem eq_zero_of_mem_excluded_weight_tangent
    (A : AddSubsemigroup (characterLattice S)) (χ : characterLattice S) (hχ : χ ∉ A)
    {X : Additive (lieKernel G k)} (hW : X ∈ RelativeRoot.actionWeightSpace b χ)
    (hX : X ∈ RelativeRoot.tangentSubmodule
      (SubgroupFunctor.range (weightHom b e A))) : X = 0 := by
  obtain ⟨n, rfl⟩ := (PointedCoordinateWeights.characterEquiv e).surjective χ
  have hXP := (mem_range_weightHom_affine b e A
    (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.toMul.val).1 hX
  have hp : X.toMul.val = 1 :=
    Corepresented.eq_one_of_mem_weightSubgroup_of_snd_comp (corepresentation G)
      (b.toCorepresentedTorusAction e) (exponentSemigroup e A) hχ
      (affinePointFunctor_reduction X) hXP
      (fun f m hm => infinitesimalCoordinate_comp_eq_zero b e m n hW hm f)
  apply Additive.toMul.injective
  exact Subtype.ext hp

/-- The exact tangent image of the actual coordinate quotient is the full semigroup weight span. -/
theorem tangentSubmodule_range_weightHom_eq [LocallyOfFiniteType G.X.hom]
    (A : AddSubsemigroup (characterLattice S)) :
    RelativeRoot.tangentSubmodule (SubgroupFunctor.range (weightHom b e A)) =
      RelativeRoot.semigroupWeightSpan b A := by
  let : IsClosedImmersion (weightHom b e A).hom.hom.left :=
    isClosedSubgroup_weightHom b e A
  let : Mono (weightHom b e A).hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom (weightGroupScheme b e A).X.hom := by
    have h : IsAffineHom ((weightHom b e A).hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  let : LocallyOfFiniteType (weightGroupScheme b e A).X.hom := by
    have h : LocallyOfFiniteType ((weightHom b e A).hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  apply le_antisymm
  · rw [RelativeRoot.tangentSubmodule_eq_iSup_weight_inf b
      (show IsSplitTorus S.toGrp from ⟨I, inferInstance, ⟨e⟩⟩)
      (weightHom b e A) ⟨inferInstance, rfl⟩ (isStable_range_weightHom b e A)]
    refine iSup_le fun χ => ?_
    by_cases hχ : χ ∈ A
    · exact inf_le_left.trans
        (le_iSup (fun ψ : A => RelativeRoot.actionWeightSpace b ψ.val) ⟨χ, hχ⟩)
    · have hz : RelativeRoot.actionWeightSpace b χ ⊓
          RelativeRoot.tangentSubmodule (SubgroupFunctor.range (weightHom b e A)) = ⊥ := by
        apply le_antisymm _ bot_le
        intro X hX
        change X = 0
        exact eq_zero_of_mem_excluded_weight_tangent b e A χ hχ hX.1 hX.2
      rw [hz]
      exact bot_le
  · exact iSup_le fun χ : A =>
      actionWeightSpace_le_tangentSubmodule_range_weightHom b e A χ.val χ.property

/-- The coordinate quotient has the exact Lie image required by semigroup realization. -/
theorem hasLieImage_range_weightHom [LocallyOfFiniteType G.X.hom]
    (A : AddSubsemigroup (characterLattice S)) :
    RelativeRoot.HasLieImage (SubgroupFunctor.range (weightHom b e A))
      (RelativeRoot.semigroupWeightSpan b A) :=
  (RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).2
    (tangentSubmodule_range_weightHom_eq b e A)

end Langlands.GroupScheme.TorusActionCoordinates
