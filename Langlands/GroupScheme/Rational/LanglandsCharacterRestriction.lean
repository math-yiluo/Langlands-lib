import Langlands.GroupScheme.Rational.LanglandsInvariantForm
import Langlands.GroupScheme.Rational.LanglandsDecompositionStatement
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsProof
import Langlands.Geometry.Building.RealTorusDuality
import Mathlib.LinearAlgebra.Projection

/-! # Character restriction on the coroot annihilator of a standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.LinearAlgebra

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- A positive definite symmetric form splits every subspace orthogonally. -/
theorem isCompl_orthogonal_of_positive [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (W : Submodule ℝ E) :
    IsCompl W (B.orthogonal W) := by
  apply (B.isCompl_orthogonal_iff_disjoint (fun x y h => by rwa [hs] at h)).mpr
  rw [Submodule.disjoint_def]
  intro x hx horth
  by_contra hn
  exact (hp x hn).ne' (horth x hx)

/-- Projection onto a subspace along its orthogonal complement for a positive form. -/
def positiveFormProjection [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (W : Submodule ℝ E) : E →ₗ[ℝ] E :=
  W.projection (B.orthogonal W) (isCompl_orthogonal_of_positive B hs hp W)

/-- A complement of the kernel of a surjective linear map contains a unique lift. -/
theorem existsUnique_preimage_of_isCompl (f : E →ₗ[ℝ] F)
    (hf : Function.Surjective f) (W : Submodule ℝ E) (hc : IsCompl f.ker W) (x : F) :
    ∃! y : E, y ∈ W ∧ f y = x := by
  obtain ⟨y, rfl⟩ := hf x
  have hy : y ∈ f.ker ⊔ W := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
  have hfb : f b = f y := by
    rw [← hab, map_add, ha, zero_add]
  refine ⟨b, ⟨hb, hfb⟩, ?_⟩
  rintro z ⟨hz, hfz⟩
  apply sub_eq_zero.mp
  apply (Submodule.disjoint_def.mp hc.disjoint) (z - b)
  · change f (z - b) = 0
    rw [map_sub, hfz, hfb, sub_self]
  · exact W.sub_mem hz hb

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An injective map on real cocharacters gives a surjective actual real restriction. -/
theorem restrictReal_surjective_of_cocharacterMapReal_injective
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    (hf : Function.Injective (cocharacterMapReal f)) :
    Function.Surjective (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)) := by
  intro x
  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective hf
    (characterDualEquiv hA x)
  refine ⟨(characterDualEquiv hT).symm φ, ?_⟩
  apply (characterDualEquiv hA).injective
  apply LinearMap.ext
  intro v
  change pair A
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
      ((characterDualEquiv hT).symm φ)) v = pair A x v
  rw [← pair_cocharacterMapReal]
  have hv := congrArg (fun ψ : Module.Dual ℝ (V A) => ψ v) hφ
  simpa only [LinearMap.dualMap_apply, LinearMap.comp_apply,
    ← characterDualEquiv_apply hT, LinearEquiv.apply_symm_apply,
    characterDualEquiv_apply] using hv

/-- The root-annihilator cocharacter image determines the character restriction kernel. -/
theorem ker_restrictReal_eq_rootSpan_of_range
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    (J : Set (characterLattice T))
    (hf : (cocharacterMapReal f).range = rootAnnihilator T J) :
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker =
      Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J) := by
  rw [ker_restrictReal_eq_characterAnnihilator_range hA, hf,
    rootAnnihilator_eq_cocharacterAnnihilator,
    characterAnnihilator_cocharacterAnnihilator hT]

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)

/-- For a compatible actual standard Levi, restriction identifies the coroot
annihilator with the full real character space of its split component. -/
theorem langlandsCharacterRestriction :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
    ∀ (D : RelativeRootReflectionData i) (B : LinearMap.BilinForm ℝ (Vstar T)),
      IsWeylInvariantInnerProduct i B →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (J : Set (characterLattice T)) (f : A ⟶ T),
      (⟨T, i, ν, J, f⟩ : ParabolicRootPresentationData A G).IsCompatible p l a →
      ∀ x : Vstar A, ∃! y : Vstar T, y ∈ corootAnnihilator i D J ∧
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = x := by
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro ν hν D B hB P M p l a J f hcompat x
  have hjc : IsClosedSubgroup (l ≫ p) :=
    hcompat.levi.isClosedSubgroup.comp hcompat.parabolic.isClosedSubgroup
  let : IsClosedImmersion (l ≫ p).hom.hom.left := hjc
  have hrep : (standardLevi i ν J).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, hcompat.levi_eq⟩
  obtain ⟨_, f', hf', _, hinj, himage, _⟩ :=
    (standardLeviCentralDirections.2 k G hG T i hi ν hν J
      hcompat.subset_simpleRoots M (l ≫ p) hjc hrep).2 A a hcompat.splitComponent
  have hff : f' = f :=
    eq_of_groupHom_comp_eq i (l ≫ p) hf' hcompat.factor_comp
  subst f'
  have hA : IsSplitTorus A.toGrp := hcompat.splitComponent.1.1.1
  have hT : IsSplitTorus T.toGrp := hi.1.1
  let := hT.finite_realCharacterSpace
  have hker := ker_restrictReal_eq_rootSpan_of_range hA hT f J himage
  have horth := corootAnnihilator_eq_orthogonal i D B hB J
    (fun α hα => (hcompat.subset_simpleRoots hα).1.1)
  have hc : IsCompl
      (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker
      (corootAnnihilator i D J) := by
    rw [hker, horth]
    exact Langlands.LinearAlgebra.isCompl_orthogonal_of_positive B hB.1 hB.2.1 _
  exact Langlands.LinearAlgebra.existsUnique_preimage_of_isCompl _
    (restrictReal_surjective_of_cocharacterMapReal_injective hA hT f hinj) _ hc x

end Langlands.GroupScheme
