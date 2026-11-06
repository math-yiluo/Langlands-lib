import Langlands.GroupScheme.Torus.CorootCharacterComparison
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeStatement

/-! # Reflection of actual character and coroot comparisons after base change -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {S T Q : CommGroupScheme (Spec (CommRingCat.of k))}

namespace characterLattice

/-- For split tori, membership in the actual character pullback image is
preserved and reflected by every field base map. -/
theorem mem_range_precompose_baseChange_iff
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (f : T ⟶ Q) (χ : characterLattice T) :
    baseChange b T χ ∈
        (precompose ((CommGroupScheme.baseChange b).map f)).toIntLinearMap.range ↔
      χ ∈ (precompose f).toIntLinearMap.range := by
  constructor
  · rintro ⟨ψ', hψ'⟩
    obtain ⟨ψ, rfl⟩ := (hQ.characterLattice_baseChange_bijective b Q).surjective ψ'
    refine ⟨ψ, (hT.characterLattice_baseChange_bijective b T).injective ?_⟩
    change baseChange b T (f ≫ ψ) = baseChange b T χ
    rw [baseChange_precomp]
    exact hψ'
  · rintro ⟨ψ, rfl⟩
    exact ⟨baseChange b Q ψ, (baseChange_precomp b f ψ).symm⟩

/-- The canonical base-change equivalence on the actual pullback-image
lattices of a homomorphism between split tori. -/
def pullbackImageBaseChangeEquiv
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) (f : T ⟶ Q) :
    (precompose f).toIntLinearMap.range ≃ₗ[ℤ]
      (precompose ((CommGroupScheme.baseChange b).map f)).toIntLinearMap.range :=
  (baseChangeEquiv b T hT).toIntLinearEquiv.ofSubmodules _ _ (by
    ext χ'
    obtain ⟨χ, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).surjective χ'
    rw [mem_range_precompose_baseChange_iff b hT hQ f]
    constructor
    · rintro ⟨ψ, hψ, h⟩
      change baseChange b T ψ = baseChange b T χ at h
      exact (hT.characterLattice_baseChange_bijective b T).injective h ▸ hψ
    · intro hχ
      exact ⟨χ, hχ, rfl⟩)

/-- The image-lattice equivalence is actual character base change. -/
@[simp] theorem pullbackImageBaseChangeEquiv_coe
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) (f : T ⟶ Q)
    (χ : (precompose f).toIntLinearMap.range) :
    (pullbackImageBaseChangeEquiv b hT hQ f χ :
        characterLattice ((CommGroupScheme.baseChange b).obj T)) =
      baseChange b T χ := rfl

/-- Injectivity of actual character pullback between split tori is invariant
under every field base map. -/
theorem precompose_injective_baseChange_iff
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) (f : T ⟶ Q) :
    Function.Injective (precompose ((CommGroupScheme.baseChange b).map f)) ↔
      Function.Injective (precompose f) := by
  constructor
  · intro hf χ ψ h
    apply (hQ.characterLattice_baseChange_bijective b Q).injective
    apply hf
    change (CommGroupScheme.baseChange b).map f ≫ baseChange b Q χ =
      (CommGroupScheme.baseChange b).map f ≫ baseChange b Q ψ
    rw [← baseChange_precomp, ← baseChange_precomp]
    exact congrArg (baseChange b T) h
  · intro hf χ' ψ' h
    obtain ⟨χ, rfl⟩ := (hQ.characterLattice_baseChange_bijective b Q).surjective χ'
    obtain ⟨ψ, rfl⟩ := (hQ.characterLattice_baseChange_bijective b Q).surjective ψ'
    apply congrArg (baseChange b Q)
    apply hf
    apply (hT.characterLattice_baseChange_bijective b T).injective
    change baseChange b T (f ≫ χ) = baseChange b T (f ≫ ψ)
    rw [baseChange_precomp, baseChange_precomp]
    exact h

/-- The canonical actual lattice transport preserves and reflects the
annihilator of any selected family of coroots. -/
theorem mem_corootAnnihilator_baseChange_iff
    (hT : IsSplitTorus T.toGrp)
    {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (s : Set J) (χ : characterLattice T) :
    baseChange b T χ ∈
        Langlands.RootDatum.corootAnnihilator (SplitRootDatum.baseChange b T hT P) s ↔
      χ ∈ Langlands.RootDatum.corootAnnihilator P s := by
  simp only [Langlands.RootDatum.mem_corootAnnihilator,
    SplitRootDatum.baseChange_coroot, SplitRootDatum.baseChange_pairing]

/-- The full actual character-image comparison, including injectivity, can
be checked after any further field base change once both tori are split. -/
theorem coroot_character_comparison_baseChange_iff
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (f : T ⟶ Q) {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (s : Set J) :
    (Function.Injective (precompose ((CommGroupScheme.baseChange b).map f)) ∧
      ∀ χ, χ ∈ (precompose ((CommGroupScheme.baseChange b).map f)).toIntLinearMap.range ↔
        χ ∈ Langlands.RootDatum.corootAnnihilator (SplitRootDatum.baseChange b T hT P) s) ↔
    (Function.Injective (precompose f) ∧
      ∀ χ, χ ∈ (precompose f).toIntLinearMap.range ↔
        χ ∈ Langlands.RootDatum.corootAnnihilator P s) := by
  apply and_congr (precompose_injective_baseChange_iff b hT hQ f)
  constructor
  · intro h χ
    simpa only [mem_range_precompose_baseChange_iff b hT hQ f,
      mem_corootAnnihilator_baseChange_iff b hT P s] using h (baseChange b T χ)
  · intro h χ'
    obtain ⟨χ, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).surjective χ'
    simpa only [mem_range_precompose_baseChange_iff b hT hQ f,
      mem_corootAnnihilator_baseChange_iff b hT P s] using h χ

end characterLattice

namespace SplitRootDatum

/-- The selected integral coroot span is carried to its canonical
base-changed span by actual cocharacter pullback. -/
theorem map_selected_corootSpan
    (hT : IsSplitTorus T.toGrp) {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (s : Set J) :
    (Submodule.span ℤ (P.coroot '' s)).map
        (cocharacterLattice.baseChangeEquiv b T hT).toIntLinearEquiv.toLinearMap =
      Submodule.span ℤ ((baseChange b T hT P).coroot '' s) := by
  rw [Submodule.map_span, Set.image_image]
  rfl

/-- An actual torus homomorphism's integral coroot-span image comparison
is invariant under canonical split lattice base change. -/
theorem corootSpan_image_baseChange_iff
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (φ : S ⟶ T) {J : Type v} {L : Type w}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (R : RootDatum L (characterLattice S) (cocharacterLattice S)) (s : Set J) :
    ((baseChange b S hS R).corootSpan ℤ).map
        (RealTorusSpace.cocharacterMapInt ((CommGroupScheme.baseChange b).map φ)) =
        Submodule.span ℤ ((baseChange b T hT P).coroot '' s) ↔
      (R.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
        Submodule.span ℤ (P.coroot '' s) := by
  let eS : cocharacterLattice S ≃ₗ[ℤ]
      cocharacterLattice ((CommGroupScheme.baseChange b).obj S) :=
    (cocharacterLattice.baseChangeEquiv b S hS).toIntLinearEquiv
  let eT : cocharacterLattice T ≃ₗ[ℤ]
      cocharacterLattice ((CommGroupScheme.baseChange b).obj T) :=
    (cocharacterLattice.baseChangeEquiv b T hT).toIntLinearEquiv
  have hcomp : eT.toLinearMap.comp (RealTorusSpace.cocharacterMapInt φ) =
      (RealTorusSpace.cocharacterMapInt ((CommGroupScheme.baseChange b).map φ)).comp
        eS.toLinearMap := by
    apply LinearMap.ext
    intro ν
    exact cocharacterLattice.baseChange_comp b ν φ
  have hleft :
      ((R.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ)).map eT.toLinearMap =
        ((baseChange b S hS R).corootSpan ℤ).map
          (RealTorusSpace.cocharacterMapInt ((CommGroupScheme.baseChange b).map φ)) := by
    rw [← Submodule.map_comp, hcomp, Submodule.map_comp]
    exact congrArg (Submodule.map
      (RealTorusSpace.cocharacterMapInt ((CommGroupScheme.baseChange b).map φ)))
      (map_corootSpan b S hS R)
  rw [← hleft, ← map_selected_corootSpan b hT P s]
  exact (Submodule.map_injective_of_injective eT.injective).eq_iff

end SplitRootDatum

end Langlands.GroupScheme
