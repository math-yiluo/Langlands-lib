import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Factoring a finite morphism through a supplied quotient -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- Any relation equalized by an affine morphism has its classes contained in affine
opens, by taking preimages of affine charts around the common image. -/
lemma exists_affine_open_of_equalizing_affine {R X Y : Scheme.{u}} (t s : R ⟶ X)
    (f : X ⟶ Y) [IsAffineHom f] (h : t ≫ f = s ≫ f) (x : X) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∀ r : R, s r = x → t r ∈ W := by
  let V := (Y.affineCover.f (Y.affineCover.idx (f x))).opensRange
  refine ⟨f ⁻¹ᵁ V, (isAffineOpen_opensRange _).preimage _, fun r hr ↦ ?_⟩
  have h' : f (t r) = f (s r) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : R ⟶ Y ↦ g r) h
  rw [Scheme.Hom.mem_preimage, h', hr]
  exact Y.affineCover.covers (f x)

/-- A separated locally finite type morphism is finite if its precomposition with a
surjective morphism is finite. -/
lemma isFinite_of_surjective_precomp {X Q Y : Scheme.{u}} (q : X ⟶ Q) (g : Q ⟶ Y)
    [Surjective q] [IsSeparated g] [LocallyOfFiniteType g] [IsFinite (q ≫ g)] : IsFinite g := by
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective q g
  have : IsProper g := ⟨⟩
  apply (IsFinite.iff_isProper_and_locallyQuasiFinite g).mpr
  refine ⟨inferInstance, LocallyQuasiFinite.of_finite_preimage_singleton g fun y ↦ ?_⟩
  refine (((q ≫ g).finite_preimage_singleton y).image q).subset fun z hz ↦ ?_
  obtain ⟨x, rfl⟩ := q.surjective z
  refine ⟨x, ?_, rfl⟩
  simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hz

/-- The descended morphism obtained from an invariant scheme map and a supplied effective
quotient. The given kernel-pair projections are used in the equality test. -/
def descendInvariantMap {X Q R Y : Scheme.{u}} (q : X ⟶ Q)
    [Flat q] [Surjective q] [QuasiCompact q] {t s : R ⟶ X} (hQ : IsPullback t s q q)
    (f : X ⟶ Y) (hf : t ≫ f = s ≫ f) : Q ⟶ Y :=
  Classical.choose (IsRegularEpi.exists_of_isKernelPair q hQ f hf)

@[reassoc (attr := simp)]
lemma descendInvariantMap_fac {X Q R Y : Scheme.{u}} (q : X ⟶ Q)
    [Flat q] [Surjective q] [QuasiCompact q] {t s : R ⟶ X} (hQ : IsPullback t s q q)
    (f : X ⟶ Y) (hf : t ≫ f = s ≫ f) : q ≫ descendInvariantMap q hQ f hf = f :=
  Classical.choose_spec (IsRegularEpi.exists_of_isKernelPair q hQ f hf)

/-- If the original invariant map is finite, its descend is finite once it is separated
and locally of finite type. -/
lemma isFinite_descendInvariantMap {X Q R Y : Scheme.{u}} (q : X ⟶ Q)
    [Flat q] [Surjective q] [QuasiCompact q] {t s : R ⟶ X} (hQ : IsPullback t s q q)
    (f : X ⟶ Y) (hf : t ≫ f = s ≫ f) [IsFinite f]
    [IsSeparated (descendInvariantMap q hQ f hf)]
    [LocallyOfFiniteType (descendInvariantMap q hQ f hf)] :
    IsFinite (descendInvariantMap q hQ f hf) := by
  have : IsFinite (q ≫ descendInvariantMap q hQ f hf) := by rw [descendInvariantMap_fac]; infer_instance
  exact isFinite_of_surjective_precomp q _

end Langlands.AlgebraicGeometry
