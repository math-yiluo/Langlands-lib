import Langlands.AlgebraicGeometry.FaithfullyFlatQuasiAffineDescent
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Extensive

/-! # Quasi-affine descent through finite affine refinements -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.QuasiAffineCoverDescent

variable {I : Type v} [Small.{u} I] (X : I → Scheme.{u})

/-- The coproduct of the canonical maps to affine hulls. -/
def coproductHullMap : (∐ X) ⟶ ∐ fun i => Spec Γ(X i, ⊤) :=
  Sigma.desc fun i => (X i).toSpecΓ ≫ Sigma.ι (fun i => Spec Γ(X i, ⊤)) i

instance [∀ i, (X i).IsQuasiAffine] : IsOpenImmersion (coproductHullMap X) := by
  apply isOpenImmersion_sigmaDesc
  intro i j hij
  change Disjoint _ _
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have he := (sigmaι_eq_iff (fun i => Spec Γ(X i, ⊤)) j i _ _).mp hy
  exact hij (congrArg Sigma.fst he).symm

/-- A finite coproduct of quasi-affine schemes is quasi-affine. -/
theorem isQuasiAffine_sigma [Finite I] [∀ i, (X i).IsQuasiAffine] :
    (∐ X).IsQuasiAffine := by
  have : Finite (sigmaOpenCover X).I₀ := by
    change Finite I
    infer_instance
  have (i : (sigmaOpenCover X).I₀) : CompactSpace ((sigmaOpenCover X).X i) := by
    change I at i
    change CompactSpace (X i)
    have h : (X i).IsQuasiAffine := inferInstance
    exact h.toCompactSpace
  have : CompactSpace (∐ X : Scheme.{u}) := (sigmaOpenCover X).compactSpace
  exact Scheme.IsQuasiAffine.of_isImmersion (coproductHullMap X)

/-- The canonical open presentation for a finite coproduct of quasi-affine schemes. -/
def finiteCoproductOpenIso [Finite I] [∀ i, (X i).IsQuasiAffine] :
    (∐ X) ≅ (coproductHullMap X).opensRange.toScheme :=
  (coproductHullMap X).isoOpensRange

/-- Descent over a finite affine family of flat maps covering an affine base. -/
theorem isQuasiAffine_of_finite_affine_cover
    {I : Type u} [Finite I] {S X : Scheme.{u}} (f : X ⟶ S)
    (B : I → Scheme.{u}) (q : ∀ i, B i ⟶ S)
    [IsAffine S] [∀ i, IsAffine (B i)] [∀ i, Flat (q i)]
    (hq : ∀ s : S, ∃ i, ∃ b : B i, q i b = s)
    [∀ i, (pullback f (q i)).IsQuasiAffine] : X.IsQuasiAffine := by
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  let g : (∐ B) ⟶ S := Sigma.desc q
  have : Flat g := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstanceAs (Flat (q i))
  have : Surjective g := by
    constructor
    intro s
    obtain ⟨i, b, rfl⟩ := hq s
    exact ⟨Sigma.ι B i b, by simp [g, ← Scheme.Hom.comp_apply]⟩
  let A : PUnit → Scheme.{u} := fun _ => X
  let a : ∀ i, A i ⟶ S := fun _ => f
  have hp := FinitaryPreExtensive.isPullback_sigmaDesc a q
  have he : IsPullback (coproductUniqueIso A).hom (Sigma.desc a) f (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by ext; simp [a]⟩
  have h := hp.paste_horiz he
  simp only [Category.comp_id] at h
  have : (∐ fun p : PUnit × I => pullback (a p.1) (q p.2)).IsQuasiAffine :=
    isQuasiAffine_sigma _
  exact FaithfullyFlatQuasiAffineDescent.isQuasiAffine_of_isPullback h

end Langlands.AlgebraicGeometry.QuasiAffineCoverDescent
