import Langlands.GroupScheme.Torus.DiagonalizableHomMonomialLocus
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerOpen
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Local character restrictions for diagonalizable homomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

private theorem baseChange_eq_of_points_on_open
    {S : Scheme.{u}} {H G : GroupScheme S} (f g : H ⟶ G) (W : S.Opens)
    (h : ∀ (U : Over S) (x : U ⟶ H.X), Set.range U.hom ⊆ W →
      x ≫ f.hom.hom = x ≫ g.hom.hom) :
    (baseChange W.ι).map f = (baseChange W.ι).map g := by
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv W.ι G T).injective
  rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_comp]
  apply h
  rintro _ ⟨t, rfl⟩
  exact (T.hom t).property

variable {R : CommRingCat.{u}} {Λ Γ : Type u} [AddCommGroup Λ] [AddCommGroup Γ]
    (f : (groupScheme R Γ).toGrp ⟶ (groupScheme R Λ).toGrp)

/-- Near each point of the base, an actual diagonalizable homomorphism is
restriction along a single homomorphism of full character groups. -/
theorem exists_open_restriction [AddGroup.FG Λ] (s : Spec R) :
    ∃ (W : (Spec R).Opens) (p : Λ →+ Γ), s ∈ W ∧
      (baseChange W.ι).map f = (baseChange W.ι).map (restrictMap R p) := by
  let C : CommAlgCat.{u} R := CommAlgCat.of R s.asIdeal.ResidueField
  let a : DiagonalizableCharacter.baseAlg R ⟶ C :=
    CommAlgCat.ofHom (Algebra.ofId R _)
  obtain ⟨p, e, he, hea, hloc⟩ := exists_idempotent_restriction_locus f a
  let W := (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv e)
  have hs : s ∈ W := by
    dsimp [W]
    rw [basicOpen_eq_of_affine]
    change e ∉ s.asIdeal
    intro hem
    have hz : a.hom e = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hem
    exact one_ne_zero (hea.symm.trans hz)
  have he' : IsIdempotentElem ((Scheme.ΓSpecIso R).inv e) := by
    change (Scheme.ΓSpecIso R).inv e * (Scheme.ΓSpecIso R).inv e =
      (Scheme.ΓSpecIso R).inv e
    rw [← map_mul, he.eq]
  refine ⟨W, p, hs, ?_⟩
  apply baseChange_eq_of_points_on_open
  intro U x hx
  apply hloc U x
  change U.hom.appTop ((Scheme.ΓSpecIso R).inv e) = 1
  exact (range_subset_basicOpen_idempotent_iff U.hom he').mp hx

/-- The chosen open base cover on which the homomorphism is a character restriction. -/
def restrictionCover [AddGroup.FG Λ] : (Spec R).OpenCover :=
  let W := fun s => (exists_open_restriction f s).choose
  Scheme.Cover.mkOfCovers (Spec R) (fun s => (W s).toScheme) (fun s => (W s).ι)
    (fun s => ⟨s, ⟨⟨s, (exists_open_restriction f s).choose_spec.choose_spec.1⟩, rfl⟩⟩)
    (fun _ => inferInstance)

/-- The full character map chosen on each member of the restriction cover. -/
def restrictionCharacterMap [AddGroup.FG Λ] (s : (restrictionCover f).I₀) : Λ →+ Γ :=
  (exists_open_restriction f s).choose_spec.choose

/-- The cover retains equality of the actual base-changed group-scheme maps. -/
theorem restrictionCover_map_eq [AddGroup.FG Λ] (s : (restrictionCover f).I₀) :
    (baseChange ((restrictionCover f).f s)).map f =
      (baseChange ((restrictionCover f).f s)).map
        (restrictMap R (restrictionCharacterMap f s)) :=
  (exists_open_restriction f s).choose_spec.choose_spec.2

end Langlands.GroupScheme.Diagonalizable
