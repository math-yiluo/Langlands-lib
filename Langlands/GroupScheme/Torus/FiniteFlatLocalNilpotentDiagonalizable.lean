import Langlands.Algebra.CoalgebraBaseChangeDual
import Langlands.GroupScheme.Torus.FiniteFlatLocalDiagonalizableSubgroup
import Langlands.GroupScheme.HopfBaseChange
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Finite flat local lifting of diagonalizability through nilpotent ideals -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped TensorProduct

namespace Langlands.GroupScheme.Diagonalizable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A diagonalizable Hopf spectrum has coordinates spanned by group-like elements. -/
theorem span_groupLike_of_diagonalizable_hopfSpec {R : CommRingCat.{u}}
    (A : CommHopfAlgCat.{u} R)
    (hA : RelativeMultiplicativeType.IsDiagonalizable ((hopfSpec R).obj (op A))) :
    Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤ := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hA
  let e' := e ≪≫ baseChangeIso (Gm.toSpecZ (Spec R)) Λ ≪≫ (hopfSpecIso R Λ).symm
  let i : hopfAlgebra R Λ ≅ A := (hopfSpec.fullyFaithful.preimageIso e').unop
  let d := (CommHopfAlgCat.ofIso i).toCoalgEquiv
  apply top_unique
  intro a _
  obtain ⟨x, rfl⟩ := d.surjective a
  have hx : x ∈ Submodule.span R {x : hopfAlgebra R Λ | IsGroupLikeElem R x} := by
    rw [AddMonoidAlgebra.span_isGroupLikeElem]
    exact Submodule.mem_top
  have hm := Submodule.mem_map_of_mem (f := d.toLinearMap) hx
  rw [Submodule.map_span] at hm
  exact Submodule.span_mono (Set.image_subset_iff.mpr (fun _ hx => hx.map d)) hm

variable {R : CommRingCat.{u}} [IsLocalRing R]
    {H : GroupScheme (Spec R)} [IsAffine H.X.left] [IsFinite H.X.hom] [Flat H.X.hom]

/-- Reconstruction of the actual finite flat local group from group-like spanning. -/
def finiteFlatLocalIsoOfGroupLikeSpan
    (hspan : Submodule.span R {a : AffineCoordinates.hopfAlgebra H |
      IsGroupLikeElem R a} = ⊤) :
    H ≅ (groupScheme R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))).toGrp := by
  let : Module.Finite R (AffineCoordinates.hopfAlgebra H) := finite_hopfAlgebra
  let : Module.Flat R (AffineCoordinates.hopfAlgebra H) := flat_hopfAlgebra
  let e : AffineCoordinates.hopfAlgebra H ≃ₐc[R]
      AddMonoidAlgebra R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H))) :=
    (finiteFlatLocalBialgEquiv hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv R R (GroupLike R (AffineCoordinates.hopfAlgebra H)))
  exact (AffineCoordinates.isoOfBialgEquiv H
    (hopfAlgebra R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))) e).symm ≪≫
      hopfSpecIso R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))

/-- Group-like spanning makes a finite flat affine local group diagonalizable. -/
theorem isDiagonalizable_of_groupLike_span
    (hspan : Submodule.span R {a : AffineCoordinates.hopfAlgebra H |
      IsGroupLikeElem R a} = ⊤) :
    RelativeMultiplicativeType.IsDiagonalizable H := by
  let : Module.Finite R (AffineCoordinates.hopfAlgebra H) := finite_hopfAlgebra
  let : Module.Flat R (AffineCoordinates.hopfAlgebra H) := flat_hopfAlgebra
  let : Finite (GroupLike R (AffineCoordinates.hopfAlgebra H)) :=
    finite_groupLike_of_finite_flat hspan
  refine ⟨Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)), inferInstance,
    inferInstance, ?_⟩
  exact ⟨finiteFlatLocalIsoOfGroupLikeSpan hspan ≪≫
    (baseChangeIso (Gm.toSpecZ (Spec R))
      (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))).symm⟩

/-- A diagonalizable actual nilpotent reduction supplies group-like spanning of
all the original affine Hopf coordinates. -/
theorem span_groupLike_of_diagonalizable_reduction
    (I : Ideal R) (hI : IsNilpotent I)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H)) :
    Submodule.span R {a : AffineCoordinates.hopfAlgebra H |
      IsGroupLikeElem R a} = ⊤ := by
  let A := AffineCoordinates.hopfAlgebra H
  let : Module.Finite R A := finite_hopfAlgebra
  let : Module.Flat R A := flat_hopfAlgebra
  have hIproper : I ≠ ⊤ := by
    intro h
    obtain ⟨n, hn⟩ := hI
    rw [h, ← Ideal.one_eq_top, one_pow] at hn
    exact one_ne_zero hn
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIproper
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let e : (hopfSpec (CommRingCat.of (R ⧸ I))).obj
      (op (HopfCoordinates.scalarExtension R (R ⧸ I) A)) ≅
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H) :=
    (HopfCoordinates.baseChangeSpecIso R (R ⧸ I) A).symm ≪≫
    (GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).mapIso
      (AffineCoordinates.hopfSpecIso H)
  have hdiag : RelativeMultiplicativeType.IsDiagonalizable
      ((hopfSpec (CommRingCat.of (R ⧸ I))).obj
        (op (HopfCoordinates.scalarExtension R (R ⧸ I) A))) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso e hH
  have hspan := span_groupLike_of_diagonalizable_hopfSpec
    (R := CommRingCat.of (R ⧸ I)) (HopfCoordinates.scalarExtension R (R ⧸ I) A) hdiag
  have hspan' : Submodule.span (R ⧸ I)
      {x : (R ⧸ I) ⊗[R] A | IsGroupLikeElem (R ⧸ I) x} = ⊤ := hspan
  obtain ⟨ι, inst, b, hb⟩ := exists_groupLike_basis hspan'
  exact Langlands.CoalgebraBaseChangeDual.span_groupLike_eq_top_of_reduced_basis
    (C := A) I hI b hb

/-- A finite flat affine group over a local ring is diagonalizable whenever
its actual reduction through a nilpotent scalar ideal is diagonalizable. -/
theorem isDiagonalizable_of_nilpotent_reduction
    (I : Ideal R) (hI : IsNilpotent I)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H)) :
    RelativeMultiplicativeType.IsDiagonalizable H :=
  isDiagonalizable_of_groupLike_span (span_groupLike_of_diagonalizable_reduction I hI hH)

end Langlands.GroupScheme.Diagonalizable
