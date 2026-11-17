import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeLocality
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupStatement
import Langlands.GroupScheme.Torus.FlatDiagonalizableSubgroup
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Sites.Pretopology

/-! # Reduction of multiplicative-type closed subgroups to Hopf reconstruction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeMultiplicativeType

variable {S : Scheme.{u}} {G : GroupScheme S}

local instance : MorphismProperty.IsStableUnderComposition
    (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) where
  comp_mem f g hf hg := by
    let : Flat f := hf.1
    let : Flat g := hg.1
    let : LocallyOfFinitePresentation f := hf.2
    let : LocallyOfFinitePresentation g := hg.2
    exact ⟨inferInstance, inferInstance⟩

/-- Multiplicative type can be checked on any open cover of the base. -/
theorem IsMultiplicativeType.of_openCover (𝒰 : Scheme.OpenCover.{u} S)
    (hG : ∀ i, IsMultiplicativeType ((GroupScheme.baseChange (𝒰.f i)).obj G)) :
    IsMultiplicativeType G :=
  IsMultiplicativeType.of_fppfCover
    (𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)) hG

end RelativeMultiplicativeType

namespace AffineCoordinates

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} [IsAffine H.X.left]

/-- Local finite presentation of an affine group gives finite presentation
of its actual coordinate Hopf algebra. -/
theorem finitePresentation_hopfAlgebra [LocallyOfFinitePresentation H.X.hom] :
    Algebra.FinitePresentation R (hopfAlgebra H) := by
  have h : LocallyOfFinitePresentation
      ((hopfSpecIso H).hom.hom.hom.left ≫ H.X.hom) := by infer_instance
  rw [Over.w] at h
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
    (algebraMap R (hopfAlgebra H)))) at h
  exact RingHom.finitePresentation_algebraMap.mp
    ((LocallyOfFinitePresentation.SpecMap_iff _).mp h)

end AffineCoordinates

/-- Internal Hopf reconstruction criterion for the closed-subgroup theorem:
a flat finitely presented commutative Hopf algebra spanned by group-like
elements has a spectrum of multiplicative type. -/
def FlatGroupLikeHopfMultiplicativeTypeStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (A : CommHopfAlgCat.{u} R),
    Module.Flat R A → Algebra.FinitePresentation R A →
    Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤ →
    RelativeMultiplicativeType.IsMultiplicativeType ((hopfSpec R).obj (op A))

namespace RelativeMultiplicativeType

/-- The Hopf criterion applies to actual affine coordinates of a closed
subgroup of a ring-level diagonalizable group. -/
theorem isMultiplicativeType_closedSubgroup_overRing_of_hopf
    (hcore : FlatGroupLikeHopfMultiplicativeTypeStatement.{u})
    {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    {H : GroupScheme (Spec R)} (i : H ⟶ (Diagonalizable.groupScheme R Λ).toGrp)
    (hi : IsClosedSubgroup i) [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] :
    IsMultiplicativeType H := by
  let : IsAffine (Diagonalizable.groupScheme R Λ).X.left :=
    isAffine_of_isAffineHom (Diagonalizable.groupScheme R Λ).X.hom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have h := hcore R (AffineCoordinates.hopfAlgebra H)
    Diagonalizable.flat_hopfAlgebra AffineCoordinates.finitePresentation_hopfAlgebra
    (Diagonalizable.span_groupLike_of_closedSubgroup i hi)
  exact IsMultiplicativeType.of_iso (AffineCoordinates.hopfSpecIso H).symm h

/-- Over an affine base, a diagonalizable ambient group is identified with
its ring-level model before applying the coordinate criterion. -/
theorem IsDiagonalizable.isMultiplicativeType_closedSubgroup_overSpec_of_hopf
    (hcore : FlatGroupLikeHopfMultiplicativeTypeStatement.{u})
    {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)} (hG : IsDiagonalizable G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] : IsMultiplicativeType H := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hG
  let e' := e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) Λ
  exact isMultiplicativeType_closedSubgroup_overRing_of_hopf hcore
    (i ≫ e'.hom) (hi.comp_iso e')

/-- The affine-base reduction extends to a diagonalizable ambient group
over any scheme by its affine open cover. -/
theorem IsDiagonalizable.isMultiplicativeType_closedSubgroup_of_hopf
    (hcore : FlatGroupLikeHopfMultiplicativeTypeStatement.{u})
    {S : Scheme.{u}} {H G : GroupScheme S} (hG : IsDiagonalizable G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] : IsMultiplicativeType H := by
  apply IsMultiplicativeType.of_openCover S.affineOpenCover.openCover
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : Flat (B.obj H).X.hom := by
    change Flat (pullback.snd _ _)
    infer_instance
  let : LocallyOfFinitePresentation (B.obj H).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd _ _)
    infer_instance
  change IsMultiplicativeType (B.obj H)
  exact (hG.baseChange b).isMultiplicativeType_closedSubgroup_overSpec_of_hopf hcore
    (R := S.affineOpenCover.X k) (B.map i) (hi.baseChange b)

end RelativeMultiplicativeType

/-- Concrete reduction of the unchanged arbitrary-base closed-subgroup
statement to the flat group-like Hopf reconstruction criterion. -/
theorem relativeMultiplicativeTypeClosedSubgroup_of_flatGroupLikeHopf
    (hcore : FlatGroupLikeHopfMultiplicativeTypeStatement.{u}) :
    RelativeMultiplicativeTypeClosedSubgroupStatement.{u} := by
  intro S H G i hG hi hflat hfp
  let : Flat H.X.hom := hflat
  let : LocallyOfFinitePresentation H.X.hom := hfp
  obtain ⟨𝒰, h𝒰⟩ := hG
  apply RelativeMultiplicativeType.IsMultiplicativeType.of_fppfCover 𝒰
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : Flat (B.obj H).X.hom := by
    change Flat (pullback.snd _ _)
    infer_instance
  let : LocallyOfFinitePresentation (B.obj H).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd _ _)
    infer_instance
  exact (h𝒰 k).isMultiplicativeType_closedSubgroup_of_hopf hcore
    (B.map i) (hi.baseChange b)

end Langlands.GroupScheme
