import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.NormalQuotientGroup
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Group structure and dimension on actual homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient

section Base

variable {S : Scheme.{u}} {G H : GroupScheme S} {i : H ⟶ G}
    (D : HomogeneousQuotient i) (hn : (SubgroupFunctor.range i).IsNormal)

local instance instHomogeneousQuotientGroup1 : Smooth D.projection.left := D.smooth_projection
local instance instHomogeneousQuotientGroup2 : Surjective D.projection.left := D.surjective_projection
local instance instHomogeneousQuotientGroup3 : QuasiCompact D.projection.left := D.quasiCompact_projection

/-- The group structure descended to the supplied actual homogeneous quotient. -/
abbrev groupScheme : GroupScheme S :=
  NormalQuotient.groupScheme G (SubgroupFunctor.range i) hn D.projection D.fibers

/-- The supplied projection, regarded as a group-scheme homomorphism. -/
def groupProjection : G ⟶ D.groupScheme hn :=
  NormalQuotient.hom G (SubgroupFunctor.range i) hn D.projection D.fibers

/-- The group projection has exactly the original underlying morphism. -/
theorem groupProjection_hom : (D.groupProjection hn).hom.hom = D.projection := rfl

/-- Its represented kernel is the prescribed subgroup on every test scheme. -/
theorem groupProjection_isFppfQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) (D.groupProjection hn) :=
  NormalQuotient.isFppfQuotient G (SubgroupFunctor.range i) hn D.projection D.fibers

/-- The descended group projection keeps the original smoothness. -/
theorem groupProjection_smooth : Smooth (D.groupProjection hn).hom.hom.left :=
  D.smooth_projection

/-- Affineness of the original quotient scheme gives an affine group quotient. -/
theorem groupScheme_isAffineHom [IsAffine S] (hD : IsAffine D.scheme.left) :
    IsAffineHom (D.groupScheme hn).X.hom := by
  let : IsAffine D.scheme.left := hD
  change IsAffineHom D.scheme.hom
  infer_instance

end Base

section Field

variable {k : Type u} [Field k]
    {G Z A : GroupScheme (Spec (CommRingCat.of k))} {i : Z ⟶ G}
    (D : HomogeneousQuotient i)

/-- An affine normal homogeneous quotient supplies the actual equivariant
quotient and the dimension decrease needed in the central induction. -/
theorem exists_action_relativeDimension
    [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] [Mono i.hom.hom]
    (haff : IsAffine D.scheme.left) (hnormal : (SubgroupFunctor.range i).IsNormal)
    (hG : IsUnipotent G) (a : AutomorphicAction A G)
    (hstable : a.IsStable (SubgroupFunctor.range i))
    {d n : ℕ} (hd : SmoothOfRelativeDimension d G.X.hom)
    (hn : SmoothOfRelativeDimension n Z.X.hom) (hpos : 0 < n) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
      (b : AutomorphicAction A Q) (m : ℕ),
      IsAffineHom Q.X.hom ∧ Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
      IsUnipotent Q ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      Smooth q.hom.hom.left ∧ SmoothOfRelativeDimension n q.hom.hom.left ∧
      SmoothOfRelativeDimension m Q.X.hom ∧ d = n + m ∧ m < d ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ A.X) (g : T ⟶ G.X),
        b.act s (g ≫ q.hom.hom) = a.act s g ≫ q.hom.hom := by
  let Q := D.groupScheme hnormal
  let q := D.groupProjection hnormal
  let : IsAffineHom Q.X.hom := D.groupScheme_isAffineHom hnormal haff
  have hq := D.groupProjection_isFppfQuotient hnormal
  have hi : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  obtain ⟨b, m, hsm, hc, hu, hnq, hm, heq, hlt, hb⟩ :=
    hq.exists_action_relativeDimension_of_kernel hi hG a hstable hd hn hpos
  exact ⟨Q, q, b, m, inferInstance, hsm, hc, hu, hq,
    D.groupProjection_smooth hnormal, hnq, hm, heq, hlt, hb⟩

end Field

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient
