import Langlands.Representation.CuspidalSupport.RationalCuspidalCategory

/-!
# Off-diagonal morphisms for the whole cuspidal factors

This is the independent Hom-vanishing part of Renard VI.3.5. The actual image
of a nonzero morphism is a nonzero subquotient of both its source and target.
The all/no conditions therefore contradict one another on that image.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The full factors in which all actual subquotients satisfy `P`, or no
nonzero actual subquotient satisfies `P`. The `true` factor is the former.
Unlike irreducible-subquotient factors, these test arbitrary subquotients. -/
def subquotientProperties
    (P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)) :
    Bool → ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)
  | false => fun A => ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      Nontrivial D → IsSubquotient D A → ¬ P D
  | true => fun A => ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      IsSubquotient D A → P D

/-- The actual image of a nonzero map contradicts the all/no subquotient
conditions, with no irreducibility or chain-condition hypothesis. -/
theorem subquotientProperties_offDiagonalHomsZero
    (P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)) :
    Renard.OffDiagonalHomsZero (subquotientProperties P) := by
  intro b c hbc A B hA hB f
  by_contra hf
  have hv : ∃ v : A, SmoothRep.hom f v ≠ 0 := by
    by_contra hn
    apply hf
    ext v
    exact Classical.not_not.mp (not_exists.mp hn v)
  obtain ⟨v, hv⟩ := hv
  let D := SmoothRep.image f
  have hD : Nontrivial D :=
    ⟨⟨⟨SmoothRep.hom f v, ⟨v, rfl⟩⟩, 0,
      fun heq => hv (congrArg Subtype.val heq)⟩⟩
  let q : A ⟶ D := SmoothRep.ofHom {
    toLinearMap := (SmoothRep.hom f).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext w
      exact Subtype.ext
        (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g w) }
  have hDA : SmoothRep.IsSubquotient D A :=
    SmoothRep.isSubquotient_iff_exists.mpr
      ⟨A, 𝟙 A, q, Function.injective_id, LinearMap.surjective_rangeRestrict _⟩
  have hDB : SmoothRep.IsSubquotient D B :=
    (SmoothRep.subrepresentation_isSubrepresentation (SmoothRep.hom f).range).isSubquotient
  cases b <;> cases c
  · exact hbc rfl
  · exact hA D hD hDA (hB D hDB)
  · exact hB D hD hDB (hA D hDA)
  · exact hbc rfl

end Langlands.SmoothRep

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (GroupScheme.rationalPoints G)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (h : ∀ I, IsSemidirectDecomposition
    (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G)))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Every morphism between distinct actual whole cuspidal factors vanishes.
The proof tests the arbitrary actual image, without choosing an irreducible
constituent or assuming finite length. -/
theorem rationalWholeCuspidalDecompositionProperties_offDiagonalHomsZero :
    Renard.OffDiagonalHomsZero
      (rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU) := by
  have hprops : rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU =
      SmoothRep.subquotientProperties
        (fun D => IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU D) := by
    funext b
    cases b <;> rfl
  rw [hprops]
  exact SmoothRep.subquotientProperties_offDiagonalHomsZero _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The first whole-category assertion of VI.3.5 is equivalent to its actual
coproduct assertion: off-diagonal vanishing needs no splitting hypothesis. -/
theorem isRationalWholeCuspidalCategoryDecomposition_iff_coproduct :
    IsRationalWholeCuspidalCategoryDecomposition.{uF, uV} G i ν h hU ↔
      Renard.EveryObjectIsCoproductOfComponents
        (rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU) :=
  ⟨And.left, fun hc =>
    ⟨hc, rationalWholeCuspidalDecompositionProperties_offDiagonalHomsZero G i ν h hU⟩⟩

end Langlands.CuspidalSupport
