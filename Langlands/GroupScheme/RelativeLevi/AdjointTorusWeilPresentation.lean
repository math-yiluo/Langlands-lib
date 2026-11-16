import Langlands.GroupScheme.RelativeLevi.AdjointBorelExtension
import Langlands.GroupScheme.RelativeLevi.AdjointTorusWeilPresentationStatement

/-! # Applying an induced-torus presentation to the actual adjoint torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi.AdjointBorelExtensionData

section GeneralBase

variable {S : Scheme.{u}} {G B A : GroupScheme S}
    {i : B ⟶ G} {q : G ⟶ A} {a : AutomorphicAction A G}
    {T : CommGroupScheme S} {t : T.toGrp ⟶ B}
    (d : AdjointBorelExtensionData i q a T t)

/-- The actual torus projection has the full ambient-center inverse image
as its kernel, with all three fppf properties retained. -/
theorem torus_center_isFppfQuotient
    (hq : RelativeRoot.IsFppfQuotient (center G) q) :
    RelativeRoot.IsFppfQuotient
      ((center G).comap (t ≫ i)) d.torus.projection := by
  refine ⟨d.torus.flat, d.torus.surjective,
    d.torus.locallyOfFinitePresentation, ?_⟩
  rw [d.torus.kernel_eq, d.borel.kernel_eq, hq.2.2.2,
    ← SubgroupFunctor.comap_comp]

end GeneralBase

section OverRing

variable {R : Type u} [CommRing R]
    {G B A : GroupScheme (Spec (CommRingCat.of R))}
    {i : B ⟶ G} {q : G ⟶ A} {a : AutomorphicAction A G}
    {T : CommGroupScheme (Spec (CommRingCat.of R))} {t : T.toGrp ⟶ B}
    (d : AdjointBorelExtensionData i q a T t)

/-- A proof of the universal presentation statement supplies the presentation
of this actual torus quotient, without an affine ambient-quotient premise. -/
theorem torus_weilPresentation_of_statement
    (hWeil : RelativeBorelAdjointTorusWeilPresentationStatement.{u})
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E)
      (_ : Module.Finite R E) (_ : Module.Projective R E),
      Algebra.Etale R E ∧
        Nonempty (d.torus.group ≅ WeilGm.groupScheme (CommRingCat.of R) E) :=
  hWeil R G B i hG hi T t hT htG hmax d.torus.group
    d.torus.projection (d.torus_center_isFppfQuotient hq)

/-- A chosen finite étale coefficient algebra and presentation of the actual
torus quotient in the supplied extension data. -/
structure TorusWeilPresentationData where
  algebra : Type u
  [commRing : CommRing algebra]
  [algebraStructure : Algebra R algebra]
  [finite : Module.Finite R algebra]
  [projective : Module.Projective R algebra]
  etale : Algebra.Etale R algebra
  iso : d.torus.group ≅ WeilGm.groupScheme (CommRingCat.of R) algebra

attribute [instance] TorusWeilPresentationData.commRing
  TorusWeilPresentationData.algebraStructure TorusWeilPresentationData.finite
  TorusWeilPresentationData.projective

/-- Choose presentation data for the actual torus from the explicitly
supplied universal presentation theorem. -/
noncomputable def torusWeilPresentation
    (hWeil : RelativeBorelAdjointTorusWeilPresentationStatement.{u})
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i)) :
    TorusWeilPresentationData d :=
  Classical.choice (by
    obtain ⟨E, hE, hRE, hFin, hProj, hEt, hIso⟩ :=
      d.torus_weilPresentation_of_statement hWeil hG hi hq hT htG hmax
    exact ⟨{
      algebra := E
      commRing := hE
      algebraStructure := hRE
      finite := hFin
      projective := hProj
      etale := hEt
      iso := Classical.choice hIso }⟩)

end OverRing

end Langlands.GroupScheme.RelativeLevi.AdjointBorelExtensionData
