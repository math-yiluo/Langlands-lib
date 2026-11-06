import Langlands.Representation.Geometric.RepresentedParabolicCoinvariants
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Filtration.ExactSmoothTransport
import Langlands.Representation.Category.RestrictionSubquotients

/-! # Exactness and image quotients for represented-parabolic coinvariants -/

noncomputable section

universe u v uC vC

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance coinvariantsExactAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
include hp in
/-- Continuity of the actual Levi section with codomain restricted to the parabolic. -/
theorem continuous_leviToParabolicPoints :
    letI := leviPointTopology l hl
    Continuous (leviToParabolicPoints p l) := by
  let := leviPointTopology l hl
  exact (leviPointsEquiv p l hp hl).continuous.subtype_val.subtype_mk _

/-- Smooth input representations of the parabolic have smooth normalized coinvariants. -/
theorem isSmooth_leviParabolicCoinvariantsFunctor_obj
    (A : SmoothRep.{0, u, v} ℂ (pointImage p)) :
    letI := leviPointTopology l hl
    IsSmooth ((leviParabolicCoinvariantsFunctor p l r hp hr hl hmul).obj A.obj).ρ := by
  let := leviPointTopology l hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let : (parabolicRadicalPoints p r).Normal := h.normal
  let hn : (⊤ : Subgroup (pointImage p)) ≤
      Subgroup.normalizer (parabolicRadicalPoints p r) := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  let j : rationalPoints M →* (⊤ : Subgroup (pointImage p)) :=
    (Subgroup.topEquiv).symm.toMonoidHom.comp (leviToParabolicPoints p l)
  have hj : Continuous j :=
    (continuous_leviToParabolicPoints p l hp hl).subtype_mk _
  exact (isSmooth_twist_iff (leviInverseHalfCharacter p l r hp hr hl).toMonoidHom _
    (leviInverseHalfCharacter p l r hp hr hl).isOpen_ker).mpr
      (isSmooth_comp j hj
        (Jacquet.Localization.isSmooth_action A.representation
          (parabolicRadicalPoints p r) 1 ⊤ hn
          (Jacquet.Localization.isInvariant_one _ _ hn) A.isSmooth))

/-- The same actual normalized coinvariants, with their proved smoothness bundled. -/
def smoothLeviParabolicCoinvariantsFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (pointImage p) ⥤ SmoothRep.{0, u, v} ℂ (rationalPoints M) := by
  letI := leviPointTopology l hl
  let J := leviParabolicCoinvariantsFunctor.{u, v} p l r hp hr hl hmul
  exact {
    obj A := SmoothRep.of (J.obj A.obj).ρ
      (isSmooth_leviParabolicCoinvariantsFunctor_obj p l r hp hr hl hmul A)
    map f := ObjectProperty.homMk (J.map f.hom)
    map_id A := by
      apply ObjectProperty.hom_ext
      exact J.map_id A.obj
    map_comp f g := by
      apply ObjectProperty.hom_ext
      exact J.map_comp f.hom g.hom }

@[simp]
theorem smoothLeviParabolicCoinvariantsFunctor_toRep :
    letI := leviPointTopology l hl
    smoothLeviParabolicCoinvariantsFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep =
      SmoothRep.toRep ⋙ leviParabolicCoinvariantsFunctor p l r hp hr hl hmul := rfl

instance smoothLeviParabolicCoinvariantsFunctor_preservesZeroMorphisms :
    letI := leviPointTopology l hl
    (smoothLeviParabolicCoinvariantsFunctor.{u, v} p l r hp hr hl hmul).PreservesZeroMorphisms := by
  let := leviPointTopology l hl
  refine ⟨fun A B => ?_⟩
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective
    A.representation (parabolicRadicalPoints p r) 1 x
  change Jacquet.Localization.mk B.representation (parabolicRadicalPoints p r) 1 0 = 0
  exact map_zero _

/-- Compact containment of the actual nested radical gives exactness on the full
smooth parabolic category. No existence of compact containment is asserted here. -/
theorem smoothLeviParabolicCoinvariantsFunctor_exact
    (hN : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints p r)) :
    letI := leviPointTopology l hl
    Derivative.Mirabolic.MapsShortExactIntertwiners
      (smoothLeviParabolicCoinvariantsFunctor.{u, v} p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let : (parabolicRadicalPoints p r).Normal := h.normal
  let hn : (⊤ : Subgroup (pointImage p)) ≤
      Subgroup.normalizer (parabolicRadicalPoints p r) := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  intro A B C f g hf hg hex
  exact ⟨Jacquet.Localization.map_injective_of_smooth
    (parabolicRadicalPoints p r) hN 1 (IsLocallyConstant.const 1) ⊤ hn
    (Jacquet.Localization.isInvariant_one _ _ hn) (SmoothRep.hom f) hf B.isSmooth,
    Jacquet.Localization.map_range_eq_ker (parabolicRadicalPoints p r) 1 ⊤ hn
      (Jacquet.Localization.isInvariant_one _ _ hn) (SmoothRep.hom f) (SmoothRep.hom g) hg hex,
    Jacquet.Localization.map_surjective (parabolicRadicalPoints p r) 1 ⊤ hn
      (Jacquet.Localization.isInvariant_one _ _ hn) (SmoothRep.hom g) hg⟩

variable {C : Type uC} [Category.{vC} C]
  {F : C ⥤ SmoothRep.{0, u, v} ℂ (pointImage p)}

/-- The actual quotient of two nested coinvariant images is naturally the
normalized coinvariants of the actual support quotient. -/
def leviParabolicCoinvariantsImageQuotientIso
    (hN : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints p r))
    (S T : RepSubfunctor (F ⋙ SmoothRep.toRep)) (hST : ∀ X, S.obj X ≤ T.obj X) :
    letI := leviPointTopology l hl
    (S.exactImage (smoothLeviParabolicCoinvariantsFunctor p l r hp hr hl hmul)).quotientFunctor
        (T.exactImage (smoothLeviParabolicCoinvariantsFunctor p l r hp hr hl hmul)) ≅
      S.quotientFunctor T ⋙ leviParabolicCoinvariantsFunctor p l r hp hr hl hmul := by
  letI := leviPointTopology l hl
  exact S.exactImageQuotientIso T (smoothLeviParabolicCoinvariantsFunctor p l r hp hr hl hmul)
    (smoothLeviParabolicCoinvariantsFunctor_exact p l r hp hr hl hmul hN) hST

end Langlands.Aubert.General.RepresentedParabolic
