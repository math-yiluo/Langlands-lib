import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Jacquet.LocalizationTransport

/-! # Normalized coinvariants of representations of a represented parabolic -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance coinvariantsAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

/-- The actual radical point image, viewed as a subgroup of the parabolic image. -/
abbrev parabolicRadicalPoints : Subgroup (pointImage p) :=
  (pointImage (r ≫ p)).subgroupOf (pointImage p)

/-- The Levi's actual point map into the literal parabolic image. -/
def leviToParabolicPoints : rationalPoints M →* pointImage p where
  toFun m := ⟨rationalPoints.map (l ≫ p) m, pointImage_comp_le p l ⟨m, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)

/-- The ambient inverse half Haar character pulled back to the actual Levi points. -/
def leviInverseHalfCharacter :
    letI := leviPointTopology l hl
    Induction.SmoothCharacter ℂ (rationalPoints M) := by
  letI := leviPointTopology l hl
  let hc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let hn := pointImage_le_normalizer p l r hr
  let e := leviPointsEquiv p l hp hl
  exact {
    toMonoidHom := (HaarModulus.closedInverseHalfCharacter
      (pointImage (r ≫ p)) hc (pointImage (l ≫ p)) hn).comp e.toMonoidHom
    isOpen_ker := (HaarModulus.isOpen_ker_closedInverseHalfCharacter
      (pointImage (r ≫ p)) hc (pointImage (l ≫ p)) hn).preimage e.continuous }

/-- Normalized radical coinvariants on the full representation category of the
parabolic itself, with output on the Levi's own rational points. -/
def leviParabolicCoinvariantsFunctor :
    letI := leviPointTopology l hl
    Rep.{v} ℂ (pointImage p) ⥤ Rep.{v} ℂ (rationalPoints M) := by
  letI := leviPointTopology l hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  letI : (parabolicRadicalPoints p r).Normal := h.normal
  let hn : (⊤ : Subgroup (pointImage p)) ≤
      Subgroup.normalizer (parabolicRadicalPoints p r) := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  let j : rationalPoints M →* (⊤ : Subgroup (pointImage p)) :=
    (Subgroup.topEquiv).symm.toMonoidHom.comp (leviToParabolicPoints p l)
  exact Jacquet.Localization.functor (parabolicRadicalPoints p r) 1 ⊤ hn
      (Jacquet.Localization.isInvariant_one _ _ hn) ⋙
    Rep.resFunctor j ⋙ (leviInverseHalfCharacter p l r hp hr hl).twistFunctor

@[simp]
theorem leviParabolicCoinvariantsFunctor_map_mk
    {A B : Rep.{v} ℂ (pointImage p)} (f : A ⟶ B) (x : A) :
    letI := leviPointTopology l hl
    ((leviParabolicCoinvariantsFunctor p l r hp hr hl hmul).map f).hom
      (Jacquet.Localization.mk A.ρ (parabolicRadicalPoints p r) 1 x) =
        Jacquet.Localization.mk B.ρ (parabolicRadicalPoints p r) 1 (f.hom x) := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Restricting the ambient representation to its parabolic leaves the actual
radical quotient unchanged, naturally and with the same normalizing character. -/
def leviParabolicCoinvariantsRestrictionIso :
    letI := leviPointTopology l hl
    SmoothRep.toRep ⋙ Rep.resFunctor (pointImage p).subtype ⋙
        leviParabolicCoinvariantsFunctor.{u, v} p l r hp hr hl hmul ≅
      leviJacquetFunctor p l r hp hr hl hmul ⋙ SmoothRep.toRep := by
  letI := leviPointTopology l hl
  let eN := subgroupOfContinuousEquiv (pointImage_comp_le p r)
  let e := fun A : SmoothRep.{0, u, v} ℂ (rationalPoints G) =>
    Jacquet.Localization.transportEquiv
      (A.representation.comp (pointImage p).subtype) A.representation
      (parabolicRadicalPoints p r) (pointImage (r ≫ p)) 1 1 eN.toMulEquiv
      (LinearEquiv.refl ℂ A) (fun _ _ => rfl) (fun _ => rfl)
  refine NatIso.ofComponents (fun A => Rep.mkIso {
    toLinearEquiv := e A
    isIntertwining' := ?_ }) ?_
  · intro m
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective
      (A.representation.comp (pointImage p).subtype) (parabolicRadicalPoints p r) 1 x
    change e A ((((leviInverseHalfCharacter p l r hp hr hl).toMonoidHom m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk _ _ 1
          (A.representation (rationalPoints.map (l ≫ p) m) y)) =
      (((leviInverseHalfCharacter p l r hp hr hl).toMonoidHom m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk _ _ 1
          (A.representation (rationalPoints.map (l ≫ p) m) y)
    rw [map_smul]
    rfl
  · intro A B f
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective
      (A.representation.comp (pointImage p).subtype) (parabolicRadicalPoints p r) 1 x
    change e B (Jacquet.Localization.mk
      (B.representation.comp (pointImage p).subtype) (parabolicRadicalPoints p r) 1
        (SmoothRep.hom f y)) =
      Jacquet.Localization.mk B.representation (pointImage (r ≫ p)) 1 (SmoothRep.hom f y)
    rfl

@[simp]
theorem leviParabolicCoinvariantsRestrictionIso_hom_mk
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (x : A) :
    letI := leviPointTopology l hl
    ((leviParabolicCoinvariantsRestrictionIso p l r hp hr hl hmul).hom.app A).hom
      (Jacquet.Localization.mk (A.representation.comp (pointImage p).subtype)
        (parabolicRadicalPoints p r) 1 x) =
      Jacquet.Localization.mk A.representation (pointImage (r ≫ p)) 1 x := rfl

end Langlands.Aubert.General.RepresentedParabolic
