import Langlands.Representation.Exponents.SmoothRepNoetherianReduction
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal

/-! # A finite proper-parabolic supercuspidality test from structural inputs

`FiniteProperParabolicSupercuspidalTestStatement` is derived from three published
structural statements: parabolic subgroups are dynamic, maximal split tori are conjugate,
and the relative roots of a maximal split torus form a root system. None of the three is
proved here. Every proper actual parabolic is conjugate, on its radical's rational points,
to a proper standard face, and there are finitely many faces. One actual parabolic per
attained face is therefore enough.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RationalPointFamily

section Faces

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (std : ∀ D : ParabolicDatum G, ¬ IsIso D.p →
    ProperParabolicUnipotentStandardization i ν D.p D.r)

/-- The proper standard faces attained, under the standardization `std`, by proper
actual parabolic data of `G`. -/
def AttainedProperFace :=
  {I : Finset (SimpleRoot i ν) //
    ∃ (D : ParabolicDatum G) (hD : ¬ IsIso D.p), (std D hD).face = I}

instance : Finite (AttainedProperFace i ν std) := by
  unfold AttainedProperFace
  infer_instance

variable {i ν std}

/-- The face attained by one proper actual parabolic datum. -/
def AttainedProperFace.ofDatum (D : ParabolicDatum G) (hD : ¬ IsIso D.p) :
    AttainedProperFace i ν std :=
  ⟨(std D hD).face, D, hD, rfl⟩

/-- A chosen proper actual parabolic datum attaining the face. -/
def AttainedProperFace.datum (I : AttainedProperFace i ν std) : ParabolicDatum G :=
  Classical.choose (Subtype.property I)

theorem AttainedProperFace.datum_proper (I : AttainedProperFace i ν std) :
    ¬ IsIso I.datum.p :=
  (Classical.choose_spec (Subtype.property I)).choose

theorem AttainedProperFace.face_datum (I : AttainedProperFace i ν std) :
    (std I.datum I.datum_proper).face = Subtype.val I :=
  (Classical.choose_spec (Subtype.property I)).choose_spec

/-- Vanishing coinvariants along the chosen datum of a face give vanishing coinvariants
along every proper datum standardized to that face. -/
theorem AttainedProperFace.subsingleton_coinvariants {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (rationalPoints G) V)
    (I : AttainedProperFace i ν std) (D : ParabolicDatum G) (hD : ¬ IsIso D.p)
    (hI : Subtype.val I = (std D hD).face)
    (h : Subsingleton (Jacquet.Localization.Coinvariants ρ
      (pointImage (I.datum.r ≫ I.datum.p)) 1)) :
    Subsingleton (Jacquet.Localization.Coinvariants ρ (pointImage (D.r ≫ D.p)) 1) := by
  have hstd : Subsingleton (Jacquet.Localization.Coinvariants ρ
      (unipotent i ν (std D hD).face) 1) := by
    rw [← hI, ← I.face_datum]
    let s := std I.datum I.datum_proper
    exact (coinvariantsTranslateEquiv s.conjugatingPoint s.radicalPoints
      ρ).symm.injective.subsingleton
  exact (coinvariantsTranslateEquiv (std D hD).conjugatingPoint
    (std D hD).radicalPoints ρ).injective.subsingleton

end Faces

/-- Parabolic recognition, conjugacy of maximal split tori and the relative root system
imply that supercuspidality is tested on finitely many proper actual parabolics. -/
theorem finiteProperParabolicSupercuspidalTest_of_structure
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u}) :
    FiniteProperParabolicSupercuspidalTestStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let _ : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot k G hG T i hi
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let std : ∀ D : ParabolicDatum G, ¬ IsIso D.p →
      ProperParabolicUnipotentStandardization i ν D.p D.r := fun D hD =>
    properParabolicUnipotentStandardization i ν hPD hconj hG hi hν hRoots
      D.p D.l D.r D.hp D.hl D.hr hD
  let e := Finite.equivFin (AttainedProperFace i ν std)
  refine ⟨Nat.card (AttainedProperFace i ν std), fun j => (e.symm j).datum,
    fun j => (e.symm j).datum_proper, ?_⟩
  intro A hA P M U p l r hp hl hr hmul hproper
  let Q : ParabolicDatum G := ⟨P, M, U, p, l, r, hp, hl, hr, hmul⟩
  let I := AttainedProperFace.ofDatum (std := std) Q hproper
  have hI : Subtype.val (e.symm (e I)) = (std Q hproper).face := by
    rw [Equiv.symm_apply_apply]
    rfl
  exact AttainedProperFace.subsingleton_coinvariants A.representation (e.symm (e I))
    Q hproper hI (hA (e I))

end Langlands.Aubert.General.RepresentedParabolic
