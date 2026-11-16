import Langlands.GroupScheme.Reductive.AffinePinnedAtlasCocharacter
import Langlands.GroupScheme.Descent.EtaleHomDescent

/-! # Descending an invariant atlas cocharacter through an actual solution -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent

open Langlands.GroupScheme.Dynamic

variable {S U : Scheme.{u}} {p : U ⟶ S} {G : GroupScheme U} {D : Datum p G}

/-- The canonical multiplicative-group overlap respects its normalized identifications. -/
theorem gmBaseChange_overlap :
    (baseChange (fst p)).map (Gm.baseChangeIso p).hom ≫
        (Gm.baseChangeIso (fst p)).hom =
      (canonicalOverlap p (Gm S).toGrp).hom ≫
        (baseChange (snd p)).map (Gm.baseChangeIso p).hom ≫
        (Gm.baseChangeIso (snd p)).hom := by
  rw [gmBaseChange_tower p (fst p) (fst p ≫ p) rfl,
    gmBaseChange_tower p (snd p) (fst p ≫ p) pullback.condition.symm]
  simp [canonicalOverlap, Category.assoc]

/-- Invariance of a normalized cocharacter is compatibility of its relative Hom map. -/
theorem compatible_of_cocharacter_invariant (χ : (Gm U).toGrp ⟶ G)
    (hχ : baseChangeCocharacter (fst p) χ ≫ D.overlap.hom =
      baseChangeCocharacter (snd p) χ) :
    Compatible (canonicalDatum p (Gm S).toGrp) D
      ((Gm.baseChangeIso p).hom ≫ χ) := by
  have h := congrArg (fun a =>
    ((baseChange (fst p)).map (Gm.baseChangeIso p).hom ≫
      (Gm.baseChangeIso (fst p)).hom) ≫ a) hχ
  simp only [baseChangeCocharacter, Category.assoc, Iso.hom_inv_id_assoc] at h
  change (baseChange (fst p)).map ((Gm.baseChangeIso p).hom ≫ χ) ≫ D.overlap.hom =
    (canonicalOverlap p (Gm S).toGrp).hom ≫
      (baseChange (snd p)).map ((Gm.baseChangeIso p).hom ≫ χ)
  simp only [Functor.map_comp, Category.assoc]
  rw [h]
  have hg := gmBaseChange_overlap (p := p)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun a => a ≫ (Gm.baseChangeIso (snd p)).inv ≫
      (baseChange (snd p)).map χ) hg

namespace Solution

variable [Etale p] [Surjective p] (s : Solution D)
    (χ : (Gm U).toGrp ⟶ G)
    (hχ : baseChangeCocharacter (fst p) χ ≫ D.overlap.hom =
      baseChangeCocharacter (snd p) χ)

/-- Descend a normalized invariant cocharacter through any supplied actual solution. -/
def cocharacterOfEtale : (Gm S).toGrp ⟶ s.obj :=
  (canonicalSolution p (Gm S).toGrp).descendHomOfEtale s
    ((Gm.baseChangeIso p).hom ≫ χ) (compatible_of_cocharacter_invariant χ hχ)

/-- The descended cocharacter recovers the prescribed normalized cocharacter exactly. -/
theorem cocharacterOfEtale_recovers :
    baseChangeCocharacter p (s.cocharacterOfEtale χ hχ) ≫ s.iso.hom = χ := by
  have h := (canonicalSolution p (Gm S).toGrp).baseChange_descendHomOfEtale s
    ((Gm.baseChangeIso p).hom ≫ χ) (compatible_of_cocharacter_invariant χ hχ)
  have h' := congrArg (fun a => (Gm.baseChangeIso p).inv ≫ a) h
  simpa only [cocharacterOfEtale, baseChangeCocharacter, Category.assoc,
    canonicalSolution, Iso.refl_hom, Category.id_comp, Iso.inv_hom_id_assoc] using h'

/-- Exact normalized recovery determines the descended cocharacter. -/
theorem cocharacterOfEtale_unique (ν : (Gm S).toGrp ⟶ s.obj)
    (hν : baseChangeCocharacter p ν ≫ s.iso.hom = χ) :
    ν = s.cocharacterOfEtale χ hχ := by
  apply (canonicalSolution p (Gm S).toGrp).descendHomOfEtale_unique s
    ((Gm.baseChangeIso p).hom ≫ χ) (compatible_of_cocharacter_invariant χ hχ)
  have h := congrArg (fun a => (Gm.baseChangeIso p).hom ≫ a) hν
  simpa only [baseChangeCocharacter, Category.assoc, Iso.hom_inv_id_assoc,
    canonicalSolution, Iso.refl_hom, Category.id_comp] using h

end Solution
end Descent

namespace AffinePinnedAtlas

variable {S : Scheme.{u}} {G : GroupScheme S} (A : AffinePinnedAtlas G)
    (P : RelativePinnedComparison.{u}) (s : Descent.Solution (A.datum P))

/-- The canonical atlas cocharacter on any actual solution of the corrected datum. -/
def descendedCocharacter : (Gm S).toGrp ⟶ s.obj :=
  s.cocharacterOfEtale A.cocharacter (A.overlap_cocharacter P)

/-- Its pullback, expressed through the solution comparison, is the atlas cocharacter. -/
theorem descendedCocharacter_recovers :
    Dynamic.baseChangeCocharacter A.projection (A.descendedCocharacter P s) ≫
      s.iso.hom = A.cocharacter :=
  s.cocharacterOfEtale_recovers A.cocharacter (A.overlap_cocharacter P)

end AffinePinnedAtlas
end Langlands.GroupScheme
