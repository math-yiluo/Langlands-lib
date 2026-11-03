import Langlands.GroupScheme.Descent.AffineDatumMorphisms
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.CentralIsogeny.Transport

/-! # Central isogenies in actual affine group-scheme descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent

namespace Solution

variable {B S : Scheme.{u}} {p : S ⟶ B}
    [Flat p] [Surjective p] [QuasiCompact p]
    {G H : GroupScheme S} {D : Datum p G} {E : Datum p H}

/-- Descending a compatible homomorphism preserves and reflects the full
central-isogeny predicate. -/
theorem descendHom_isCentralIsogeny_iff (s : Solution D) (t : Solution E)
    (f : G ⟶ H) (hf : Compatible D E f) :
    IsCentralIsogeny (descendHom s t f hf) ↔ IsCentralIsogeny f := by
  constructor
  · intro ha
    have h := (ha.baseChange p).comp_iso t.iso
    rw [baseChange_descendHom] at h
    exact (isCentralIsogeny_iso_comp_iff f s.iso).mp h
  · intro h
    apply centralIsogenyFpqcReflection B S p s.obj t.obj
    apply (isCentralIsogeny_comp_iso_iff _ t.iso).mp
    rw [baseChange_descendHom]
    exact h.iso_comp s.iso

/-- An arrow descended to its original target is a central isogeny precisely
when the supplied compatible arrow is. -/
theorem descendTo_isCentralIsogeny_iff (s : Solution D) (C : GroupScheme B)
    (f : G ⟶ (baseChange p).obj C)
    (hf : Compatible D (canonicalDatum p C) f) :
    IsCentralIsogeny (s.descendTo C f hf) ↔ IsCentralIsogeny f :=
  descendHom_isCentralIsogeny_iff s (canonicalSolution p C) f hf

end Solution

namespace Datum

variable {B S : Scheme.{u}} {p : S ⟶ B}
    [IsAffine B] [IsAffine S] [Flat p] [Surjective p]
    {G H : GroupScheme S} [IsAffine G.X.left]
    (D : Datum p G)

/-- Central isogenies between affine data give central isogenies between the
constructed affine solutions, in both directions. -/
theorem affineHom_isCentralIsogeny_iff [IsAffine H.X.left] (E : Datum p H)
    (f : G ⟶ H) (hf : Compatible D E f) :
    IsCentralIsogeny (D.affineHom E f hf) ↔ IsCentralIsogeny f :=
  Solution.descendHom_isCentralIsogeny_iff D.affineSolution E.affineSolution f hf

variable (C : GroupScheme B) (f : G ⟶ (baseChange p).obj C)
    (hf : Compatible D (canonicalDatum p C) f)

/-- The actual arrow from the constructed affine solution to the original
target preserves and reflects central isogenies. -/
theorem affineHomTo_isCentralIsogeny_iff :
    IsCentralIsogeny (D.affineHomTo C f hf) ↔ IsCentralIsogeny f :=
  Solution.descendTo_isCentralIsogeny_iff D.affineSolution C f hf

/-- Construct an actual central isogeny to the original target from compatible
affine datum and an actual central isogeny after the change of base. -/
def affineCentralIsogenyTo (hcentral : IsCentralIsogeny f) :
    {a : D.affineSolution.obj ⟶ C // IsCentralIsogeny a} :=
  ⟨D.affineHomTo C f hf, (D.affineHomTo_isCentralIsogeny_iff C f hf).mpr hcentral⟩

/-- The constructed central isogeny's underlying arrow has the exact original
pullback recovery equation. -/
theorem baseChange_affineCentralIsogenyTo (hcentral : IsCentralIsogeny f) :
    (baseChange p).map (D.affineCentralIsogenyTo C f hf hcentral).val =
      D.affineSolution.iso.hom ≫ f :=
  D.baseChange_affineHomTo C f hf

include hf in
/-- The pullback equation determines exactly one actual central isogeny from
the constructed affine solution to the original target. -/
theorem existsUnique_affineCentralIsogenyTo (hcentral : IsCentralIsogeny f) :
    ∃! a : D.affineSolution.obj ⟶ C,
      IsCentralIsogeny a ∧ (baseChange p).map a = D.affineSolution.iso.hom ≫ f := by
  obtain ⟨a, ha, huniq⟩ := D.existsUnique_affineHomTo C f hf
  have heq : a = D.affineHomTo C f hf :=
    huniq _ (D.baseChange_affineHomTo C f hf)
      |>.symm
  refine ⟨a, ⟨?_, ha⟩, ?_⟩
  · rw [heq]
    exact (D.affineHomTo_isCentralIsogeny_iff C f hf).mpr hcentral
  · intro b hb
    exact huniq b hb.2

end Datum

end Langlands.GroupScheme.Descent
