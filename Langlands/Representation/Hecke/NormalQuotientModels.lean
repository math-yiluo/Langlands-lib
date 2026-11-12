import Langlands.Representation.Jacquet.Coinvariants
import Langlands.ClassFieldTheory.Local.Galois
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Smooth.Transfer.StabilizerProof
import Langlands.Representation.Category.Basic
import Langlands.Representation.Hecke.NormalizedIndicator
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # The actual normal-quotient coinvariant functor

Renard III.2.10, printed pp.80–82 / PDF pp.86–88.
The action and induced maps are Mathlib's quotient-to-coinvariants constructions.
-/

noncomputable section

open CategoryTheory MeasureTheory Topology

namespace Langlands.Hecke.Homomorphism

universe uR uP v

variable {P : Type uP} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  (N : Subgroup P) [N.Normal]

/-- The image of an open subgroup under the actual open quotient projection. -/
def quotientOpenSubgroup (K : OpenSubgroup P) : OpenSubgroup (P ⧸ N) where
  toSubgroup := K.toSubgroup.map (QuotientGroup.mk' N)
  isOpen' := QuotientGroup.isOpenMap_coe _ K.isOpen

/-- Compactness of the same image subgroup. -/
theorem isCompact_quotientOpenSubgroup (K : OpenSubgroup P)
    (hK : IsCompact (K : Set P)) :
    IsCompact (quotientOpenSubgroup N K : Set (P ⧸ N)) :=
  hK.image QuotientGroup.continuous_mk

omit [IsTopologicalGroup P] in
/-- A normal quotient of a nonarchimedean group is nonarchimedean. -/
instance quotientNonarchimedean [NonarchimedeanGroup P] :
    NonarchimedeanGroup (P ⧸ N) :=
  Langlands.LocalClassField.quotientNonarchimedean N

variable {R : Type uR} [CommRing R]
  {V : Type v} [AddCommGroup V] [Module R V]

/-- The existing quotient-group action on the actual Jacquet coinvariant carrier. -/
abbrev normalQuotientAction (ρ : Representation R P V) :
    Representation R (P ⧸ N) (Jacquet.Coinvariants ρ N) :=
  ρ.quotientToCoinvariants N

omit [TopologicalSpace P] [IsTopologicalGroup P] in
@[simp] theorem normalQuotientAction_mk (ρ : Representation R P V) (p : P) (v : V) :
    normalQuotientAction N ρ (QuotientGroup.mk' N p) (Jacquet.mk ρ N v) =
      Jacquet.mk ρ N (ρ p v) := rfl

/-- Smoothness passes to the quotient action through the quotient topology. -/
theorem isSmooth_normalQuotientAction (ρ : Representation R P V) (hρ : IsSmooth ρ) :
    IsSmooth (normalQuotientAction N ρ) := by
  have hq := isSmooth_of_surjective (ρ.toCoinvariantsMkQ N)
    (Jacquet.mk_surjective ρ N) hρ
  intro v
  apply (isSmoothVector_iff_isOpen_stabilizer v).mpr
  apply (QuotientGroup.isQuotientMap_mk N).isOpen_preimage.mp
  exact (isSmoothVector_iff_isOpen_stabilizer v).mp (hq v)

/-- Renard's `j_N`, using the actual quotient carrier and Mathlib's induced maps. -/
def normalCoinvariantFunctor :
    SmoothRep.{uR, uP, v} R P ⥤ SmoothRep.{uR, uP, v} R (P ⧸ N) where
  obj A := SmoothRep.of (normalQuotientAction N A.representation)
    (isSmooth_normalQuotientAction N A.representation A.isSmooth)
  map f := SmoothRep.ofHom ((Rep.quotientToCoinvariantsFunctor R N).map f.hom).hom
  map_id A := by
    apply (smoothRepProperty R (P ⧸ N)).hom_ext
    exact (Rep.quotientToCoinvariantsFunctor R N).map_id A.obj
  map_comp f g := by
    apply (smoothRepProperty R (P ⧸ N)).hom_ext
    exact (Rep.quotientToCoinvariantsFunctor R N).map_comp f.hom g.hom

@[simp] theorem normalCoinvariantFunctor_map_mk
    {A B : SmoothRep.{uR, uP, v} R P} (f : A ⟶ B) (v : A) :
    SmoothRep.hom ((normalCoinvariantFunctor N).map f)
      (Jacquet.mk A.representation N v) = Jacquet.mk B.representation N (SmoothRep.hom f v) :=
  rfl

end Langlands.Hecke.Homomorphism
