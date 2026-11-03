import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-! # Pseudo-complete schemes over an arbitrary field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

namespace PseudoComplete

/-- The actual relative spectrum of a `k`-algebra, with its induced structure map. -/
abbrev algebraSpec (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] :
    Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))

@[simp]
theorem algebraSpec_hom (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] :
    (algebraSpec k A).hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) := rfl

variable {k : Type u} [Field k]

/-- The canonical generic-point map, over `Spec k`, induced by `R → FractionRing R`.
The fraction field has the `k`-algebra structure induced through `R`. -/
def genericPoint (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] :
    algebraSpec k (FractionRing R) ⟶ algebraSpec k R :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (FractionRing R))).op

@[simp]
theorem genericPoint_left (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] :
    (genericPoint (k := k) R).left =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := rfl

/-- The restricted valuative existence property, tested on every DVR in `Type u`.
Geometric reducedness of the induced residue extension means general separability;
the residue extension is not required to be algebraic. -/
def HasDVRLifting (X : Over (Spec (CommRingCat.of k))) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [IsDiscreteValuationRing R],
    Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField R) →
      ∀ x : algebraSpec k (FractionRing R) ⟶ X,
        ∃ xR : algebraSpec k R ⟶ X, genericPoint (k := k) R ≫ xR = x

end PseudoComplete

variable {k : Type u} [Field k]

/-- A separated finite-type `k`-scheme with the DVR lifting property for every
same-universe DVR whose residue extension over `k` is generally separable.
This is CGP, Definition C.1.1, with uniqueness supplied by separatedness. -/
structure IsPseudoComplete (X : Over (Spec (CommRingCat.of k))) : Prop where
  isSeparated : IsSeparated X.hom
  locallyOfFiniteType : LocallyOfFiniteType X.hom
  quasiCompact : QuasiCompact X.hom
  dvrLifting : PseudoComplete.HasDVRLifting X

variable {X : Over (Spec (CommRingCat.of k))}

/-- The separatedness, finite-type and valuative clauses of pseudo-completeness. -/
theorem isPseudoComplete_iff :
    IsPseudoComplete X ↔
      IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
        PseudoComplete.HasDVRLifting X :=
  ⟨fun h => ⟨h.isSeparated, h.locallyOfFiniteType, h.quasiCompact, h.dvrLifting⟩,
    fun ⟨hs, hf, hq, hv⟩ => ⟨hs, hf, hq, hv⟩⟩

/-- Finite type here is the conjunction of locally finite type and quasi-compactness. -/
theorem IsPseudoComplete.finiteType (h : IsPseudoComplete X) :
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom :=
  ⟨h.locallyOfFiniteType, h.quasiCompact⟩

/-- A fraction-field point extends with the actual relative restriction equation. -/
theorem IsPseudoComplete.exists_extension (h : IsPseudoComplete X)
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [IsDiscreteValuationRing R]
    (hsep : Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField R))
    (x : PseudoComplete.algebraSpec k (FractionRing R) ⟶ X) :
    ∃ xR : PseudoComplete.algebraSpec k R ⟶ X,
      PseudoComplete.genericPoint (k := k) R ≫ xR = x :=
  h.dvrLifting R hsep x

end Langlands.GroupScheme
