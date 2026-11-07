import Langlands.GroupScheme.SplitExistence.RootDatumOf
import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Torus.RelativeAdjointWeightBaseChange

/-! # Full coordinate root data on every field-valued fibre -/

noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

variable {I : Type u} [Fintype I] {J : Type v}
  (k : Type u) [Field k] (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Realize both full coordinate lattices as the actual character and
cocharacter lattices of the coordinate split torus over a supplied field. -/
def fieldRealization :
    RootDatum J
      (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))
      (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) :=
  P.map (Equiv.refl J) (splitTorus.characterLatticeEquiv k I).symm.toIntLinearEquiv
    (splitTorus.cocharacterLatticeEquiv k I).symm.toIntLinearEquiv

/-- The realization retains both entire lattices, with the usual
contravariant coweight convention for root-pairing equivalences. -/
def fieldRealizationEquiv : RootPairing.Equiv P (fieldRealization k P) :=
  SplitExistence.rootPairingMapEquiv P
    (splitTorus.characterLatticeEquiv k I).symm.toIntLinearEquiv
    (splitTorus.cocharacterLatticeEquiv k I).symm.toIntLinearEquiv

@[simp] theorem fieldRealization_root (α : J) :
    (fieldRealization k P).root α =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α) :=
  (splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k (P.root α)).symm

@[simp] theorem fieldRealization_coroot (α : J) :
    (fieldRealization k P).coroot α =
      splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (P.coroot α) :=
  (splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm I k (P.coroot α)).symm

@[simp] theorem fieldRealization_pairing (m n : I → ℤ) :
    (fieldRealization k P).toLinearMap
        (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) =
      P.toLinearMap m n := by
  rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
    splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
  change P.toLinearMap
    ((splitTorus.characterLatticeEquiv k I) ((splitTorus.characterLatticeEquiv k I).symm m))
    ((splitTorus.cocharacterLatticeEquiv k I)
      ((splitTorus.cocharacterLatticeEquiv k I).symm n)) = _
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

@[simp] theorem fieldRealizationEquiv_weightMap (m : I → ℤ) :
    (fieldRealizationEquiv k P).weightMap m =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m :=
  (splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k m).symm

@[simp] theorem fieldRealizationEquiv_coweightMap
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) :
    (fieldRealizationEquiv k P).coweightMap ν =
      splitTorus.cocharacterLatticeEquiv k I ν := rfl

/-- An equivalence of the realized full data gives an equivalence of the
original coordinate data, including the central lattice directions. -/
def equivOfFieldRealizationEquiv
    {I' : Type u} [Fintype I'] {J' : Type w}
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (e : RootPairing.Equiv (fieldRealization k P) (fieldRealization k Q)) :
    RootPairing.Equiv P Q :=
  (fieldRealizationEquiv k Q).symm.comp (e.comp (fieldRealizationEquiv k P))

end CoordinateRootDatum

section Fibrewise

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))

local instance fibrewiseRootDatumAffine {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

/-- A finite reduced full coordinate root datum is associated to the actual
torus map when its realization is an actual root datum on every supplied
field-valued fibre, using that field's original algebra structure. -/
def IsFibrewiseRootDatumOf : Prop :=
  Finite J ∧ P.IsReduced ∧
    ∀ (k : Type u) [Field k] [Algebra R k],
      IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
        (CoordinateRootDatum.fieldRealization k P)

variable {I G i P}

theorem IsFibrewiseRootDatumOf.finite (hP : IsFibrewiseRootDatumOf I G i P) :
    Finite J := hP.1

theorem IsFibrewiseRootDatumOf.isReduced (hP : IsFibrewiseRootDatumOf I G i P) :
    P.IsReduced := hP.2.1

/-- Specialize to the actual fibre defined by any supplied field algebra. -/
theorem IsFibrewiseRootDatumOf.field (hP : IsFibrewiseRootDatumOf I G i P)
    (k : Type u) [Field k] [Algebra R k] :
    IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (CoordinateRootDatum.fieldRealization k P) :=
  hP.2.2 k

/-- The coordinate pairing is forced to be the standard integer dot
product as soon as a field-valued fibre is supplied. -/
theorem IsFibrewiseRootDatumOf.pairing (hP : IsFibrewiseRootDatumOf I G i P)
    (k : Type u) [Field k] [Algebra R k] (m n : I → ℤ) :
    P.toLinearMap m n = ∑ j, m j * n j := by
  rw [← CoordinateRootDatum.fieldRealization_pairing k P m n, (hP.field k).1]
  exact splitTorus.latticePairing_exponentCharacter_exponentCocharacter I k m n

/-- The actual roots on each supplied field fibre are exactly the
fixed-exponent characters of the roots of the common full datum. -/
theorem IsFibrewiseRootDatumOf.mem_roots_iff
    (hP : IsFibrewiseRootDatumOf I G i P)
    (k : Type u) [Field k] [Algebra R k] (m : I → ℤ) :
    splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (splitTorus.baseChangeHom (K := k) G I i) ↔
      m ∈ Set.range P.root := by
  rw [← (hP.field k).2.1]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, ?_⟩
    rw [CoordinateRootDatum.fieldRealization_root,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm] at hα
    exact (splitTorus.characterLatticeEquiv k I).symm.injective hα
  · rintro ⟨α, rfl⟩
    exact ⟨α, CoordinateRootDatum.fieldRealization_root k P α⟩

end Fibrewise

end Langlands.GroupScheme
