import Langlands.MathlibBase
import WeilConjectures.DeligneLaumon.AffineLine.Perverse
import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
import WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform
import WeilConjectures.WeilSheaf.FourierInversion.Reflection

/-!
# The three types of simple perverse Weil sheaves on the line and the Fourier transform

Laumon 1987, (1.4.2) and Théorème (1.4.2.1), pp. 148–149: a simple perverse sheaf on the affine
line `A` over a finite field `k` is of one of three types — punctual `(T1)`, the transform type
`(T2)` built from the Artin–Schreier kernel on a closed point of the dual line, and the
nonexceptional middle extensions `(T3)` — and the Fourier transform exchanges `(T1)` and `(T2')`,
`(T2)` and `(T1')`, and carries `(T3)` to `(T3')`. This module states this on weil-conjectures'
Weil complexes of the line.
-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.Henniart.Laumon

variable (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- A **closed point datum** on the line: a closed immersion `i : Z ↪ 𝔸¹_k`, the base change
`X' = Z ×_k 𝔸¹` of the product along `i × 1` with its projections `q : X' → Z`,
`i' : X' → 𝔸¹ × 𝔸¹` and the finite projection `π : X' → 𝔸¹` to the second factor, and a Weil
sheaf `sheaf` on `Z`. These are the data of weil-conjectures'
`WeilSheaf.nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback`. -/
structure FourierPointDatum where
  /-- The closed subscheme `Z`. -/
  Z : Scheme.{u}
  [overZ : Z.Over (Spec (CommRingCat.of k))]
  /-- The product `X' = Z ×_k 𝔸¹`. -/
  X' : Scheme.{u}
  [overX' : X'.Over (Spec (CommRingCat.of k))]
  [locallyOfFiniteType_X' : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k))]
  /-- The closed immersion `i : Z ↪ 𝔸¹`. -/
  i : Z ⟶ affineLine k
  [isClosedImmersion_i : IsClosedImmersion i]
  [isOver_i : i.IsOver (Spec (CommRingCat.of k))]
  /-- The projection `q : X' → Z`. -/
  q : X' ⟶ Z
  [isOver_q : q.IsOver (Spec (CommRingCat.of k))]
  /-- The map `i' = i × 1 : X' → 𝔸¹ × 𝔸¹`. -/
  i' : X' ⟶ affinePlane k
  [isOver_i' : i'.IsOver (Spec (CommRingCat.of k))]
  [isSeparated_i' : IsSeparated i']
  [locallyOfFiniteType_i' : LocallyOfFiniteType i']
  [quasiCompact_i' : QuasiCompact i']
  /-- The finite projection `π : X' → 𝔸¹` to the second factor. -/
  π : X' ⟶ affineLine k
  [isOver_π : π.IsOver (Spec (CommRingCat.of k))]
  [isFinite_π : IsFinite π]
  comp_snd : i' ≫ affinePlane.snd k = π
  isPullback : IsPullback q i' i (affinePlane.fst k)
  /-- The Weil sheaf on `Z`. -/
  sheaf : WeilSheaf k ℓ Z

attribute [instance] FourierPointDatum.overZ FourierPointDatum.overX'
  FourierPointDatum.locallyOfFiniteType_X' FourierPointDatum.isClosedImmersion_i
  FourierPointDatum.isOver_i FourierPointDatum.isOver_q FourierPointDatum.isOver_i'
  FourierPointDatum.isSeparated_i' FourierPointDatum.locallyOfFiniteType_i'
  FourierPointDatum.quasiCompact_i' FourierPointDatum.isOver_π FourierPointDatum.isFinite_π

namespace FourierPointDatum

variable {k ℓ}

/-- The punctual Weil complex `i_* E` (in degree `0`) of a closed point datum: a perverse sheaf of
type `(T1)` when `E` is simple. -/
def punctual (P : FourierPointDatum k ℓ) : WeilComplex k ℓ (affineLine k) :=
  (WeilComplex.derivedLowerShriek k ℓ P.i).obj (WeilSheaf.toComplex.obj P.sheaf)

/-- The Weil sheaf `π_*(i'^* Lψ(xx') ⊗ q^* E)` on the line attached to a closed point datum. -/
def kernelSheaf (P : FourierPointDatum k ℓ) (ψ : AddChar k (PadicAlgCl ℓ)) :
    WeilSheaf k ℓ (affineLine k) :=
  (WeilSheaf.lowerStar P.π).obj
    (((WeilSheaf.upperStar P.i').obj (fourierKernel ψ)).tensorObj
      ((WeilSheaf.upperStar P.q).obj P.sheaf)
      (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ)))

/-- The Weil complex `π_*(i'^* Lψ(xx') ⊗ q^* E)[1]` of a closed point datum: a perverse sheaf of
type `(T2)` when `E` is simple (Laumon (1.4.2)); the kernel `Lψ(xx')` is symmetric, so the
same object is of type `(T2)` on `A` and of type `(T2')` on `A'`. -/
def kernelType (P : FourierPointDatum k ℓ) (ψ : AddChar k (PadicAlgCl ℓ)) :
    WeilComplex k ℓ (affineLine k) :=
  WeilSheaf.toShiftedComplex.obj (P.kernelSheaf ψ)

end FourierPointDatum

/-- Type `(T1)` (Laumon (1.4.2)): isomorphic to `i_* E` for a closed point datum with simple
Weil sheaf `E`. -/
def IsPunctualFourierType (K : WeilComplex k ℓ (affineLine k)) : Prop :=
  ∃ P : FourierPointDatum k ℓ, Simple P.sheaf ∧ Nonempty (K ≅ P.punctual)

/-- Type `(T2)` (Laumon (1.4.2)): isomorphic to `π_*(i'^* Lψ(xx') ⊗ q^* E)[1]` for a closed
point datum with simple Weil sheaf `E`. -/
def IsKernelFourierType (ψ : AddChar k (PadicAlgCl ℓ)) (K : WeilComplex k ℓ (affineLine k)) :
    Prop :=
  ∃ P : FourierPointDatum k ℓ, Simple P.sheaf ∧ Nonempty (K ≅ P.kernelType ψ)

/-- Type `(T3)` (Laumon (1.4.2)): isomorphic to the middle extension `j_* F[1]` of an irreducible
lisse Weil sheaf `F` on a dense open `j : U ↪ A` with no geometric constituent `Lψ(a x)`,
`a ∈ k̄` (weil-conjectures' `WeilSheaf.IsNonexceptional`). -/
def IsNonexceptionalFourierType (ψ : AddChar k (PadicAlgCl ℓ))
    (K : WeilComplex k ℓ (affineLine k)) : Prop :=
  ∃ D : WeilSheaf.LisseOnDenseOpen k ℓ, D.sheaf.IsIrreducibleLisse ∧
    D.sheaf.IsNonexceptional ψ D.j ∧ Nonempty (K ≅ D.middleExtension)

/-- **The Fourier transform and the three types** (Laumon (1.4.2)–Théorème (1.4.2.1),
pp. 148–149; BBD (4.3.1)(ii)). For a nontrivial character `ψ` of the finite field `k`:
every simple perverse Weil sheaf on the line is of type `(T1)`, `(T2)` or `(T3)`; for every closed
point datum, `FTψ(i_* E) ≅ π_*(i'^* Lψ(xx') ⊗ q^* E)[1]` and
`FTψ(π_*(i'^* Lψ(xx') ⊗ q^* E)[1]) ≅ [-1]^* i_* E(-1)`; and the transform of an object of type
`(T3)` is of type `(T3')`, i.e. its output is again nonexceptional. -/
def WeilFourierTypeExchangeStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)), ψ ≠ 1 →
    (∀ K : (WeilComplex.curvePerverse (k₀ := k) (l := ℓ)).FullSubcategory, Simple K →
      IsPunctualFourierType k ℓ K.obj ∨ IsKernelFourierType k ℓ ψ K.obj ∨
        IsNonexceptionalFourierType k ℓ ψ K.obj) ∧
    (∀ P : FourierPointDatum k ℓ,
      Nonempty ((fourierTransform ψ).obj P.punctual ≅ P.kernelType ψ)) ∧
    (∀ P : FourierPointDatum k ℓ,
      Nonempty ((fourierTransform ψ).obj (P.kernelType ψ) ≅
        (WeilComplex.tateTwist k ℓ (affineLine k) (-1)).obj
          ((WeilComplex.upperStar (affineLine.neg k)).obj P.punctual))) ∧
    ∀ K : WeilComplex k ℓ (affineLine k), IsNonexceptionalFourierType k ℓ ψ K →
      IsNonexceptionalFourierType k ℓ ψ ((fourierTransform ψ).obj K)

end Langlands.Henniart.Laumon
