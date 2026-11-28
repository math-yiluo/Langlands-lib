import Langlands.Automorphic.GeneralLinearDiscreteCuspidalHeckeIsolationStatement
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicGL
import Langlands.GroupScheme.FiniteAlgebraUnits
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Finiteness of the Hecke class of a cuspidal representation of `GL_n` on a division algebra

Let `E` be a number field, `A` a central division algebra of dimension `n² = (r + 1)²` over `E`
and `G' = Aˣ` its unit group scheme. Given a cuspidal realization `S` of `GL_n` over `E`, a finite
set `Ω` of finite places and algebra isomorphisms `E_p ⊗ A ≃ M_n(E_p)` for the finite places
`p ∉ Ω` and `E_∞ ⊗ A ≃ M_n(E_∞)`, a closed subspace of `L²([G'])` is in the Hecke class of `S`
off `Ω` if at every finite place outside `Ω` it has the spherical Hecke character of `S`, and
at the archimedean place it contains an isometric copy of an irreducible constituent of the
closure `V_S` of the `L²` classes of the forms of `S`. The proposition
`DivisionAlgebraHeckeClassFinitenessStatement` asserts that, when `E_v ⊗ A` is a division algebra
or a matrix algebra at every `v ∈ Ω`, only finitely many members of a Hilbert sum decomposition
of `L²([G'])` into irreducible closed invariant subspaces are in the Hecke class of `S` off `Ω`.

The statement is derived from Deligne–Kazhdan–Vignéras 1984, B.1.d–e (the Corollary of B.1.e,
printed p. 81), with the global functional equation of Godement–Jacquet 1972, Corollary 13.8;
the paired Markdown gives the argument. The module defines the charts, the local and archimedean
actions on `L²([G'])` and `L²([GL_n])` and the Hecke class, and states the proposition. It
contains no proof. -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic.DivisionHeckeClass

open Langlands.Global Langlands.GroupScheme Langlands.Automorphic.DiscreteHeckeIsolation

local instance divisionHeckeGeneralLinearIsAffine (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance divisionHeckeGeneralLinearLocallyOfFiniteType (F : Type) [Field F] (n : ℕ) :
    LocallyOfFiniteType (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  have := IsConnectedReductive.smooth (isConnectedReductive_generalLinear F (Fin n))
  inferInstance

local instance divisionHeckeRationalAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance divisionHeckeContinuousAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance divisionHeckeSmoothAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance divisionHeckeFormsAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance divisionHeckeStableAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance divisionHeckeRealizationAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ)
    (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

section Charts

variable {E : Type} [Field E] [NumberField E] {A : Type} [Ring A] [Algebra E A]
  [FiniteDimensional E A] {r : ℕ}

/-- The chart at a finite place `p`: a point of `G' = Aˣ` over `E_p` is a unit of `E_p ⊗[E] A`
(`FiniteAlgebraUnits.affinePointsEquiv`), which the `E_p`-algebra isomorphism
`s : E_p ⊗[E] A ≃ M_{r+1}(E_p)` sends to `GL_{r+1}(E_p)`. -/
def localChart (p : Langlands.Global.FinitePlace E)
    (s : FiniteCompletion E p ⊗[E] A ≃ₐ[FiniteCompletion E p]
      Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion E p)) :
    PlaceGroupPoints E (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)) (.inr p) ≃*
      FiniteLocalGL E (r + 1) p :=
  (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis E A) (placeCompletion E (.inr p))).trans
    (Units.mapEquiv s.toRingEquiv.toMulEquiv)

/-- The archimedean chart: a point of `G' = Aˣ` over `E_∞ = E ⊗ ℝ` (`InfiniteAdeleRing E`) is a
unit of `E_∞ ⊗[E] A`, which the `E_∞`-algebra isomorphism `s : E_∞ ⊗[E] A ≃ M_{r+1}(E_∞)` sends
to `GL_{r+1}(E_∞)`. -/
def infiniteChart
    (s : InfiniteAdeleRing E ⊗[E] A ≃ₐ[InfiniteAdeleRing E]
      Matrix (Fin (r + 1)) (Fin (r + 1)) (InfiniteAdeleRing E)) :
    InfiniteAdelicGroupPoints E (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)) ≃*
      InfiniteAdelicGL E (r + 1) :=
  (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis E A)
      (CommAlgCat.of E (InfiniteAdeleRing E))).trans
    (Units.mapEquiv s.toRingEquiv.toMulEquiv)

variable (hG' : IsConnectedReductive (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)))

/-- The right regular representation of `G'(𝔸_E)` on `L²([G'])` (canonical measure), restricted
to `GL_{r+1}(E_p)` through the chart `s` at the finite place `p` and the inclusion of the local
points at `p` (`AdelicGroupPoints.ofPlace`). -/
def divisionL2LocalAction (p : Langlands.Global.FinitePlace E)
    (s : FiniteCompletion E p ⊗[E] A ≃ₐ[FiniteCompletion E p]
      Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion E p)) :
    Representation ℂ (FiniteLocalGL E (r + 1) p)
      (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
        (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)))) :=
  (RestrictionSplitCentre.canonicalL2RightAction E
      (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)) centralSplitTorusCharacter hG').comp
    ((AdelicGroupPoints.ofPlace E (FiniteAlgebraUnits.groupScheme (Module.finBasis E A))
        (.inr p)).comp (localChart p s).symm.toMonoidHom)

/-- The right regular representation of `G'(𝔸_E)` on `L²([G'])` (canonical measure), restricted
to `GL_{r+1}(E_∞)` through the archimedean chart `s` and the inclusion of the archimedean points
(`AdelicGroupPoints.ofInfinite`). -/
def divisionL2InfiniteAction
    (s : InfiniteAdeleRing E ⊗[E] A ≃ₐ[InfiniteAdeleRing E]
      Matrix (Fin (r + 1)) (Fin (r + 1)) (InfiniteAdeleRing E)) :
    Representation ℂ (InfiniteAdelicGL E (r + 1))
      (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
        (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)))) :=
  (RestrictionSplitCentre.canonicalL2RightAction E
      (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)) centralSplitTorusCharacter hG').comp
    ((AdelicGroupPoints.ofInfinite E
        (FiniteAlgebraUnits.groupScheme (Module.finBasis E A))).toMonoidHom.comp
      (infiniteChart s).symm.toMonoidHom)

end Charts

section GeneralLinear

variable (E : Type) [Field E] [NumberField E] (r : ℕ)

/-- The right regular representation of `GL_{r+1}(𝔸_E)` on `L²([GL_{r+1}])` (canonical
measure), restricted to `GL_{r+1}(E_∞)` in the matrix model: a matrix is sent to the point of the
group scheme with that matrix (`GroupScheme.GeneralLinear.affinePointsEquiv`), which is included
as an archimedean point (`AdelicGroupPoints.ofInfinite`). -/
def canonicalL2InfiniteAction :
    Representation ℂ (InfiniteAdelicGL E (r + 1))
      (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
        (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of E)))) :=
  (RestrictionSplitCentre.canonicalL2RightAction E
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of E))
      centralSplitTorusCharacter (isConnectedReductive_generalLinear E (Fin (r + 1)))).comp
    ((AdelicGroupPoints.ofInfinite E
        (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of E))).toMonoidHom.comp
      (GroupScheme.GeneralLinear.affinePointsEquiv (Fin (r + 1)) (CommRingCat.of E)
        (CommAlgCat.of E (InfiniteAdeleRing E))).symm.toMonoidHom)

end GeneralLinear

section HeckeClass

variable {E : Type} [Field E] [NumberField E] [CompactSpace (AdeleQuotient E)] {A : Type} [Ring A]
  [Algebra E A] [FiniteDimensional E A] {r : ℕ}

/-- The closed subspace `T` of `L²([G'])` is in the Hecke class of the cuspidal realization `S`
off the finite set `Ω` of finite places, for the charts `s` (at the finite places outside `Ω`)
and `sInf` (archimedean):

* at every finite place `p ∉ Ω` there is a character `χ` of the spherical Hecke algebra of
  `GL_{r+1}(E_p)` such that `T`, for the action `divisionL2LocalAction hG' p (s p hp)`, and the
  space of `S` have nonzero vectors fixed by `GL_{r+1}(𝒪_p)` on which the Hecke algebra acts by
  `χ` (`HasSphericalHeckeCharacterOn`);
* some closed `GL_{r+1}(E_∞)`-invariant subspace `W` of `V_S = cuspidalRealizationClosure E r S`
  with no closed invariant subspace other than `0` and `W` admits a linear isometry into `T`
  intertwining `canonicalL2InfiniteAction E r` with `divisionL2InfiniteAction hG' sInf`. -/
def IsInHeckeClass
    (hG' : IsConnectedReductive (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)))
    (S : CuspidalOperatorRealization E r) (Ω : Finset (Langlands.Global.FinitePlace E))
    (s : ∀ p : Langlands.Global.FinitePlace E, p ∉ Ω →
      (FiniteCompletion E p ⊗[E] A ≃ₐ[FiniteCompletion E p]
        Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion E p)))
    (sInf : InfiniteAdeleRing E ⊗[E] A ≃ₐ[InfiniteAdeleRing E]
      Matrix (Fin (r + 1)) (Fin (r + 1)) (InfiniteAdeleRing E))
    (T : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
      (FiniteAlgebraUnits.groupScheme (Module.finBasis E A))))) : Prop :=
  (∀ (p : Langlands.Global.FinitePlace E) (hp : p ∉ Ω),
    ∃ χ : Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField p) r →ₐ[ℂ] ℂ,
      HasSphericalHeckeCharacterOn (divisionL2LocalAction hG' p (s p hp)) T χ ∧
        HasSphericalHeckeCharacterOn (S.realization.localRepresentation p) ⊤ χ) ∧
  ∃ W : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of E)))),
    W ≤ cuspidalRealizationClosure E r S ∧
    Langlands.Analysis.IsIrreducibleSubrepresentation (canonicalL2InfiniteAction E r) W ∧
    ∃ f : W →ₗᵢ[ℂ] Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
        (FiniteAlgebraUnits.groupScheme (Module.finBasis E A))),
      (∀ x : W, f x ∈ T) ∧
      ∀ (g : InfiniteAdelicGL E (r + 1)) (x y : W),
        (y : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
            (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of E)))) =
          canonicalL2InfiniteAction E r g x →
        f y = divisionL2InfiniteAction hG' sInf g (f x)

end HeckeClass

/-- **Finiteness of the Hecke class of a cuspidal representation of `GL_n` on a division
algebra** (Deligne–Kazhdan–Vignéras, B.1.e, Corollary). Let `E` be a number field with compact
adele quotient, `r : ℕ`, `S` a cuspidal realization of `GL_{r+1}` over `E` trivial on the
positive split centre, and `A` a central division algebra over `E` of dimension `(r + 1)²`
whose unit group scheme `G'` is connected reductive. Let `Ω` be a finite set of finite places
such that at every `v ∈ Ω` the algebra `E_v ⊗[E] A` is a division algebra or is isomorphic to
`M_{r+1}(E_v)`, and let `s` be charts `E_p ⊗[E] A ≃ M_{r+1}(E_p)` at the finite places `p ∉ Ω`
and `sInf` a chart `E_∞ ⊗[E] A ≃ M_{r+1}(E_∞)`. Then for every family `P` of nonzero closed
`G'(𝔸_E)`-invariant subspaces of `L²([G'])` without closed invariant subspaces other than `0` and
themselves whose inclusions form a Hilbert sum, only finitely many members `P i` are in the
Hecke class of `S` off `Ω` (`IsInHeckeClass`). -/
def DivisionAlgebraHeckeClassFinitenessStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [CompactSpace (AdeleQuotient E)] (r : ℕ)
    (S : CuspidalOperatorRealization E r),
    CuspidalPairPoles.IsTrivialOnSplitCentre S →
    ∀ (A : Type) [Ring A] [Algebra E A] [FiniteDimensional E A],
      Algebra.IsCentral E A → Module.finrank E A = (r + 1) ^ 2 →
      (∀ a : A, a ≠ 0 → IsUnit a) →
      ∀ (hG' : IsConnectedReductive (FiniteAlgebraUnits.groupScheme (Module.finBasis E A)))
        (Ω : Finset (Langlands.Global.FinitePlace E)),
        (∀ v ∈ Ω, (∀ a : FiniteCompletion E v ⊗[E] A, a ≠ 0 → IsUnit a) ∨
          Nonempty (FiniteCompletion E v ⊗[E] A ≃ₐ[FiniteCompletion E v]
            Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion E v))) →
        ∀ (s : ∀ p : Langlands.Global.FinitePlace E, p ∉ Ω →
            (FiniteCompletion E p ⊗[E] A ≃ₐ[FiniteCompletion E p]
              Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion E p)))
          (sInf : InfiniteAdeleRing E ⊗[E] A ≃ₐ[InfiniteAdeleRing E]
            Matrix (Fin (r + 1)) (Fin (r + 1)) (InfiniteAdeleRing E))
          (I : Type) (P : I → Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E
            (FiniteAlgebraUnits.groupScheme (Module.finBasis E A))))),
          (∀ i, Langlands.Analysis.IsIrreducibleSubrepresentation
            (RestrictionSplitCentre.canonicalL2RightAction E
              (FiniteAlgebraUnits.groupScheme (Module.finBasis E A))
              centralSplitTorusCharacter hG') (P i)) →
          IsHilbertSum ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ) →
          {i : I | IsInHeckeClass hG' S Ω s sInf (P i)}.Finite

end Langlands.Automorphic.DivisionHeckeClass
