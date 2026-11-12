import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientHorizontalTransport
import Langlands.Automorphic.OperatorDeterminantTwistClasses

/-! # The cohomological condition at infinity for automorphic realizations

An actual automorphic operator realization of `GL_n` over a number field is cohomological
when, after a twist by a finite-order Hecke character composed with the determinant, its
relative Lie algebra cohomology with coefficients in some finite-dimensional algebraic
representation of `∏_{ι : F → ℂ} GL_n(ℂ)` is nonzero in some degree. The cohomology is the
published actual horizontal cohomology for the reduced Lie algebra and the full standard
compact group at infinity. The condition is invariant under equivalence and descends to
isomorphism classes and actual cuspidal classes. No cohomology is computed.
-/

noncomputable section

universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme
open ArchimedeanAlgebraicCoefficient

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance cohomologicalRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cohomologicalContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cohomologicalSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cohomologicalFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cohomologicalStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance cohomologicalSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable (F n) in
/-- The index set of all complex embeddings of `F`: one label at each real place and both
orientations at each complex place, enumerated in universe zero. -/
abbrev EmbeddingLabel : Type :=
  Fin (Fintype.card (EmbeddingIndex F))

variable (F n) in
/-- The finite-dimensional algebraic coefficient representations: algebraic representations
`∏_{ι : F → ℂ} GL_n(ℂ) → GL_m(ℂ)` of the complex group scheme, on `m`-dimensional spaces. -/
abbrev AlgebraicCoefficient (m : Type) [Fintype m] [DecidableEq m] :=
  MatrixRepresentation
    (GeneralLinearProductDualNumber.groupScheme (fun _ : EmbeddingLabel F => Fin n)
      (CommRingCat.of ℂ)) m

/-- An intertwining map with a left inverse is injective. -/
theorem injective_of_comp_eq_id {G V W : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap ρ)
    (h : g.comp f = Representation.IntertwiningMap.id ρ) : Function.Injective f := by
  intro a b hab
  have ha := DFunLike.congr_fun h a
  have hb := DFunLike.congr_fun h b
  simp only [Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.id_apply] at ha hb
  rw [← ha, ← hb, hab]

namespace OperatorRealization

variable [NeZero n]

/-- `S` has nonzero relative Lie algebra cohomology with algebraic coefficients: for some
algebraic coefficient representation `W` of `∏_{ι : F → ℂ} GL_n(ℂ)` and some degree `q`, the
published horizontal cohomology `H^q(𝔤̃_∞, K_∞; S ⊗ W)` is nonzero. -/
def HasNonzeroCoefficientCohomology (S : OperatorRealization F n) : Prop :=
  ∃ (m : Type) (_ : Fintype m) (_ : DecidableEq m) (W : AlgebraicCoefficient F n m) (q : ℕ),
    Nontrivial
      (TensorAlgebraicHorizontalCohomology (fullEmbeddingEnumeration F) W S q)

/-- `S` is cohomological: for some finite-order Hecke character `χ`, the twist of `S` by
`χ ∘ det` has nonzero relative Lie algebra cohomology with algebraic coefficients. The
archimedean components of a finite-order character are trivial at complex places and of order
at most two at real places, which is the twist allowed by Clozel's Lemma 3.14. -/
def IsCohomological (S : OperatorRealization F n) : Prop :=
  ∃ (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder),
    (S.determinantTwist χ hχ).HasNonzeroCoefficientCohomology

variable {S T : OperatorRealization F n}

/-- A full equivalence induces an injective map on algebraic coefficient cohomology. -/
theorem injective_tensorAlgebraicHorizontalCohomologyMap {m : Type} [Fintype m]
    [DecidableEq m] (W : AlgebraicCoefficient F n m) (e : S.Equivalence T) (q : ℕ) :
    Function.Injective
      (tensorAlgebraicHorizontalCohomologyMap (fullEmbeddingEnumeration F) W
        e.toIntertwiningMap q) := by
  have hid : e.symm.toIntertwiningMap.comp e.toIntertwiningMap =
      Representation.IntertwiningMap.id S.representation :=
    Representation.IntertwiningMap.ext (LinearMap.ext fun x => e.symm_apply_apply x)
  have h1 := (congrArg (fun L => tensorAlgebraicHorizontalCohomologyMap
      (fullEmbeddingEnumeration F) W L q) hid).trans
    (tensorAlgebraicHorizontalCohomologyMap_id (fullEmbeddingEnumeration F) W S q)
  have h2 := (tensorAlgebraicHorizontalCohomologyMap_comp (fullEmbeddingEnumeration F) W
    e.toIntertwiningMap e.symm.toIntertwiningMap q).symm.trans h1
  exact injective_of_comp_eq_id _ _ h2

/-- Nonzero algebraic coefficient cohomology is transported along full equivalences. -/
theorem HasNonzeroCoefficientCohomology.of_equiv (e : S.Equivalence T)
    (h : S.HasNonzeroCoefficientCohomology) : T.HasNonzeroCoefficientCohomology := by
  obtain ⟨m, hm, hd, W, q, hW⟩ := h
  refine ⟨m, hm, hd, W, q, ?_⟩
  obtain ⟨a, b, hab⟩ := hW.exists_pair_ne
  exact ⟨⟨_, _, fun h => hab (injective_tensorAlgebraicHorizontalCohomologyMap W e q h)⟩⟩

/-- The cohomological condition is transported along full equivalences. -/
theorem IsCohomological.of_equiv (e : S.Equivalence T) (h : S.IsCohomological) :
    T.IsCohomological := by
  obtain ⟨χ, hχ, h⟩ := h
  obtain ⟨e'⟩ := determinantTwist_congr ⟨e⟩ χ hχ
  exact ⟨χ, hχ, h.of_equiv e'⟩

/-- The cohomological condition is a property of the isomorphism class. -/
def IsoClass.IsCohomological (c : IsoClass F n) : Prop :=
  Quotient.lift (s := equivalenceSetoid F n)
    (fun S : OperatorRealization F n => S.IsCohomological)
    (fun S T (h : Nonempty (S.Equivalence T)) =>
      h.elim fun e => propext ⟨fun hS => hS.of_equiv e, fun hT => hT.of_equiv e.symm⟩) c

@[simp]
theorem isoClass_isCohomological (S : OperatorRealization F n) :
    S.isoClass.IsCohomological ↔ S.IsCohomological :=
  Iff.rfl

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- An actual cuspidal class of `GL_{r+1}` is cohomological when its operator class is. -/
def IsoClass.IsCohomological (c : IsoClass F r) : Prop :=
  c.toOperatorClass.IsCohomological

@[simp]
theorem isoClass_isCohomological (S : CuspidalOperatorRealization F r) :
    S.isoClass.IsCohomological ↔ S.realization.IsCohomological :=
  Iff.rfl

end CuspidalOperatorRealization

namespace PositiveRankCuspidalClass

variable [CompactSpace (AdeleQuotient F)]

/-- A mixed-rank actual cuspidal class is cohomological when its fixed-rank class is. -/
def IsCohomological (c : PositiveRankCuspidalClass F) : Prop :=
  c.2.IsCohomological

end PositiveRankCuspidalClass

end Langlands.Automorphic
