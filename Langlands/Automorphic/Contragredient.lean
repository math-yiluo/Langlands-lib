import Langlands.Automorphic.ConjugateContragredient

/-!
# Contragredient realizations

An actual automorphic realization `T` of `GL_n(𝔸_F)` realizes the contragredient of a
realization `S` when a pairing `B : S × T → ℂ`, invariant under the finite, compact and
real Lie algebra operators acting on both variables, has partial map `x ↦ B (·) x` a
bijection from `T` onto the contragredient functionals of `S`. These are the algebraic
functionals on `S` that are smooth for the finite adelic group and finite for the
standard compact subgroup at infinity. No contragredient realization is constructed.
-/

noncomputable section

universe u

namespace Langlands.Automorphic

open NumberField Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance contragredientRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance contragredientContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance contragredientSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance contragredientFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance contragredientStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance contragredientSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

section Pairing

variable (S T : OperatorRealization F n)

/-- Invariance of a pairing between `S` and `T` under the finite, compact and real Lie
algebra operators acting on both variables. -/
def IsInvariantPairing (B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ) : Prop :=
  (∀ (d : FiniteAdelicGL F n) (y : S.Space) (x : T.Space),
      B (S.finiteRepresentation d y) (T.finiteRepresentation d x) = B y x) ∧
    (∀ (k : standardInfiniteCompact F n) (y : S.Space) (x : T.Space),
      B (S.compactRepresentation k y) (T.compactRepresentation k x) = B y x) ∧
    ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (y : S.Space) (x : T.Space),
      B (S.lieAction X y) x + B y (T.lieAction X x) = 0

/-- The partial map `x ↦ B (·) x` of an invariant pairing is a bijection from `T` onto
the contragredient functionals of `S`. -/
def IsContragredientPairing (B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ) : Prop :=
  S.IsInvariantPairing T B ∧
    (∀ x : T.Space, S.IsContragredientFunctional (B.flip x)) ∧
    Function.Injective B.flip ∧
    ∀ l : Module.Dual ℂ S.Space, S.IsContragredientFunctional l → ∃ x, B.flip x = l

end Pairing

/-- `T` realizes the contragredient of `S`. -/
def IsContragredientOf (T S : OperatorRealization F n) : Prop :=
  ∃ B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ, S.IsContragredientPairing T B

variable {S S' T T' : OperatorRealization F n}

section Intertwining

variable {B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ}

/-- The partial map of an invariant pairing intertwines the finite action of `T` with
the dual finite action on functionals on `S`. -/
theorem IsInvariantPairing.flip_finite (hB : S.IsInvariantPairing T B)
    (d : FiniteAdelicGL F n) (x : T.Space) :
    B.flip (T.finiteRepresentation d x) = S.finiteRepresentation.dual d (B.flip x) := by
  apply LinearMap.ext
  intro y
  have h := hB.1 d⁻¹ y (T.finiteRepresentation d x)
  have hx : T.finiteRepresentation d⁻¹ (T.finiteRepresentation d x) = x :=
    Representation.inv_self_apply _ d x
  change B y (T.finiteRepresentation d x) = B (S.finiteRepresentation d⁻¹ y) x
  exact h.symm.trans (congrArg (fun z => B (S.finiteRepresentation d⁻¹ y) z) hx)

/-- The partial map of an invariant pairing intertwines the compact action of `T` with
the dual compact action on functionals on `S`. -/
theorem IsInvariantPairing.flip_compact (hB : S.IsInvariantPairing T B)
    (k : standardInfiniteCompact F n) (x : T.Space) :
    B.flip (T.compactRepresentation k x) = S.compactRepresentation.dual k (B.flip x) := by
  apply LinearMap.ext
  intro y
  have h := hB.2.1 k⁻¹ y (T.compactRepresentation k x)
  have hx : T.compactRepresentation k⁻¹ (T.compactRepresentation k x) = x :=
    Representation.inv_self_apply _ k x
  change B y (T.compactRepresentation k x) = B (S.compactRepresentation k⁻¹ y) x
  exact h.symm.trans (congrArg (fun z => B (S.compactRepresentation k⁻¹ y) z) hx)

/-- The partial map of an invariant pairing intertwines the real Lie action of `T` with
the negative transpose of the real Lie action of `S`. -/
theorem IsInvariantPairing.flip_lieAction (hB : S.IsInvariantPairing T B)
    (X : ArchimedeanGL.RealLieAlgebra F n) (x : T.Space) :
    B.flip (T.lieAction X x) = -((B.flip x).comp (S.lieAction X)) := by
  apply LinearMap.ext
  intro y
  have h := hB.2.2 X y x
  change B y (T.lieAction X x) = -B (S.lieAction X y) x
  exact eq_neg_of_add_eq_zero_right h

end Intertwining

section Transport

/-- The same linear map intertwines the restricted compact actions. -/
private def compactRestriction (L : S.Intertwiner T) :
    S.compactRepresentation.IntertwiningMap T.compactRepresentation where
  toLinearMap := L.toLinearMap
  isIntertwining' k := L.isIntertwining' (compactOperator F n k)

/-- Contragredient functionals pull back along full-operator intertwiners. -/
private theorem isContragredientFunctional_comp (L : S.Intertwiner T)
    {l : Module.Dual ℂ T.Space} (hl : T.IsContragredientFunctional l) :
    S.IsContragredientFunctional (l.comp L.toLinearMap) :=
  ⟨isSmoothVector_map (dualIntertwining (Intertwiner.finiteRestriction L)) hl.1,
    hl.2.map (dualIntertwining (compactRestriction L))⟩

/-- A contragredient of `S` is a contragredient of every realization equivalent to `S`. -/
theorem IsContragredientOf.of_equivalence_left (e : S.Equivalence S')
    (h : T.IsContragredientOf S) : T.IsContragredientOf S' := by
  obtain ⟨B, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := h
  let M : S'.Intertwiner S := e.symm.toIntertwiningMap
  refine ⟨B.comp M.toLinearMap, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro d y x
    change B (M (S'.finiteRepresentation d y)) (T.finiteRepresentation d x) = B (M y) x
    exact (congrArg (fun a => B a (T.finiteRepresentation d x))
      (Intertwiner.finite M d y)).trans (hd d (M y) x)
  · intro k y x
    change B (M (S'.compactRepresentation k y)) (T.compactRepresentation k x) = B (M y) x
    exact (congrArg (fun a => B a (T.compactRepresentation k x))
      (Intertwiner.compact M k y)).trans (hk k (M y) x)
  · intro X y x
    change B (M (S'.lieAction X y)) x + B (M y) (T.lieAction X x) = 0
    have hM : M (S'.lieAction X y) = S.lieAction X (M y) := Intertwiner.differential M _ y
    exact (congrArg (fun a => B a x + B (M y) (T.lieAction X x)) hM).trans (hX X (M y) x)
  · intro x
    exact isContragredientFunctional_comp M (hB x)
  · intro x₁ x₂ h
    apply hinj
    apply LinearMap.ext
    intro y
    have h₀ := LinearMap.congr_fun h (e y)
    change B (e.symm (e y)) x₁ = B (e.symm (e y)) x₂ at h₀
    change B y x₁ = B y x₂
    have hy : e.symm (e y) = y := e.symm_apply_apply y
    exact (congrArg (fun z => B z x₁) hy).symm.trans (h₀.trans (congrArg (fun z => B z x₂) hy))
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj (l.comp e.toIntertwiningMap.toLinearMap)
      (isContragredientFunctional_comp e.toIntertwiningMap hl)
    refine ⟨x, ?_⟩
    apply LinearMap.ext
    intro y
    have h₀ := LinearMap.congr_fun hx (e.symm y)
    change B (e.symm y) x = l (e (e.symm y)) at h₀
    change B (e.symm y) x = l y
    exact h₀.trans (congrArg l (e.apply_symm_apply y))

/-- A realization equivalent to a contragredient of `S` is a contragredient of `S`. -/
theorem IsContragredientOf.of_equivalence_right (e : T.Equivalence T')
    (h : T.IsContragredientOf S) : T'.IsContragredientOf S := by
  obtain ⟨B, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := h
  let M : T'.Intertwiner T := e.symm.toIntertwiningMap
  refine ⟨B.compl₂ M.toLinearMap, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro d y x
    change B (S.finiteRepresentation d y) (M (T'.finiteRepresentation d x)) = B y (M x)
    exact (congrArg (fun b => B (S.finiteRepresentation d y) b)
      (Intertwiner.finite M d x)).trans (hd d y (M x))
  · intro k y x
    change B (S.compactRepresentation k y) (M (T'.compactRepresentation k x)) = B y (M x)
    exact (congrArg (fun b => B (S.compactRepresentation k y) b)
      (Intertwiner.compact M k x)).trans (hk k y (M x))
  · intro X y x
    change B (S.lieAction X y) (M x) + B y (M (T'.lieAction X x)) = 0
    have hM : M (T'.lieAction X x) = T.lieAction X (M x) := Intertwiner.differential M _ x
    exact (congrArg (fun b => B (S.lieAction X y) (M x) + B y b) hM).trans (hX X y (M x))
  · intro x
    exact hB (M x)
  · intro x₁ x₂ h
    have h' : B.flip (M x₁) = B.flip (M x₂) := h
    have hM := hinj h'
    change e.symm x₁ = e.symm x₂ at hM
    exact e.symm.injective hM
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj l hl
    refine ⟨e x, ?_⟩
    change B.flip (e.symm (e x)) = l
    exact (congrArg B.flip (e.symm_apply_apply x)).trans hx

/-- Being a contragredient of `S` depends only on the equivalence class of `S`. -/
theorem isContragredientOf_congr_left (e : S.Equivalence S') :
    T.IsContragredientOf S ↔ T.IsContragredientOf S' :=
  ⟨IsContragredientOf.of_equivalence_left e, IsContragredientOf.of_equivalence_left e.symm⟩

/-- Being a contragredient of `S` depends only on the equivalence class of `T`. -/
theorem isContragredientOf_congr_right (e : T.Equivalence T') :
    T.IsContragredientOf S ↔ T'.IsContragredientOf S :=
  ⟨IsContragredientOf.of_equivalence_right e, IsContragredientOf.of_equivalence_right e.symm⟩

end Transport

/-- The class `d` is a contragredient of the class `c` when some representative of `d`
realizes the contragredient of some representative of `c`. -/
def IsoClass.IsContragredientOf (d c : IsoClass F n) : Prop :=
  ∃ S T : OperatorRealization F n, S.isoClass = c ∧ T.isoClass = d ∧ T.IsContragredientOf S

/-- For classes, one pair of representatives realizes the contragredient relation exactly
when every pair does. -/
theorem isoClass_isContragredientOf_iff (T S : OperatorRealization F n) :
    T.isoClass.IsContragredientOf S.isoClass ↔ T.IsContragredientOf S := by
  constructor
  · rintro ⟨S₀, T₀, hS, hT, h⟩
    obtain ⟨eS⟩ := (S₀.isoClass_eq_iff S).mp hS
    obtain ⟨eT⟩ := (T₀.isoClass_eq_iff T).mp hT
    exact (h.of_equivalence_left eS).of_equivalence_right eT
  · intro h
    exact ⟨S, T, rfl, rfl, h⟩

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The irreducible cuspidal class `d` is a contragredient of the irreducible cuspidal
class `c` when their full-operator classes are. -/
def IsoClass.IsContragredientOf (d c : IsoClass F r) : Prop :=
  d.toOperatorClass.IsContragredientOf c.toOperatorClass

/-- For irreducible cuspidal classes, the relation holds exactly when the actual
representatives realize it. -/
theorem isoClass_isContragredientOf_iff (T S : CuspidalOperatorRealization F r) :
    T.isoClass.IsContragredientOf S.isoClass ↔
      T.realization.IsContragredientOf S.realization :=
  OperatorRealization.isoClass_isContragredientOf_iff T.realization S.realization

end CuspidalOperatorRealization

end Langlands.Automorphic
