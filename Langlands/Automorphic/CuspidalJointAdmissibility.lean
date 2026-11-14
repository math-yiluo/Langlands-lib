import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Automorphic.CuspidalAdmissible.JointAdmissibility
import Langlands.Automorphic.HeckeTwist.Admissibility
import Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison
import Langlands.Global.AdelicGLSiegelFinitenessProof

/-!
# Joint admissibility of every actual cuspidal realization

The Library proves joint admissibility (`OperatorRealization.IsJointlyAdmissible`) of actual
cuspidal realizations with a unitary central character
(`CuspidalAdmissible.isJointlyAdmissible_of_siegelFiniteness`, with the proved Siegel-set
finiteness). This module removes the central-character hypothesis.

* `OperatorRealization.isJointlyAdmissible_of_heckeDeterminantTwist`: joint admissibility of
  the twist of `S` by `χ ∘ det` implies that of `S`. Composition with the twisting isomorphism
  maps the multiplicity space of `S` for an open subgroup `L` and a representation `σ`
  injectively into the multiplicity space of the twist for `L` intersected with the kernel of
  `χ ∘ det` on the finite adelic group and for `σ` multiplied by `χ ∘ det` on the compact
  group.
* `CuspidalOperatorRealization.isJointlyAdmissible`: every actual cuspidal realization is
  jointly admissible. Its twist by the unitarizing character of its central character has a
  unitary central character.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

local instance jointAdmRationalAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance jointAdmContinuousAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance jointAdmSmoothAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance jointAdmFormsAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance jointAdmStableAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance jointAdmSpaceAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

/-- The scalar twist of a representation of the standard compact by `χ ∘ det`. -/
def compactDeterminantTwistRep (χ : HeckeCharacter F) {m : ℕ}
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ) where
  toFun k := ((χ.compactAdelicDeterminant n k : ℂˣ) : ℂ) • σ k
  map_one' := by
    rw [map_one, map_one, Units.val_one, one_smul]
  map_mul' k l := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

/-- **Joint admissibility descends along determinant twists.** -/
theorem isJointlyAdmissible_of_heckeDeterminantTwist (χ : HeckeCharacter F)
    (h : (S.heckeDeterminantTwist χ).IsJointlyAdmissible) : S.IsJointlyAdmissible := by
  intro L m σ
  let K₀ : OpenSubgroup (FiniteAdelicGL F n) :=
    ⟨(χ.finiteAdelicDeterminant n).toMonoidHom.ker, χ.finiteAdelicHeckeDeterminant_isOpen_ker n⟩
  let L₀ : OpenSubgroup (FiniteAdelicGL F n) := L ⊓ K₀
  let σ' := compactDeterminantTwistRep (n := n) χ σ
  have hfin := h L₀ m σ'
  let e := S.heckeDeterminantTwistEquiv χ
  let T := S.heckeDeterminantTwist χ
  have hmem : ∀ φ ∈ jointMultiplicitySpace S.finiteRepresentation S.compactRepresentation
      L.toSubgroup σ, e.toLinearMap ∘ₗ φ ∈ jointMultiplicitySpace T.finiteRepresentation
        T.compactRepresentation L₀.toSubgroup σ' := by
    intro φ hφ
    refine ⟨fun v d => ?_, fun k v => ?_⟩
    · have hd : (d : FiniteAdelicGL F n) ∈ L ∧ (d : FiniteAdelicGL F n) ∈ K₀ := d.2
      have h1 : S.finiteRepresentation d (φ v) = φ v := hφ.1 v ⟨d, hd.1⟩
      have h2 : ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂˣ) : ℂ) = 1 := by
        have : χ.finiteAdelicDeterminant n d = 1 := hd.2
        change ((χ.finiteAdelicDeterminant n d : ℂˣ) : ℂ) = 1
        rw [this, Units.val_one]
      have e1 := S.heckeDeterminantTwistEquiv_finite χ d (φ v)
      have e2 : ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂˣ) : ℂ) •
          e (S.finiteRepresentation d (φ v)) = e (φ v) :=
        (congrArg (fun y => ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂˣ) : ℂ) • e y)
          h1).trans ((congrArg (fun c : ℂ => c • e (φ v)) h2).trans (one_smul ℂ _))
      exact e1.trans e2
    · have hσ' : σ' k v = ((χ.compactAdelicDeterminant n k : ℂˣ) : ℂ) • σ k v := rfl
      have e1 : e (φ (σ' k v)) = ((χ.compactAdelicDeterminant n k : ℂˣ) : ℂ) • e (φ (σ k v)) :=
        (congrArg (fun y => e (φ y)) hσ').trans
          ((congrArg e (map_smul φ _ (σ k v))).trans (map_smul e _ (φ (σ k v))))
      have e2 : ((χ.compactAdelicDeterminant n k : ℂˣ) : ℂ) • e (φ (σ k v)) =
          ((χ.compactAdelicDeterminant n k : ℂˣ) : ℂ) • e (S.compactRepresentation k (φ v)) :=
        congrArg (fun y => ((χ.compactAdelicDeterminant n k : ℂˣ) : ℂ) • e y) (hφ.2 k v)
      have e3 := (S.heckeDeterminantTwistEquiv_compact χ k (φ v)).symm
      exact e1.trans (e2.trans e3)
  let Φ : jointMultiplicitySpace S.finiteRepresentation S.compactRepresentation L.toSubgroup σ
      →ₗ[ℂ] jointMultiplicitySpace T.finiteRepresentation T.compactRepresentation
        L₀.toSubgroup σ' :=
    { toFun := fun φ => ⟨e.toLinearMap ∘ₗ φ.1, hmem φ.1 φ.2⟩
      map_add' := fun φ ψ => by
        apply Subtype.ext
        exact LinearMap.comp_add _ _ _
      map_smul' := fun c φ => by
        apply Subtype.ext
        exact LinearMap.comp_smul _ _ _ }
  have hΦ : Function.Injective Φ := by
    intro φ ψ hφψ
    apply Subtype.ext
    refine LinearMap.ext fun v => e.injective ?_
    exact LinearMap.congr_fun (congrArg Subtype.val hφψ) v
  have hfin' : FiniteDimensional ℂ (jointMultiplicitySpace T.finiteRepresentation
      T.compactRepresentation L₀.toSubgroup σ') := hfin
  have hN : IsNoetherian ℂ (jointMultiplicitySpace T.finiteRepresentation
      T.compactRepresentation L₀.toSubgroup σ') :=
    isNoetherian_of_isNoetherianRing_of_finite ℂ (jointMultiplicitySpace T.finiteRepresentation
      T.compactRepresentation L₀.toSubgroup σ')
  exact Module.Finite.of_injective Φ hΦ

end OperatorRealization

namespace CuspidalOperatorRealization

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- **Joint admissibility of actual cuspidal realizations**, with no central-character
hypothesis. -/
theorem isJointlyAdmissible (T : CuspidalOperatorRealization F r) :
    T.realization.IsJointlyAdmissible := by
  obtain ⟨ω, hω, -⟩ :=
    OperatorRealization.existsUnique_hasCentralCharacter T.realization T.irreducible
  have hu := hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter T hω
  have hJ := CuspidalAdmissible.isJointlyAdmissible_of_siegelFiniteness
    PrimitiveAdelicHeight.siegelSetGLFiniteness _ hu
  exact T.realization.isJointlyAdmissible_of_heckeDeterminantTwist
    (unitarizingCharacter r ω) hJ

end CuspidalOperatorRealization

end Langlands.Automorphic
