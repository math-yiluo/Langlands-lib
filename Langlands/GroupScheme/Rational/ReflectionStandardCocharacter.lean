import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.ReflectionNegation
import Langlands.GroupScheme.Rational.StandardCocharacterReduction
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Standard cocharacters from actual integral reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

section Local

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)

/-- Finite actual integral reflections supply independence of the simple roots.
No generation or faithfulness assertion for the Weyl quotient is used. -/
theorem RelativeRootReflectionData.linearIndependent_simpleRelativeRoots
    (D : RelativeRootReflectionData i)
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν) :
    LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)) := by
  classical
  let := hfinite.fintype
  let P := D.rootPairing hT hfinite
  have : P.IsRootSystem := D.rootPairing_isRootSystem hT hfinite
  have : P.IsCrystallographic := D.rootPairing_isCrystallographic hT hfinite
  let V := ℚ ⊗[ℤ] characterLattice T
  let W := relativeRootSpan i
  let f : W →ₗ[ℚ] ℚ := RelativeRootSystem.corootFunctional i ν
  have hfr (α : relativeRoots i) :
      f (P.root α) = (latticePairing T α.val ν : ℚ) :=
    RelativeRootSystem.corootFunctional_rootVector i ν α
  have hf (α : relativeRoots i) : f (P.root α) ≠ 0 := by
    rw [hfr]
    exact_mod_cast hν α.val α.property
  let a : simpleRelativeRoots i ν → relativeRoots i := fun α => ⟨α.val, α.property.1.1⟩
  have hbase (α : simpleRelativeRoots i ν) :
      a α ∈ IsAddIndecomposable.baseOf P.root f.toAddMonoidHom := by
    refine ⟨?_, fun β hβ γ hγ heq => ?_⟩
    · change 0 < f (P.root (a α))
      rw [hfr]
      exact_mod_cast α.property.1.2
    · exfalso
      apply α.property.2
      have hβpos : 0 < latticePairing T β.val ν := by
        change 0 < f (P.root β) at hβ
        rw [hfr] at hβ
        exact_mod_cast hβ
      have hγpos : 0 < latticePairing T γ.val ν := by
        change 0 < f (P.root γ) at hγ
        rw [hfr] at hγ
        exact_mod_cast hγ
      refine ⟨β.val, ⟨β.property, hβpos⟩, γ.val, ⟨γ.property, hγpos⟩, ?_⟩
      apply hT.character_toRat_injective
      rw [map_add]
      exact congrArg Subtype.val heq
  let a' : simpleRelativeRoots i ν →
      IsAddIndecomposable.baseOf P.root f.toAddMonoidHom := fun α => ⟨a α, hbase α⟩
  have ha' : Function.Injective a' := by
    intro α β hab
    apply Subtype.ext
    exact congrArg
      (fun j : IsAddIndecomposable.baseOf P.root f.toAddMonoidHom => j.val.val) hab
  have hli := (P.linearIndepOn_root_baseOf f.toAddMonoidHom hf).comp a' ha'
  have hli' := hli.map' W.subtype (by simp)
  convert hli' using 1
  funext α
  rfl

/-- Standard cocharacters need only the finite reflection pairing, independently
of generation or faithfulness of the actual relative Weyl quotient. -/
theorem RelativeRootReflectionData.exists_standardCocharacter
    (D : RelativeRootReflectionData i)
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta :=
  exists_standardCocharacter_of_linearIndependent i ν hT
    (D.linearIndependent_simpleRelativeRoots i ν hT hfinite hν) J hJ

/-- A standard cocharacter selected using actual integral reflection data. -/
def standardCocharacterOfRootReflections
    (D : RelativeRootReflectionData i)
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    cocharacterLattice T :=
  (D.exists_standardCocharacter i ν hT hfinite hν J hJ).choose

theorem standardCocharacterOfRootReflections_spec
    (D : RelativeRootReflectionData i)
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    IsStandardCocharacter i ν J
      (standardCocharacterOfRootReflections i ν D hT hfinite hν J hJ) :=
  (D.exists_standardCocharacter i ν hT hfinite hν J hJ).choose_spec

/-- Reflection negation closure and an explicit sign comparison give equality
of dynamic subgroups for every pair of standard cocharacters of a face. -/
theorem RelativeRootReflectionData.standardCocharacterDynamicComparison
    (D : RelativeRootReflectionData i) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T))
    (hsign : ∀ zeta eta : cocharacterLattice T,
      HaveSameRelativeRootSigns i zeta eta →
        Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
        Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    StandardCocharacterDynamicComparison i ν J := by
  intro zeta hzeta eta heta
  exact hsign zeta eta (hzeta.haveSameRelativeRootSigns i ν hν
    (fun _ hα => D.neg_mem_relativeRoots i hα) heta)

end Local

/-- Existence follows from intrinsic reflection existence without the
generation and faithfulness clauses of the full relative-root-system target. -/
theorem exists_standardCocharacter_of_relativeRootReflectionExistenceStatement
    (hreflect : RelativeRootReflectionExistenceStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
        ∃ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro hν J hJ
  obtain ⟨D, _⟩ := hreflect k G hG T i hi
  have hT := hi.isSplitSubtorus.1
  exact D.exists_standardCocharacter i ν hT (hT.finite_relativeRoots i) hν J hJ

/-- Conditional assembly of the unchanged host target from intrinsic reflection
existence and the sign-to-dynamic statement. Neither structural input is proved. -/
theorem standardCocharacterStatement_of_reflections_of_signs
    (hreflect : RelativeRootReflectionExistenceStatement.{u})
    (hsign : RelativeRootSignsDetermineDynamicStatement.{u}) :
    StandardCocharacterStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro hν J hJ
  obtain ⟨D, _⟩ := hreflect k G hG T i hi
  have hT := hi.isSplitSubtorus.1
  refine ⟨D.exists_standardCocharacter i ν hT (hT.finite_relativeRoots i) hν J hJ, ?_⟩
  intro zeta hzeta
  exact (D.standardCocharacterDynamicComparison i ν hν J
    (hsign k G hG T i hi)).standard_eq_dynamic i ν J hzeta

end Langlands.GroupScheme
