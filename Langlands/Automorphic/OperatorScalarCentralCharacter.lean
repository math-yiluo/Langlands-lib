import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.ClassField.Global.LocalRelativeWeilUnramified
import Langlands.Global.IdeleClosedSubgroupDensity
import Langlands.Representation.Unramified.TopHeckeOperator

/-! # Scalar matrices acting through a Hecke character

For an operator realization `S` of rank `n` and a Hecke character `χ`, the ideles `z` whose
scalar matrix acts on the functions of `S` by left multiplication through `χ(z)` form a
closed subgroup `centralCharacterSubgroup`, which contains the principal ideles by rational
invariance; `S` has central character `χ` when this subgroup is everything. A local idele
at a finite place `v` lies in it exactly when the local scalar matrix acts on `S` by the
value of the local component of `χ`. In an irreducible realization the local scalar
matrices are central, so such a matrix acts by a scalar as soon as it does so on one
nonzero vector.

The file also contains the commutation of local scalar matrices with the finite adelic
group, the scalar matrices of local and principal ideles, and the fact that a subgroup of
`F_v^×` containing the integral units and the uniformizer is the whole group. These are
used in `Langlands.Automorphic.CentralCharacterTopCoefficient`.
-/

noncomputable section
universe uF uP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter

namespace Langlands.Global

variable (F : Type uF) [Field F] [NumberField F]

namespace FiniteAdelicGL

/-- A scalar matrix inserted at one finite place is central in the finite adelic group. -/
theorem localInclusion_scalar_commute (n : ℕ) (v : FinitePlace F)
    (a : (FiniteCompletion F v)ˣ) (d : FiniteAdelicGL F n) :
    Commute (localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a)) d := by
  change _ * _ = _ * _
  apply ext_localProjection
  intro w
  simp only [map_mul]
  by_cases h : w = v
  · subst h
    rw [localProjection_localInclusion]
    apply Units.ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_comm _ (Commute.all _) _
  · rw [localProjection_localInclusion_of_ne F n v w h, one_mul, mul_one]

end FiniteAdelicGL

namespace AdelicGL

open scoped Classical in
/-- The scalar matrix of a local idele at a finite place is the finite adelic matrix of the
local scalar matrix inserted at that place. -/
theorem scalar_finiteIdeleInclusion (n : ℕ) (v : FinitePlace F) (a : (FiniteCompletion F v)ˣ) :
    scalar F n (finiteIdeleInclusion F v a) =
      ofFinite F n (FiniteAdelicGL.localInclusion F n v
        (Matrix.GeneralLinearGroup.scalar (Fin n) a)) := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · change (Matrix.scalar (Fin n) ((finiteIdeleInclusion F v a : Ideles F) : Adeles F) i j).1 =
      (1 : Matrix (Fin n) (Fin n) (InfiniteAdeles F)) i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    change (Matrix.scalar (Fin n) ((finiteIdeleInclusion F v a : Ideles F) : Adeles F) i j).2 w =
      FiniteAdelicGL.localProjection F n w (FiniteAdelicGL.localInclusion F n v
        (Matrix.GeneralLinearGroup.scalar (Fin n) a)) i j
    have hc := IdeleDensity.coord_finiteIdeleInclusion v w a
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hw : w = v
    · subst hw
      rw [FiniteAdelicGL.localProjection_localInclusion]
      change _ = (Matrix.scalar (Fin n) a.val) i j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · rw [Pi.mulSingle_eq_same] at hc
        exact hc
      · rfl
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw]
      change _ = (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F w)) i j
      rw [Matrix.one_apply]
      split_ifs
      · rw [Pi.mulSingle_eq_of_ne hw] at hc
        exact hc
      · rfl

/-- The scalar matrix of a principal idele is the rational scalar matrix. -/
theorem scalar_diagonalUnits (n : ℕ) (a : Fˣ) :
    scalar F n (diagonalUnits F a) = rational F n (Matrix.GeneralLinearGroup.scalar (Fin n) a) := by
  apply Units.ext
  ext i j
  change Matrix.scalar (Fin n) (algebraMap F (Adeles F) (a : F)) i j =
    algebraMap F (Adeles F) (Matrix.scalar (Fin n) (a : F) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact (map_zero _).symm

end AdelicGL

namespace CompletionPadic

open Langlands.ClassField.Global.RelativeWeilGroup

/-- A subgroup of `F_v^×` containing the integral units and the canonical uniformizer is the
whole group. -/
theorem subgroup_eq_top_of_uniformizer_mem (v : FinitePlace F)
    (G : Subgroup (FiniteCompletion F v)ˣ)
    (hu : ∀ a : (FiniteCompletion F v)ˣ,
      a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units → a ∈ G)
    (hϖ : LocalFactor.PadicAbelian.uniformizerUnit (padicField v).canonicalTopologicalData ∈ G) :
    G = ⊤ := by
  rw [eq_top_iff]
  intro a _
  let ϖ : (v.adicCompletion F)ˣ :=
    LocalFactor.PadicAbelian.uniformizerUnit (padicField v).canonicalTopologicalData
  have hne : Valued.v (a : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (a : v.adicCompletion F) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  have hϖm : Valued.v ((ϖ ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-m) := by
    have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value
      (padicField v).canonicalTopologicalData m
    rw [discreteValuation_padicField v] at h
    exact h
  have hval : Valued.v ((a * ϖ ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, map_mul, hm, hϖm, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hint : a * ϖ ^ m ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units := by
    refine ⟨?_, ?_⟩
    · change Valued.v ((a * ϖ ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1
      rw [hval]
    · change Valued.v (((a * ϖ ^ m)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  have ha : a = (a * ϖ ^ m) * (ϖ ^ m)⁻¹ := (mul_inv_cancel_right a (ϖ ^ m)).symm
  rw [ha]
  exact G.mul_mem (hu _ hint) (G.inv_mem (G.zpow_mem hϖ m))

end CompletionPadic

end Langlands.Global

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified
open ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F]

local instance scalarCentralRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance scalarCentralContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance scalarCentralSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance scalarCentralFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance scalarCentralStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance scalarCentralRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable {n : ℕ} (S : OperatorRealization F n)

/-- The scalar matrix of the idele `z` acts on the functions of `S` by left multiplication
through the value of the central idele character of `χ` at `z`. -/
def ScalarActsBy (χ : HeckeCharacter F) (z : Ideles F) : Prop :=
  ∀ (f : S.Space) (x : AdelicGL F n),
    evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
      (centralIdeleCharacter F χ z : ℂ) * evaluate F n (S.toContinuous f) x

theorem scalarActsBy_one (χ : HeckeCharacter F) : S.ScalarActsBy χ 1 := by
  intro f x
  rw [map_one, one_mul, map_one, Units.val_one, one_mul]

theorem scalarActsBy_mul (χ : HeckeCharacter F) {z w : Ideles F} (hz : S.ScalarActsBy χ z)
    (hw : S.ScalarActsBy χ w) : S.ScalarActsBy χ (z * w) := by
  intro f x
  have h1 : AdelicGL.scalar F n (z * w) * x =
      AdelicGL.scalar F n z * (AdelicGL.scalar F n w * x) := by
    rw [map_mul, mul_assoc]
  rw [h1, hz f, hw f, map_mul (centralIdeleCharacter F χ) z w, Units.val_mul, mul_assoc]

theorem scalarActsBy_inv (χ : HeckeCharacter F) {z : Ideles F} (hz : S.ScalarActsBy χ z) :
    S.ScalarActsBy χ z⁻¹ := by
  intro f x
  have hx : AdelicGL.scalar F n z * (AdelicGL.scalar F n z⁻¹ * x) = x := by
    rw [← mul_assoc, ← map_mul (AdelicGL.scalar F n) z z⁻¹, mul_inv_cancel, map_one, one_mul]
  have h := hz f (AdelicGL.scalar F n z⁻¹ * x)
  rw [hx] at h
  have hc : (centralIdeleCharacter F χ z⁻¹ : ℂ) = (centralIdeleCharacter F χ z : ℂ)⁻¹ := by
    rw [map_inv (centralIdeleCharacter F χ) z, Units.val_inv_eq_inv_val]
  rw [hc, h, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

/-- The ideles whose scalar matrices act on the functions of `S` by left multiplication
through the character `χ`. -/
def centralCharacterSubgroup (χ : HeckeCharacter F) : Subgroup (Ideles F) where
  carrier := {z | S.ScalarActsBy χ z}
  one_mem' := S.scalarActsBy_one χ
  mul_mem' := fun hz hw => S.scalarActsBy_mul χ hz hw
  inv_mem' := fun hz => S.scalarActsBy_inv χ hz

theorem mem_centralCharacterSubgroup (χ : HeckeCharacter F) (z : Ideles F) :
    z ∈ S.centralCharacterSubgroup χ ↔ ∀ (f : S.Space) (x : AdelicGL F n),
      evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
        (centralIdeleCharacter F χ z : ℂ) * evaluate F n (S.toContinuous f) x :=
  Iff.rfl

theorem isClosed_centralCharacterSubgroup (χ : HeckeCharacter F) :
    IsClosed (S.centralCharacterSubgroup χ : Set (Ideles F)) := by
  have h : (S.centralCharacterSubgroup χ : Set (Ideles F)) =
      ⋂ (f : S.Space) (x : AdelicGL F n), {z : Ideles F |
        evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
          (centralIdeleCharacter F χ z : ℂ) * evaluate F n (S.toContinuous f) x} := by
    ext z
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun f => isClosed_iInter fun x => isClosed_eq ?_ ?_
  · exact (continuous_evaluate F n _).comp ((AdelicGL.scalar F n).continuous.mul continuous_const)
  · exact (Units.continuous_val.comp (centralIdeleCharacter F χ).continuous).mul continuous_const

/-- Principal ideles act trivially, by rational invariance. -/
theorem diagonalUnits_mem_centralCharacterSubgroup (χ : HeckeCharacter F) (a : Fˣ) :
    diagonalUnits F a ∈ S.centralCharacterSubgroup χ := by
  refine (S.mem_centralCharacterSubgroup χ _).mpr fun f x => ?_
  rw [AdelicGL.scalar_diagonalUnits, evaluate_rational]
  have h1 : (centralIdeleCharacter F χ (diagonalUnits F a) : ℂ) = 1 := by
    rw [centralIdeleCharacter_principal, Units.val_one]
  rw [h1, one_mul]

theorem hasCentralCharacter_of_centralCharacterSubgroup_eq_top (χ : HeckeCharacter F)
    (h : S.centralCharacterSubgroup χ = ⊤) : S.HasCentralCharacter χ := by
  refine (S.hasCentralCharacter_iff χ).mpr fun f =>
    (mem_centralCharacterAutomorphicSubrepresentation F n χ _).mpr fun z x => ?_
  have hz : z ∈ S.centralCharacterSubgroup χ := by
    rw [h]
    exact Subgroup.mem_top z
  exact (S.mem_centralCharacterSubgroup χ z).mp hz f x

theorem evaluate_toContinuous_smul (c : ℂ) (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (c • f)) x = c * evaluate F n (S.toContinuous f) x :=
  (congrArg (fun φ => evaluate F n φ x) (S.toContinuous.map_smul c f)).trans rfl

/-- Left translation by the scalar matrix of a local idele is the local action of the local
scalar matrix. -/
theorem evaluate_scalar_finiteIdeleInclusion (v : FinitePlace F) (a : (FiniteCompletion F v)ˣ)
    (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous f) (AdelicGL.scalar F n (finiteIdeleInclusion F v a) * x) =
      evaluate F n (S.toContinuous
        (S.localRepresentation v (Matrix.GeneralLinearGroup.scalar (Fin n) a) f)) x := by
  have hx : AdelicGL.scalar F n (finiteIdeleInclusion F v a) * x =
      x * AdelicGL.ofFinite F n
        (localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a)) :=
    (AdelicGL.scalar_commute F n (finiteIdeleInclusion F v a) x).eq.trans
      (congrArg (x * ·) (AdelicGL.scalar_finiteIdeleInclusion F n v a))
  exact (congrArg (evaluate F n (S.toContinuous f)) hx).trans
    (S.evaluate_finiteRepresentation _ f x).symm

/-- A local idele lies in the central character subgroup exactly when its scalar matrix
acts on `S` by the value of the local component. -/
theorem finiteIdeleInclusion_mem_centralCharacterSubgroup_iff (χ : HeckeCharacter F)
    (v : FinitePlace F) (a : (FiniteCompletion F v)ˣ) :
    finiteIdeleInclusion F v a ∈ S.centralCharacterSubgroup χ ↔
      ∀ f : S.Space, S.localRepresentation v (Matrix.GeneralLinearGroup.scalar (Fin n) a) f =
        (χ.finiteComponent v a : ℂ) • f := by
  have hc : (centralIdeleCharacter F χ (finiteIdeleInclusion F v a) : ℂ) =
      (χ.finiteComponent v a : ℂ) := rfl
  constructor
  · intro hz f
    rw [mem_centralCharacterSubgroup] at hz
    apply S.toContinuous_injective
    apply toContinuousMap_injective F n
    ext x
    change evaluate F n (S.toContinuous
        (S.localRepresentation v (Matrix.GeneralLinearGroup.scalar (Fin n) a) f)) x =
      evaluate F n (S.toContinuous ((χ.finiteComponent v a : ℂ) • f)) x
    rw [← S.evaluate_scalar_finiteIdeleInclusion v a f x, hz f x, hc,
      S.evaluate_toContinuous_smul (χ.finiteComponent v a : ℂ) f x]
  · intro hl
    refine (S.mem_centralCharacterSubgroup χ _).mpr fun f x => ?_
    rw [hc]
    exact (S.evaluate_scalar_finiteIdeleInclusion v a f x).trans
      ((congrArg (fun g => evaluate F n (S.toContinuous g) x) (hl f)).trans
        (S.evaluate_toContinuous_smul (χ.finiteComponent v a : ℂ) f x))

/-- In an irreducible realization, a scalar matrix at one finite place acts by a scalar as
soon as it acts by that scalar on one nonzero vector. -/
theorem localScalar_eq_smul_of_ne_zero (hS : S.IsIrreducible) (v : FinitePlace F)
    (a : (FiniteCompletion F v)ˣ) (c : ℂ) {b : S.Space} (hb : b ≠ 0)
    (hab : S.localRepresentation v (Matrix.GeneralLinearGroup.scalar (Fin n) a) b = c • b)
    (f : S.Space) :
    S.localRepresentation v (Matrix.GeneralLinearGroup.scalar (Fin n) a) f = c • f := by
  let e := localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a)
  have hcomm : ∀ d : FiniteAdelicGL F n, e * d = d * e := fun d =>
    (localInclusion_scalar_commute F n v a d).eq
  let N : Submodule ℂ S.Space := Module.End.eigenspace (S.finiteRepresentation e) c
  have hd : ∀ (d : FiniteAdelicGL F n) (f : S.Space), f ∈ N → S.finiteRepresentation d f ∈ N := by
    intro d f hf
    have hf' : S.finiteRepresentation e f = c • f := Module.End.mem_eigenspace_iff.mp hf
    refine Module.End.mem_eigenspace_iff.mpr ?_
    calc S.finiteRepresentation e (S.finiteRepresentation d f)
        = S.finiteRepresentation (e * d) f := S.finiteRepresentation_mul_apply e d f
      _ = S.finiteRepresentation (d * e) f :=
          congrArg (fun y => S.finiteRepresentation y f) (hcomm d)
      _ = S.finiteRepresentation d (S.finiteRepresentation e f) :=
          (S.finiteRepresentation_mul_apply d e f).symm
      _ = S.finiteRepresentation d (c • f) := congrArg (S.finiteRepresentation d) hf'
      _ = c • S.finiteRepresentation d f := (S.finiteRepresentation d).map_smul c f
  have hk : ∀ (k : standardInfiniteCompact F n) (f : S.Space), f ∈ N →
      S.compactRepresentation k f ∈ N := by
    intro k f hf
    have hf' : S.finiteRepresentation e f = c • f := Module.End.mem_eigenspace_iff.mp hf
    refine Module.End.mem_eigenspace_iff.mpr ?_
    calc S.finiteRepresentation e (S.compactRepresentation k f)
        = S.compactRepresentation k (S.finiteRepresentation e f) :=
          S.finiteRepresentation_compactRepresentation e k f
      _ = S.compactRepresentation k (c • f) := congrArg (S.compactRepresentation k) hf'
      _ = c • S.compactRepresentation k f := (S.compactRepresentation k).map_smul c f
  have hu : ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space), f ∈ N →
      S.envelopingAction u f ∈ N := by
    intro u f hf
    have hf' : S.finiteRepresentation e f = c • f := Module.End.mem_eigenspace_iff.mp hf
    refine Module.End.mem_eigenspace_iff.mpr ?_
    calc S.finiteRepresentation e (S.envelopingAction u f)
        = S.envelopingAction u (S.finiteRepresentation e f) :=
          S.finiteRepresentation_envelopingAction e u f
      _ = S.envelopingAction u (c • f) := congrArg (S.envelopingAction u) hf'
      _ = c • S.envelopingAction u f := (S.envelopingAction u).map_smul c f
  have hbN : b ∈ N := Module.End.mem_eigenspace_iff.mpr
    ((S.localRepresentation_apply v _ b).symm.trans hab)
  have hN : N ≠ ⊥ := fun hbot => hb ((Submodule.mem_bot ℂ).mp (hbot ▸ hbN))
  have htop := S.eq_top_of_generatorStable hS N hd hk hu hN
  have hf : f ∈ N := by
    rw [htop]
    exact Submodule.mem_top
  exact (S.localRepresentation_apply v _ f).trans (Module.End.mem_eigenspace_iff.mp hf)

end OperatorRealization

end Langlands.Automorphic
