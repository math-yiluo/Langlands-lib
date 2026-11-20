import Langlands.Global.FiniteParametrizedBlockInduction
import Langlands.Global.RankinSelberg.ArchimedeanDeterminantProducts
import Langlands.Representation.Induction.LocalSectionSlices

/-! Local restriction of normalized finite adelic block sections. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Global.FiniteParametrizedBlockInduction

open CompletionPadic FiniteAdelicGL GeneralLinear Induction _root_.Representation
open scoped BigOperators NNReal

universe u uV uW

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n) (v : FinitePlace F)

/-- The insertion at one place restricts to the actual upper block parabolic. -/
def localParabolicInclusion : B.parabolic (FiniteCompletion F v) →* AdelicBlockParabolic.Finite F B where
  toFun p := ⟨localInclusion F n v p.val, by
    apply (B.mem_parabolic_iff _ _).mpr
    intro i j a b hij
    apply RestrictedProduct.ext
    intro w
    change localProjection F n w (localInclusion F n v p.val) (B.index i a) (B.index j b) = 0
    by_cases hw : w = v
    · subst w
      rw [localProjection_localInclusion]
      exact (B.mem_parabolic_iff _ _).mp p.property i j a b hij
    · rw [localProjection_localInclusion_of_ne F n v w hw]
      exact (B.mem_parabolic_iff _ _).mp (B.parabolic (FiniteCompletion F w)).one_mem i j a b hij⟩
  map_one' := Subtype.ext (map_one (localInclusion F n v))
  map_mul' p q := Subtype.ext (map_mul (localInclusion F n v) p.val q.val)

/-- Each diagonal block inserts at the same finite place. -/
def localLeviInclusion : B.Levi (FiniteCompletion F v) →* AdelicBlockParabolic.FiniteLevi F B where
  toFun m i := localInclusion F (B.size i) v (m i)
  map_one' := funext fun i => map_one (localInclusion F (B.size i) v)
  map_mul' m m' := funext fun i => map_mul (localInclusion F (B.size i) v) (m i) (m' i)

@[simp] theorem leviProjection_localParabolicInclusion (p : B.parabolic (FiniteCompletion F v)) :
    B.leviProjection (FiniteAdeles F) (localParabolicInclusion F B v p) =
      localLeviInclusion F B v (B.leviProjection (FiniteCompletion F v) p) := by
  funext i
  apply ext_localProjection F (B.size i)
  intro w
  apply Units.ext
  apply Matrix.ext
  intro a b
  change localProjection F n w (localInclusion F n v p.val) (B.index i a) (B.index i b) =
    localProjection F (B.size i) w
      (localInclusion F (B.size i) v (B.leviProjection (FiniteCompletion F v) p i)) a b
  by_cases hw : w = v
  · subst w
    rw [localProjection_localInclusion, localProjection_localInclusion, B.leviProjection_apply]
  · rw [localProjection_localInclusion_of_ne F n v w hw,
      localProjection_localInclusion_of_ne F (B.size i) v w hw]
    simp [Matrix.one_apply, (B.index i).injective.eq_iff]

private theorem determinantNorm_local (i : Fin B.length) (g : FiniteLocalGL F (B.size i) v) :
    AdelicBlockDeterminantCharacter.determinantNorm F (B.size i)
      (AdelicGL.ofFinite F (B.size i) (localInclusion F (B.size i) v g)) =
    (padicField v).canonicalTopologicalData.determinantNorm (B.size i) g := by
  apply Units.ext
  apply NNReal.eq
  rw [AdelicBlockDeterminantCharacter.coe_determinantNorm_localInclusion,
    PadicField.TopologicalData.determinantNorm_coe,
    RankinSelbergGlobal.DeterminantProducts.normalizedAbs_eq_completion_norm]

/-- The finite adelic half-modulus at the inserted parabolic equals the
positive residue-normalized local half-modulus. -/
theorem finiteHalfCharacter_local (p : B.parabolic (FiniteCompletion F v)) :
    finiteHalfCharacter F B (localParabolicInclusion F B v p) =
      (padicField v).canonicalTopologicalData.parabolicHalfModulus B p := by
  let D := (padicField v).canonicalTopologicalData
  let P := localParabolicInclusion F B v p
  change AdelicBlockDeterminantCharacter.leviHalfCharacter F B
    (B.leviProjection (Adeles F) (AdelicBlockParabolic.ofFinite F B P)) =
    D.leviHalfModulus B (B.leviProjection (FiniteCompletion F v) p)
  have he : B.leviProjection (Adeles F) (AdelicBlockParabolic.ofFinite F B P) =
      fun i => AdelicGL.ofFinite F (B.size i)
        (B.leviProjection (FiniteAdeles F) P i) := by
    change B.leviProjection (Adeles F) (AdelicBlockParabolic.pair F B 1 P) = _
    rw [AdelicBlockParabolic.leviProjection_pair, map_one]
    rfl
  apply Units.ext
  rw [AdelicBlockDeterminantCharacter.coe_leviHalfCharacter, D.leviHalfModulus_apply, he,
    AdelicBlockDeterminantCharacter.leviCharacter_apply, D.leviModulus_apply]
  simp only [D, P, leviProjection_localParabolicInclusion, localLeviInclusion,
    MonoidHom.coe_mk, OneHom.coe_mk, determinantNorm_local]

private def localParameterParabolic : B.parabolic (FiniteCompletion F v) →* parabolic F B where
  toFun p := ⟨(1, (localParabolicInclusion F B v p).val),
    ⟨(⊥ : Subgroup (standardInfiniteCompact F n)).one_mem,
      (localParabolicInclusion F B v p).property⟩⟩
  map_one' := Subtype.ext (Prod.ext rfl (congrArg Subtype.val (map_one (localParabolicInclusion F B v))))
  map_mul' p q := Subtype.ext (Prod.ext (one_mul 1).symm
    (congrArg Subtype.val (map_mul (localParabolicInclusion F B v) p q)))

private theorem exists_local_mul_away (g : Arguments F (n := n)) :
    ∃ x : FiniteLocalGL F n v, ∃ a : Arguments F (n := n),
      (∀ h : FiniteLocalGL F n v, Commute a (finiteEmbedding F (localInclusion F n v h))) ∧
      g = finiteEmbedding F (localInclusion F n v x) * a := by
  let x := localProjection F n v g.2
  let d := (localInclusion F n v x)⁻¹ * g.2
  let a : Arguments F (n := n) := (g.1, d)
  refine ⟨x, a, fun h => ?_, ?_⟩
  · change (g.1 * 1, d * localInclusion F n v h) = (1 * g.1, localInclusion F n v h * d)
    apply Prod.ext (by rw [mul_one, one_mul])
    change d * localInclusion F n v h = localInclusion F n v h * d
    apply ext_localProjection F n
    intro w
    rw [map_mul _ d (localInclusion F n v h), map_mul _ (localInclusion F n v h) d]
    by_cases hw : w = v
    · subst w
      have hd : localProjection F n v d = 1 := by
        dsimp [d]
        rw [map_mul, map_inv, localProjection_localInclusion, inv_mul_cancel]
      rw [hd, one_mul, mul_one]
    · rw [localProjection_localInclusion_of_ne F n v w hw, one_mul, mul_one]
  · exact Prod.ext (one_mul g.1).symm (mul_inv_cancel_left (localInclusion F n v x) g.2).symm

variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (FiniteAdelicGL F (B.size i)) (V i))
  (τ : ∀ i, Representation ℂ (FiniteLocalGL F (B.size i) v) (W i))

local instance : AddCommGroup (EquivariantFunctions (parabolic F B) (coefficient F B σ)) :=
  Submodule.addCommGroup _

local instance : AddCommGroup (Sections F B σ) := Submodule.addCommGroup _

/-- The actual Levi coefficient separation gives separating local slices of
the normalized finite adelic induced representation. -/
theorem hasSeparatingIntertwiners_restriction
    (hsep : HasSeparatingIntertwiners ((B.blockTensor σ).comp (localLeviInclusion F B v))
      (B.blockTensor τ)) :
    letI : TopologicalSpace (FiniteLocalGL F n v) := (padicField v).canonicalGeneralLinearTopology n
    HasSeparatingIntertwiners (V := Sections F B σ)
      ((induced F B σ).comp (localPadicInclusion F v n).toMonoidHom)
      ((padicField v).canonicalNormalizedProductInduced B τ) := by
  let D := (padicField v).canonicalTopologicalData
  let pLoc := localParameterParabolic F B v
  let σL := twist (D.parabolicHalfModulus B)
    ((B.blockTensor τ).comp (B.leviProjection (FiniteCompletion F v)))
  have hsepP : HasSeparatingIntertwiners ((coefficient F B σ).comp pLoc) σL := by
    intro x hx
    refine hsep x fun q => ?_
    let qP : IntertwiningMap ((coefficient F B σ).comp pLoc) σL :=
      { toLinearMap := q.toLinearMap
        isIntertwining' p := by
          apply LinearMap.ext
          intro y
          change q ((finiteHalfCharacter F B (localParabolicInclusion F B v p) : ℂ) •
              B.blockTensor σ
                (B.leviProjection (FiniteAdeles F) (localParabolicInclusion F B v p)) y) =
            (D.parabolicHalfModulus B p : ℂ) •
              B.blockTensor τ (B.leviProjection (FiniteCompletion F v) p) (q y)
          rw [leviProjection_localParabolicInclusion, finiteHalfCharacter_local, map_smul]
          exact congrArg ((D.parabolicHalfModulus B p : ℂ) • ·)
            (IntertwiningMap.isIntertwining ((B.blockTensor σ).comp (localLeviInclusion F B v))
              (B.blockTensor τ) q (B.leviProjection (FiniteCompletion F v) p) y) }
    exact hx qP
  let : TopologicalSpace (FiniteLocalGL F n v) := (padicField v).canonicalGeneralLinearTopology n
  let : IsTopologicalGroup (FiniteLocalGL F n v) := (padicField v).canonicalGeneralLinearTopologicalGroup n
  exact Induction.hasSeparatingIntertwiners_localSlices (finiteEmbedding F)
    (localPadicInclusion F v n) pLoc (fun _ => rfl) (exists_local_mul_away F v) hsepP

end Langlands.Global.FiniteParametrizedBlockInduction
