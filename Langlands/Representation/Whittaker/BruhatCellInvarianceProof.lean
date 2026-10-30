import Langlands.Representation.Whittaker.BruhatCellInvarianceStatement
import Langlands.Representation.Whittaker.BruhatCellFactorizationProof
import Langlands.Representation.Whittaker.BruhatHaarMeasureProof
import Langlands.Representation.Whittaker.CompatibleMonomialFixedProof

/-!
# Proof of transpose invariance on compatible Bruhat cells

Proves `Langlands.Whittaker.BruhatCellInvarianceStatement`. A compatible torus point gives
a monomial representative of the cell fixed by the Weyl-conjugated transpose, which proves
stability of the whole cell. The product exchange of the two unipotent variables preserves
the inverse-weight character average, and on fixed monomial slices it commutes with the
fiber average because the stabilizer anti-involution preserves Haar measure. A
zero-preserving orbital lift transfers the compatible support of the published
factorization to cell support, and finite linearity with orbital surjectivity gives
invariance. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis MeasureTheory

universe uK uF

namespace BruhatCellInvariance

section Generic

variable (n : ℕ) (K : Type uK) [Field K] [TopologicalSpace K]
  [IsTopologicalRing K]

/-- The product involution exchanges the two unipotent coordinates and
applies the actual Weyl-conjugated transpose to each. -/
def productTranspose :
    (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K) ≃ₜ
      (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K) where
  toFun m := (weylTransposeUnipotent n K m.2.2, m.2.1, weylTransposeUnipotent n K m.1)
  invFun m := (weylTransposeUnipotent n K m.2.2, m.2.1, weylTransposeUnipotent n K m.1)
  left_inv m := by simp
  right_inv m := by simp
  continuous_toFun :=
    ((weylTransposeUnipotent n K).continuous.comp (continuous_snd.comp continuous_snd)).prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        ((weylTransposeUnipotent n K).continuous.comp continuous_fst))
  continuous_invFun :=
    ((weylTransposeUnipotent n K).continuous.comp (continuous_snd.comp continuous_snd)).prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        ((weylTransposeUnipotent n K).continuous.comp continuous_fst))

@[simp]
theorem transpose_inv (g : GeneralLinear (n + 1) K) :
    weylTransposeHomeomorph n K g⁻¹ = (weylTransposeHomeomorph n K g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← weylTransposeHomeomorph_mul, mul_inv_cancel]
  simp [weylTransposeHomeomorph_apply]

variable {n K}

/-- Swapping the unipotent variables preserves their character average.
The measure premise is precisely the published unipotent Haar symmetry. -/
theorem characterAverage_productTranspose
    (ψ : UnitaryAdditiveCharacter K)
    (μ : letI := borel (upperUnipotent (n + 1) K); Measure (upperUnipotent (n + 1) K))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (hμ : letI := borel (upperUnipotent (n + 1) K);
      Measure.map (weylTransposeUnipotent n K) μ = μ)
    (α : SchwartzBruhat
      (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K)) :
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ
        (Hecke.TestFunction.pullback (productTranspose n K) α) =
      SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ α := by
  let := borel (upperUnipotent (n + 1) K)
  have : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let e := (weylTransposeUnipotent n K).toMeasurableEquiv
  let E := (MeasurableEquiv.prodComm :
    upperUnipotent (n + 1) K × upperUnipotent (n + 1) K ≃ᵐ
      upperUnipotent (n + 1) K × upperUnipotent (n + 1) K).trans (e.prodCongr e)
  have he : MeasurePreserving e μ μ := ⟨e.measurable, hμ⟩
  have hE : MeasurePreserving E (μ.prod μ) (μ.prod μ) :=
    (he.prod he).comp Measure.measurePreserving_swap
  ext d
  rw [SchwartzBruhat.characterAverage_apply, SchwartzBruhat.characterAverage_apply,
    ← hE.integral_comp' (fun z => α (z.1, (d, z.2)) *
      ((standardCharacterContinuous ψ n z.1 : ℂ) *
        (standardCharacterContinuous ψ n z.2 : ℂ))⁻¹)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change α (weylTransposeUnipotent n K z.2, d, weylTransposeUnipotent n K z.1) *
      ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ =
    α (weylTransposeUnipotent n K z.2, d, weylTransposeUnipotent n K z.1) *
      ((standardCharacter ψ n (weylTransposeUnipotent n K z.2) : ℂ) *
        (standardCharacter ψ n (weylTransposeUnipotent n K z.1) : ℂ))⁻¹
  rw [standardCharacter_weylTranspose, standardCharacter_weylTranspose,
    mul_comm (standardCharacter ψ n z.2 : ℂ) (standardCharacter ψ n z.1 : ℂ)]

variable (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Kˣ)

/-- For a transpose-fixed monomial representative, transpose followed by
conjugation back preserves its actual stabilizer subgroup. -/
theorem fiberTranspose_mem
    (hs : weylTransposeHomeomorph n K
      (permutation (n + 1) K w * Iwasawa.diagonalUnits d) =
        permutation (n + 1) K w * Iwasawa.diagonalUnits d)
    (u : permutationUnipotentPlus (n + 1) K w) :
    (permutation (n + 1) K w * Iwasawa.diagonalUnits d)⁻¹ *
        weylTransposeHomeomorph n K u.val *
          (permutation (n + 1) K w * Iwasawa.diagonalUnits d) ∈
      permutationUnipotentPlus (n + 1) K w := by
  let s := permutation (n + 1) K w * Iwasawa.diagonalUnits d
  have hs' : weylTransposeHomeomorph n K s = s := hs
  have hsu : s * u.val * s⁻¹ ∈ upperUnipotent (n + 1) K :=
    monomial_conj_mem_upperUnipotent w d u.property.2
  have htu := weylTransposeHomeomorph_mem_upperUnipotent n K u.property.1
  have hA : s⁻¹ * weylTransposeHomeomorph n K u.val * s ∈ upperUnipotent (n + 1) K := by
    have h := weylTransposeHomeomorph_mem_upperUnipotent n K hsu
    simpa only [weylTransposeHomeomorph_mul, transpose_inv, hs', mul_assoc] using h
  refine ⟨hA, permutation_conj_mem_upperUnipotent_of_monomial w d ?_⟩
  change s * (s⁻¹ * weylTransposeHomeomorph n K u.val * s) * s⁻¹ ∈ _
  convert htu using 1
  group

/-- The stabilizer anti-involution at a transpose-fixed monomial matrix. -/
def fiberTranspose
    (hs : weylTransposeHomeomorph n K
      (permutation (n + 1) K w * Iwasawa.diagonalUnits d) =
        permutation (n + 1) K w * Iwasawa.diagonalUnits d) :
    permutationUnipotentPlus (n + 1) K w ≃ₜ permutationUnipotentPlus (n + 1) K w where
  toFun u := ⟨(permutation (n + 1) K w * Iwasawa.diagonalUnits d)⁻¹ *
    weylTransposeHomeomorph n K u.val *
      (permutation (n + 1) K w * Iwasawa.diagonalUnits d), fiberTranspose_mem w d hs u⟩
  invFun u := ⟨(permutation (n + 1) K w * Iwasawa.diagonalUnits d)⁻¹ *
    weylTransposeHomeomorph n K u.val *
      (permutation (n + 1) K w * Iwasawa.diagonalUnits d), fiberTranspose_mem w d hs u⟩
  left_inv u := by
    apply Subtype.ext
    let s := permutation (n + 1) K w * Iwasawa.diagonalUnits d
    have hs' : weylTransposeHomeomorph n K s = s := hs
    change s⁻¹ * weylTransposeHomeomorph n K
      (s⁻¹ * weylTransposeHomeomorph n K u.val * s) * s = u.val
    rw [weylTransposeHomeomorph_mul n K (s⁻¹ * weylTransposeHomeomorph n K u.val) s,
      hs', weylTransposeHomeomorph_mul n K s⁻¹ (weylTransposeHomeomorph n K u.val),
      transpose_inv, hs', weylTransposeHomeomorph_involutive]
    group
  right_inv u := by
    apply Subtype.ext
    let s := permutation (n + 1) K w * Iwasawa.diagonalUnits d
    have hs' : weylTransposeHomeomorph n K s = s := hs
    change s⁻¹ * weylTransposeHomeomorph n K
      (s⁻¹ * weylTransposeHomeomorph n K u.val * s) * s = u.val
    rw [weylTransposeHomeomorph_mul n K (s⁻¹ * weylTransposeHomeomorph n K u.val) s,
      hs', weylTransposeHomeomorph_mul n K s⁻¹ (weylTransposeHomeomorph n K u.val),
      transpose_inv, hs', weylTransposeHomeomorph_involutive]
    group
  continuous_toFun :=
    ((continuous_const.mul ((weylTransposeHomeomorph n K).continuous.comp
      continuous_subtype_val)).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul ((weylTransposeHomeomorph n K).continuous.comp
      continuous_subtype_val)).mul continuous_const).subtype_mk _

/-- The stabilizer involution reverses multiplication. -/
theorem fiberTranspose_mul
    (hs : weylTransposeHomeomorph n K
      (permutation (n + 1) K w * Iwasawa.diagonalUnits d) =
        permutation (n + 1) K w * Iwasawa.diagonalUnits d)
    (u v : permutationUnipotentPlus (n + 1) K w) :
    fiberTranspose w d hs (u * v) = fiberTranspose w d hs v * fiberTranspose w d hs u := by
  apply Subtype.ext
  change (permutation (n + 1) K w * Iwasawa.diagonalUnits d)⁻¹ *
      weylTransposeHomeomorph n K (u.val * v.val) *
        (permutation (n + 1) K w * Iwasawa.diagonalUnits d) =
    ((permutation (n + 1) K w * Iwasawa.diagonalUnits d)⁻¹ *
      weylTransposeHomeomorph n K v.val *
        (permutation (n + 1) K w * Iwasawa.diagonalUnits d)) *
    ((permutation (n + 1) K w * Iwasawa.diagonalUnits d)⁻¹ *
      weylTransposeHomeomorph n K u.val *
        (permutation (n + 1) K w * Iwasawa.diagonalUnits d))
  rw [weylTransposeHomeomorph_mul]
  group

/-- The product exchange carries a fiber orbit to the orbit obtained by
the inverse of the stabilizer anti-involution. -/
theorem productTranspose_bruhatFiberAct
    (m : upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) ×
      upperUnipotent (n + 1) K)
    (hs : weylTransposeHomeomorph n K
      (permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1) =
        permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1)
    (u : permutationUnipotentPlus (n + 1) K w) :
    productTranspose n K (bruhatFiberAct (n + 1) K w u m) =
      bruhatFiberAct (n + 1) K w (fiberTranspose w m.2.1 hs u)⁻¹
        (productTranspose n K m) := by
  let s := permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1
  have hs' : weylTransposeHomeomorph n K s = s := hs
  refine Prod.ext (Subtype.ext ?_) (Prod.ext rfl (Subtype.ext ?_))
  · change weylTransposeHomeomorph n K (u.val * m.2.2.val) =
      weylTransposeHomeomorph n K m.2.2.val * permutation (n + 1) K w *
        Iwasawa.diagonalUnits m.2.1 *
          ((s⁻¹ * weylTransposeHomeomorph n K u.val * s)⁻¹)⁻¹ *
        (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation (n + 1) K w)⁻¹
    rw [weylTransposeHomeomorph_mul, inv_inv]
    dsimp [s]
    group
  · change weylTransposeHomeomorph n K
      (m.1.val * permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ *
        (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation (n + 1) K w)⁻¹) =
      (s⁻¹ * weylTransposeHomeomorph n K u.val * s)⁻¹ *
        weylTransposeHomeomorph n K m.1.val
    have he :
        m.1.val * permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ *
          (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation (n + 1) K w)⁻¹ =
        m.1.val * s * u.val⁻¹ * s⁻¹ := by
      dsimp [s]
      group
    rw [he, weylTransposeHomeomorph_mul n K (m.1.val * s * u.val⁻¹) s⁻¹,
      transpose_inv, hs', weylTransposeHomeomorph_mul n K (m.1.val * s) u.val⁻¹,
      transpose_inv, weylTransposeHomeomorph_mul n K m.1.val s, hs']
    group

/-- Haar normalization of the stabilizer anti-involution and the inverse
substitution used for the fiber integral. -/
theorem fiberTranspose_measurePreserving
    [MeasurableSpace (permutationUnipotentPlus (n + 1) K w)]
    [BorelSpace (permutationUnipotentPlus (n + 1) K w)]
    [LocallyCompactSpace (permutationUnipotentPlus (n + 1) K w)]
    [SecondCountableTopology (permutationUnipotentPlus (n + 1) K w)]
    (hs : weylTransposeHomeomorph n K
      (permutation (n + 1) K w * Iwasawa.diagonalUnits d) =
        permutation (n + 1) K w * Iwasawa.diagonalUnits d)
    (ν : Measure (permutationUnipotentPlus (n + 1) K w))
    [ν.IsHaarMeasure] [ν.IsMulRightInvariant] :
    MeasurePreserving (fiberTranspose w d hs) ν ν ∧
      MeasurePreserving
        ((fiberTranspose w d hs).trans
          (Homeomorph.inv (permutationUnipotentPlus (n + 1) K w))) ν ν := by
  have hA : MeasurePreserving (fiberTranspose w d hs) ν ν :=
    ⟨(fiberTranspose w d hs).continuous.measurable,
      map_eq_self_of_antiInvolution (fiberTranspose w d hs)
        (fiberTranspose_mul w d hs) (fiberTranspose w d hs).left_inv ν⟩
  have hinv : MeasurePreserving
      (Homeomorph.inv (permutationUnipotentPlus (n + 1) K w)) ν ν :=
    ⟨continuous_inv.measurable,
      map_eq_self_of_antiInvolution
        (Homeomorph.inv (permutationUnipotentPlus (n + 1) K w))
        (fun _ _ => mul_inv_rev _ _) inv_inv ν⟩
  exact ⟨hA, hinv.comp hA⟩

/-- Fiber averaging commutes with product exchange on a fixed monomial
slice, with its scalar normalization proved by Haar transport. -/
theorem bruhatFiberAverage_productTranspose
    [T2Space K]
    [LocallyCompactSpace (permutationUnipotentPlus (n + 1) K w)]
    [SecondCountableTopology (permutationUnipotentPlus (n + 1) K w)] :
    letI := borel (permutationUnipotentPlus (n + 1) K w)
    ∀ (ν : Measure (permutationUnipotentPlus (n + 1) K w))
      [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
      (α : SchwartzBruhat
        (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K))
      (m : upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) ×
        upperUnipotent (n + 1) K)
      (_hs : weylTransposeHomeomorph n K
        (permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1) =
          permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1),
      bruhatFiberAverage (n + 1) K w ν
          (Hecke.TestFunction.pullback (productTranspose n K) α) m =
        bruhatFiberAverage (n + 1) K w ν α (productTranspose n K m) := by
  let := borel (permutationUnipotentPlus (n + 1) K w)
  have : BorelSpace (permutationUnipotentPlus (n + 1) K w) := ⟨rfl⟩
  intro ν _ _ α m hs
  have hT := (fiberTranspose_measurePreserving w m.2.1 hs ν).2
  rw [bruhatFiberAverage_apply, bruhatFiberAverage_apply]
  calc
    (∫ u, Hecke.TestFunction.pullback (productTranspose n K) α
        (bruhatFiberAct (n + 1) K w u m) ∂ν) =
      ∫ u, α (bruhatFiberAct (n + 1) K w (fiberTranspose w m.2.1 hs u)⁻¹
        (productTranspose n K m)) ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      exact congrArg α (productTranspose_bruhatFiberAct w m hs u)
    _ = ∫ u, α (bruhatFiberAct (n + 1) K w u (productTranspose n K m)) ∂ν :=
      hT.integral_comp
        (((fiberTranspose w m.2.1 hs).trans
          (Homeomorph.inv (permutationUnipotentPlus (n + 1) K w))).toMeasurableEquiv.measurableEmbedding)
        (fun u => α (bruhatFiberAct (n + 1) K w u (productTranspose n K m)))

/-- The multiplication map intertwines the two actual transposes on a
monomial slice fixed by transpose. -/
theorem upperBruhatTorusMap_productTranspose
    (m : upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) ×
      upperUnipotent (n + 1) K)
    (hs : weylTransposeHomeomorph n K
      (permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1) =
        permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1) :
    (upperBruhatTorusMap (n + 1) w (productTranspose n K m)).val =
      weylTransposeHomeomorph n K (upperBruhatTorusMap (n + 1) w m).val := by
  let s := permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1
  have hs' : weylTransposeHomeomorph n K s = s := hs
  change weylTransposeHomeomorph n K m.2.2.val * permutation (n + 1) K w *
      Iwasawa.diagonalUnits m.2.1 * weylTransposeHomeomorph n K m.1.val =
    weylTransposeHomeomorph n K
      (m.1.val * permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1 * m.2.2.val)
  have he : m.1.val * permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1 *
      m.2.2.val = m.1.val * s * m.2.2.val := by simp only [s, mul_assoc]
  rw [he, weylTransposeHomeomorph_mul n K (m.1.val * s) m.2.2.val,
    weylTransposeHomeomorph_mul n K m.1.val s, hs']
  simp only [s, mul_assoc]

/-- The actual transpose preserves upper-triangular matrices. -/
theorem transpose_mem_upperTriangular {b : GeneralLinear (n + 1) K}
    (hb : b ∈ upperTriangularSubgroup (n + 1) K) :
    weylTransposeHomeomorph n K b ∈ upperTriangularSubgroup (n + 1) K := by
  rw [mem_upperTriangularSubgroup_iff] at hb ⊢
  intro i j hji
  rw [weylTransposeHomeomorph_entry]
  exact hb j.rev i.rev (Fin.rev_lt_rev.mpr hji)

/-- A single transpose-fixed monomial representative implies stability of
its entire upper Bruhat cell. No stability is assumed for arbitrary cells. -/
theorem cell_stable_of_fixed_monomial
    (hs : weylTransposeHomeomorph n K
      (permutation (n + 1) K w * Iwasawa.diagonalUnits d) =
        permutation (n + 1) K w * Iwasawa.diagonalUnits d) :
    Set.MapsTo (weylTransposeHomeomorph n K)
      (upperBruhatCell (n + 1) K w) (upperBruhatCell (n + 1) K w) := by
  have hdiag := diagonalUnits_mem_upperTriangular (n + 1) d
  have ht := transpose_mem_upperTriangular hdiag
  have hperm : weylTransposeHomeomorph n K (permutation (n + 1) K w) =
      (weylTransposeHomeomorph n K (Iwasawa.diagonalUnits d))⁻¹ *
        permutation (n + 1) K w * Iwasawa.diagonalUnits d := by
    rw [weylTransposeHomeomorph_mul] at hs
    calc
      _ = (weylTransposeHomeomorph n K (Iwasawa.diagonalUnits d))⁻¹ *
          (weylTransposeHomeomorph n K (Iwasawa.diagonalUnits d) *
            weylTransposeHomeomorph n K (permutation (n + 1) K w)) := by group
      _ = _ := by rw [hs, mul_assoc]
  rintro g ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  refine ⟨weylTransposeHomeomorph n K b₂ *
      (weylTransposeHomeomorph n K (Iwasawa.diagonalUnits d))⁻¹,
    mul_mem (transpose_mem_upperTriangular hb₂) (inv_mem ht),
    Iwasawa.diagonalUnits d * weylTransposeHomeomorph n K b₁,
    mul_mem hdiag (transpose_mem_upperTriangular hb₁), ?_⟩
  rw [weylTransposeHomeomorph_mul n K (b₁ * permutation (n + 1) K w) b₂,
    weylTransposeHomeomorph_mul n K b₁ (permutation (n + 1) K w), hperm]
  simp only [mul_assoc]

end Generic

section Lift

variable {r : ℕ} {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] {w : Equiv.Perm (Fin r)}
  {eT : (upperUnipotent r K × (Fin r → Kˣ) × permutationUnipotentMinus r K w) ≃ₜ
    UpperBruhatCell r K w}
  {e : (permutationUnipotentPlus r K w × permutationUnipotentMinus r K w) ≃ₜ
    upperUnipotent r K}
  (heT : ∀ x, (eT x).val =
    x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
  (he : ∀ x, (e x).val = x.1.val * x.2.val)

include heT he

omit [IsTopologicalRing K] [T2Space K] in
/-- The middle coordinate of the actual multiplication map is its unique
torus parameter, as obtained from the published cell coordinates. -/
theorem middleCoordinate_upperBruhatTorusMap
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    (eT.symm (upperBruhatTorusMap r w m)).2.1 = m.2.1 := by
  exact congrArg (fun z => z.2.1) (bruhatFiberAct_plusCoordinate_cellSection heT he m)

/-- The normalized orbital lift also vanishes wherever the original test
function vanishes after multiplication. This strengthens the published
orbital-surjectivity construction of Worker 1011. -/
theorem exists_orbitalLift_preserving_zeros
    {K₀ : Set (permutationUnipotentPlus r K w)}
    (hK₀c : IsCompact K₀) (hK₀o : IsOpen K₀) (hK₀ : K₀.Nonempty) :
    letI := borel (permutationUnipotentPlus r K w)
    ∀ (ν : Measure (permutationUnipotentPlus r K w)) [ν.IsHaarMeasure]
      (I : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) →ₗ[ℂ]
        SchwartzBruhat (UpperBruhatCell r K w)),
      (∀ α m, I α (upperBruhatTorusMap r w m) =
        bruhatFiberAverage r K w ν α m) →
      ∀ f : SchwartzBruhat (UpperBruhatCell r K w),
        ∃ α : SchwartzBruhat
            (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K),
          I α = f ∧ ∀ m, f (upperBruhatTorusMap r w m) = 0 → α m = 0 := by
  let := borel (permutationUnipotentPlus r K w)
  have : BorelSpace (permutationUnipotentPlus r K w) := ⟨rfl⟩
  intro ν _ I hI f
  have hreal : ν.real K₀ ≠ 0 :=
    (measureReal_ne_zero_iff hK₀c.measure_ne_top).2 (hK₀o.measure_ne_zero ν hK₀)
  let φ : permutationUnipotentPlus r K w → ℂ :=
    K₀.indicator fun _ => (ν.real K₀ : ℂ)⁻¹
  let g : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K → ℂ :=
    fun m => f (upperBruhatTorusMap r w m) * φ (plusCoordinate e m)
  have hg_lc : IsLocallyConstant g :=
    (f.locallyConstant.comp_continuous (continuous_upperBruhatTorusMap r w)).mul
      ((isLocallyConstant_indicator_const ⟨hK₀c.isClosed, hK₀o⟩ _).comp_continuous
        continuous_plusCoordinate)
  have hg_cs : HasCompactSupport g := by
    refine HasCompactSupport.intro ((f.hasCompactSupport.isCompact.prod hK₀c).image
      (continuous_bruhatFiberAct_cellSection (eT := eT))) fun m hm => ?_
    by_contra h
    apply hm
    refine ⟨(upperBruhatTorusMap r w m, plusCoordinate e m), ⟨?_, ?_⟩,
      bruhatFiberAct_plusCoordinate_cellSection heT he m⟩
    · exact subset_tsupport _ (left_ne_zero_of_mul h)
    · by_contra hq
      exact h (by simp only [g, φ, Set.indicator_of_notMem hq, mul_zero])
  refine ⟨⟨g, hg_lc, hg_cs⟩, ?_, fun m hm => ?_⟩
  · ext c
    have hIc := hI ⟨g, hg_lc, hg_cs⟩ (cellSection eT c)
    rw [upperBruhatTorusMap_cellSection heT c] at hIc
    rw [hIc, bruhatFiberAverage_apply]
    have hint : ∀ u : permutationUnipotentPlus r K w,
        g (bruhatFiberAct r K w u (cellSection eT c)) = f c * φ u := fun u => by
      simp only [g, upperBruhatTorusMap_bruhatFiberAct, upperBruhatTorusMap_cellSection heT,
        plusCoordinate_bruhatFiberAct_cellSection he]
    change (∫ u, g (bruhatFiberAct r K w u (cellSection eT c)) ∂ν) = f c
    simp only [hint]
    rw [integral_const_mul, integral_indicator_const _ hK₀o.measurableSet, Complex.real_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hreal), mul_one]
  · change f (upperBruhatTorusMap r w m) * φ (plusCoordinate e m) = 0
    rw [hm, zero_mul]

/-- Factorization over a supported torus distribution gives support on the
corresponding cell points. The zero-preserving lift permits this deduction
for the full algebraic dual. -/
theorem supportedOn_middle_of_factorization
    {K₀ : Set (permutationUnipotentPlus r K w)}
    (hK₀c : IsCompact K₀) (hK₀o : IsOpen K₀) (hK₀ : K₀.Nonempty)
    (χ : ContinuousMonoidHom (upperUnipotent r K) ℂˣ) :
    letI := borel (upperUnipotent r K)
    letI : BorelSpace (upperUnipotent r K) := ⟨rfl⟩
    letI := borel (permutationUnipotentPlus r K w)
    ∀ (μ : Measure (upperUnipotent r K)) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
      (ν : Measure (permutationUnipotentPlus r K w)) [ν.IsHaarMeasure]
      (I : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) →ₗ[ℂ]
        SchwartzBruhat (UpperBruhatCell r K w)),
      (∀ α m, I α (upperBruhatTorusMap r w m) =
        bruhatFiberAverage r K w ν α m) →
      ∀ (D : Distribution (UpperBruhatCell r K w))
        (τ : Distribution (Fin r → Kˣ)) (S : Set (Fin r → Kˣ)),
        τ ∈ Distribution.supportedOn S →
        Distribution.characterAverageDual χ μ τ = D.comp I →
        D ∈ Distribution.supportedOn {c | (eT.symm c).2.1 ∈ S} := by
  let := borel (upperUnipotent r K)
  have : BorelSpace (upperUnipotent r K) := ⟨rfl⟩
  let := borel (permutationUnipotentPlus r K w)
  intro μ _ _ ν _ I hI D τ S hτ hfac
  apply (Distribution.mem_supportedOn_iff _ _).mpr
  intro f hf
  obtain ⟨α, hα, hzero⟩ :=
    exists_orbitalLift_preserving_zeros heT he hK₀c hK₀o hK₀ ν I hI f
  have hav : τ (SchwartzBruhat.characterAverage χ μ α) = 0 := by
    apply (Distribution.mem_supportedOn_iff _ _).mp hτ
    intro d hd
    rw [SchwartzBruhat.characterAverage_apply]
    apply integral_eq_zero_of_ae
    refine Filter.Eventually.of_forall fun z => ?_
    have hz : α (z.1, d, z.2) = 0 := by
      apply hzero
      apply hf
      change (eT.symm (upperBruhatTorusMap r w (z.1, d, z.2))).2.1 ∈ S
      rw [middleCoordinate_upperBruhatTorusMap heT he]
      exact hd
    change α (z.1, d, z.2) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ = 0
    rw [hz, zero_mul]
  calc
    D f = D (I α) := congrArg D hα.symm
    _ = τ (SchwartzBruhat.characterAverage χ μ α) :=
      (congrArg (fun E => E α) hfac).symm
    _ = 0 := hav

end Lift

end BruhatCellInvariance

open BruhatCellInvariance in
/-- Every factorization theorem of the published form gives cell stability and transpose
invariance on cells with nonempty compatible torus. All measure and coordinate data are
constructed from the published p-adic results. -/
theorem bruhatCellInvariance_of_factorization
    (hfac : BruhatCellFactorizationStatement.{uF}) :
    BruhatCellInvarianceStatement.{uF} := by
  intro p hp F
  let := F.canonicalNormedField
  intro n ψ w hnon
  have hfixed (d : Fin (n + 1) → F.Carrierˣ) (hd : d ∈ compatibleTorus ψ n w) :
      weylTransposeHomeomorph n F.Carrier
          (permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d) =
        permutation (n + 1) F.Carrier w * Iwasawa.diagonalUnits d :=
    compatibleMonomialFixed p hp F n ψ w d hd
  obtain ⟨d₀, hd₀⟩ := hnon
  let hτ := cell_stable_of_fixed_monomial w d₀ (hfixed d₀ hd₀)
  refine ⟨hτ, ?_⟩
  intro D hD
  let U := upperUnipotent (n + 1) F.Carrier
  let P := permutationUnipotentPlus (n + 1) F.Carrier w
  let H := Fin (n + 1) → F.Carrierˣ
  let M := U × (H × U)
  let C := UpperBruhatCell (n + 1) F.Carrier w
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  let := borel P
  have : BorelSpace P := ⟨rfl⟩
  have : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  have : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
  have : LocallyCompactSpace P :=
    (isClosed_permutationUnipotentPlus (n + 1) F.Carrier w).locallyCompactSpace
  have : SecondCountableTopology P := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨μ, hμ⟩ := (bruhatHaarMeasure p hp F n).1
  have := hμ
  obtain ⟨hσ, hr, htranspose⟩ := (bruhatHaarMeasure p hp F n).2.1 μ
  have := hσ
  have := hr
  obtain ⟨ν, hν⟩ := ((bruhatHaarMeasure p hp F n).2.2 w).1
  have := hν
  have := (((bruhatHaarMeasure p hp F n).2.2 w).2 ν).2
  obtain ⟨I, ⟨hI, hsurj, -⟩, -⟩ := bruhatOrbitalIntegration p hp F n w ν
  obtain ⟨τ, ⟨hsupp, hτfac⟩, -⟩ := hfac p hp F n ψ w μ ν I hI D hD
  obtain ⟨-, eT, heT⟩ := upperBruhatCoordinates F.Carrier (n + 1) w
  obtain ⟨e, he⟩ := upperUnipotentFactorization F.Carrier (n + 1) w
  obtain ⟨L, hLc, -⟩ := F.canonicalGeneralLinearCompactOpen (n + 1) Set.univ Filter.univ_mem
  let K₀ : Set P := Subtype.val ⁻¹' (L : Set (GeneralLinear (n + 1) F.Carrier))
  have hK₀c : IsCompact K₀ :=
    (isClosed_permutationUnipotentPlus (n + 1) F.Carrier w).isClosedEmbedding_subtypeVal.isCompact_preimage
      hLc
  have hK₀o : IsOpen K₀ := L.isOpen.preimage continuous_subtype_val
  have hK₀ : K₀.Nonempty := ⟨1, L.one_mem⟩
  have hDsupp : D ∈ Distribution.supportedOn
      {c | (eT.symm c).2.1 ∈ compatibleTorus ψ n w} :=
    supportedOn_middle_of_factorization heT he hK₀c hK₀o hK₀
      (standardCharacterContinuous ψ n) μ ν I hI D τ _ hsupp hτfac
  have hfac_eval (β : SchwartzBruhat M) :
      D (I β) = τ (SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ β) :=
    (congrArg (fun E => E β) hτfac).symm
  apply (isWeylTransposeInvariantBruhatCellDistribution_iff n F.Carrier w hτ D).mpr
  intro f
  obtain ⟨α, rfl⟩ := hsurj f
  have hDexchange :
      D (I (Hecke.TestFunction.pullback (productTranspose n F.Carrier) α)) = D (I α) := by
    rw [hfac_eval, hfac_eval, characterAverage_productTranspose ψ μ htranspose]
  have hdiff : D
      (Hecke.TestFunction.pullback (bruhatCellWeylTranspose n F.Carrier w hτ) (I α) -
        I (Hecke.TestFunction.pullback (productTranspose n F.Carrier) α)) = 0 := by
    apply (Distribution.mem_supportedOn_iff _ _).mp hDsupp
    intro c hc
    let m : M := cellSection eT c
    have hm : upperBruhatTorusMap (n + 1) w m = c :=
      upperBruhatTorusMap_cellSection heT c
    have hmd : m.2.1 ∈ compatibleTorus ψ n w := hc
    have hπσ : upperBruhatTorusMap (n + 1) w (productTranspose n F.Carrier m) =
        bruhatCellWeylTranspose n F.Carrier w hτ c := by
      apply Subtype.ext
      rw [upperBruhatTorusMap_productTranspose w m (hfixed _ hmd)]
      exact congrArg (fun z : C => weylTransposeHomeomorph n F.Carrier z.val) hm
    have hpoint :
        I (Hecke.TestFunction.pullback (productTranspose n F.Carrier) α) c =
          I α (bruhatCellWeylTranspose n F.Carrier w hτ c) := by
      calc
        _ = I (Hecke.TestFunction.pullback (productTranspose n F.Carrier) α)
            (upperBruhatTorusMap (n + 1) w m) := by rw [hm]
        _ = bruhatFiberAverage (n + 1) F.Carrier w ν
            (Hecke.TestFunction.pullback (productTranspose n F.Carrier) α) m := hI _ _
        _ = bruhatFiberAverage (n + 1) F.Carrier w ν α
            (productTranspose n F.Carrier m) :=
          bruhatFiberAverage_productTranspose w ν α m (hfixed _ hmd)
        _ = I α (upperBruhatTorusMap (n + 1) w (productTranspose n F.Carrier m)) :=
          (hI _ _).symm
        _ = _ := congrArg (I α) hπσ
    change I α (bruhatCellWeylTranspose n F.Carrier w hτ c) -
      I (Hecke.TestFunction.pullback (productTranspose n F.Carrier) α) c = 0
    rw [hpoint, sub_self]
  rw [map_sub] at hdiff
  exact (sub_eq_zero.mp hdiff).trans hDexchange

/-- Transpose invariance of positively bi-equivariant distributions on Bruhat cells with
nonempty compatible torus, using the published factorization theorem. -/
theorem bruhatCellInvariance : BruhatCellInvarianceStatement.{uF} :=
  bruhatCellInvariance_of_factorization bruhatCellFactorization

end Langlands.Whittaker
