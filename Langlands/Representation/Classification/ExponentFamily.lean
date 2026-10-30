import Langlands.Topology.CompactNormCharacter
import Langlands.Representation.Induction.CovariantRescaling
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.NormalizedIntegralForm
import Langlands.Representation.Classification.LanglandsData

/-!
# Real exponent families of normalized products on one space

For a standard block shape `B` of `GL_n(F)` and real exponents `u`, the
character `q ↦ ∏ i |det m_i(q)| ^ u_i` of the standard parabolic is trivial on
`P ∩ K` for every compact subgroup `K`. Given `G = P K` with `K` compact open,
it is therefore the modulus of an Iwasawa height, and the resulting family on
the untwisted normalized induced space is, at the parameter `s`, equivalent to
the actual normalized product `i(ν^(s u_1) A_1, …, ν^(s u_r) A_r)`.

A compact integral form for the untwisted induction pairs the members at `s`
and `-s` invariantly. At `s = 0` it is an invariant positive form, and an
equivalence between the members at `s` and `-s` turns it into a nonzero
invariant sesquilinear form for the member at `s`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped NNReal ComplexConjugate

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The character `q ↦ ∏ i |det m_i(q)| ^ u_i` of the standard parabolic, where
`m_i(q)` is the `i`th diagonal block of `q`. -/
def exponentModulus (u : Fin B.length → ℝ) : B.parabolic F.Carrier →* ℝ≥0ˣ :=
  ∏ i, (Units.map (NNReal.rpowMonoidHom (u i))).comp
    ((T.determinantNorm (B.size i)).comp
      ((Pi.evalMonoidHom (fun j => GeneralLinear (B.size j) F.Carrier) i).comp
        (B.leviProjection F.Carrier)))

theorem coe_exponentModulus (u : Fin B.length → ℝ) (q : B.parabolic F.Carrier) :
    ((T.exponentModulus B u q : ℝ≥0ˣ) : ℝ≥0) =
      ∏ i, ((T.determinantNorm (B.size i) (B.leviProjection F.Carrier q i) : ℝ≥0ˣ) : ℝ≥0) ^
        u i := by
  simp [exponentModulus, Units.coe_prod]

/-- The exponent modulus is trivial on the intersection of the parabolic with a
compact subgroup. -/
theorem exponentModulus_eq_one_of_mem (u : Fin B.length → ℝ)
    (K : Subgroup (GeneralLinear n F.Carrier))
    (hK : letI := T.topology; IsCompact (K : Set (GeneralLinear n F.Carrier)))
    (q : B.parabolic F.Carrier) (hq : (q : GeneralLinear n F.Carrier) ∈ K) :
    T.exponentModulus B u q = 1 := by
  let := T.topology
  let := T.isTopologicalRing
  let := T.fieldT2
  have hJ : IsCompact ((K.subgroupOf (B.parabolic F.Carrier)) :
      Set (B.parabolic F.Carrier)) := by
    rw [Subtype.isCompact_iff, Subgroup.coe_subgroupOf, Subgroup.coe_subtype,
      Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact hK.inter_right (B.isClosed_parabolic F.Carrier)
  have hdet (i : Fin B.length) :
      T.determinantNorm (B.size i) (B.leviProjection F.Carrier q i) = 1 := by
    let χ : B.parabolic F.Carrier →* ℝ≥0ˣ := (T.determinantNorm (B.size i)).comp
      ((Pi.evalMonoidHom (fun j => GeneralLinear (B.size j) F.Carrier) i).comp
        (B.leviProjection F.Carrier))
    have hχ : Continuous χ :=
      (T.determinantNormContinuous (B.size i)).continuous.comp
        ((continuous_apply i).comp (B.leviProjectionContinuous F.Carrier).continuous)
    exact Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact χ hχ _ hJ (Subgroup.mem_subgroupOf.mpr hq)
  apply Units.ext
  rw [coe_exponentModulus, Units.val_one]
  apply Finset.prod_eq_one
  intro i _
  rw [hdet i, Units.val_one, NNReal.one_rpow]

/-- The real power of the exponent modulus is the product of the block
determinant powers with exponents `s u_i`. -/
theorem realPowerCharacter_exponentModulus (u : Fin B.length → ℝ) (s : ℝ)
    (q : B.parabolic F.Carrier) :
    (realPowerCharacter (T.exponentModulus B u) s q : ℂ) =
      ((∏ i, T.determinantPowerCharacter (B.size i) (s * u i)
        (B.leviProjection F.Carrier q i) : ℂˣ) : ℂ) := by
  rw [coe_realPowerCharacter, Units.coe_prod]
  simp only [determinantPowerCharacter, coe_realPowerCharacter]
  rw [← NNReal.coe_rpow, coe_exponentModulus, ← NNReal.finsetProd_rpow]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  rw [← NNReal.coe_rpow, ← NNReal.coe_rpow, ← NNReal.rpow_mul, mul_comm]
  rw [NNReal.coe_rpow]

section Tensor

variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Twisting each block by a determinant power multiplies the tensor action by
the product of the block characters. -/
theorem blockTensor_determinantTwist
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (u : Fin B.length → ℝ) (m : B.Levi F.Carrier) :
    B.blockTensor (fun i => twist (T.determinantPowerCharacter (B.size i) (u i)) (σ i)) m =
      ((∏ i, T.determinantPowerCharacter (B.size i) (u i) (m i) : ℂˣ) : ℂ) •
        B.blockTensor σ m := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change FiniteTensor.external _ m (PiTensorProduct.tprod ℂ v) =
    ((∏ i, T.determinantPowerCharacter (B.size i) (u i) (m i) : ℂˣ) : ℂ) •
      FiniteTensor.external σ m (PiTensorProduct.tprod ℂ v)
  rw [FiniteTensor.external_tprod, FiniteTensor.external_tprod]
  change PiTensorProduct.tprod ℂ (fun i =>
      (T.determinantPowerCharacter (B.size i) (u i) (m i) : ℂ) • σ i (m i) (v i)) = _
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ, Units.coe_prod]

/-- The real power twist of the untwisted inducing representation by the
exponent modulus is the inducing representation of the twisted blocks. -/
theorem realPowerTwist_exponentModulus
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (u : Fin B.length → ℝ) (s : ℝ) :
    realPowerTwist (T.exponentModulus B u) s
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) =
      twist (T.parabolicHalfModulus B)
        ((B.blockTensor (fun i => twist (T.determinantPowerCharacter (B.size i) (s * u i))
          (σ i))).comp (B.leviProjection F.Carrier)) := by
  apply MonoidHom.ext
  intro q
  change (realPowerCharacter (T.exponentModulus B u) s q : ℂ) •
      ((T.parabolicHalfModulus B q : ℂ) • B.blockTensor σ (B.leviProjection F.Carrier q)) =
    (T.parabolicHalfModulus B q : ℂ) •
      B.blockTensor (fun i => twist (T.determinantPowerCharacter (B.size i) (s * u i))
        (σ i)) (B.leviProjection F.Carrier q)
  rw [T.blockTensor_determinantTwist B σ, T.realPowerCharacter_exponentModulus B u s q,
    smul_comm]

end Tensor

section Height

/-- The Iwasawa height of a factorization `G = P K` with `K` compact open, with
the exponent modulus. -/
def exponentHeight (u : Fin B.length → ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier)),
      IsCompact (K : Set (GeneralLinear n F.Carrier)) →
      (∀ g : GeneralLinear n F.Carrier, ∃ (q : B.parabolic F.Carrier) (k : K),
        g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier)) →
      Induction.IwasawaHeight (B.parabolic F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  intro K hK hPK
  exact
    { compactSubgroup := K
      isCompact := hK
      factor := hPK
      modulus := T.exponentModulus B u
      modulus_eq_one := fun q hq =>
        T.exponentModulus_eq_one_of_mem B u K.toSubgroup hK q hq }

theorem exponentHeight_modulus (u : Fin B.length → ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier)))
      (hPK : ∀ g : GeneralLinear n F.Carrier, ∃ (q : B.parabolic F.Carrier) (k : K),
        g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier)),
      (T.exponentHeight B u K hK hPK).modulus = T.exponentModulus B u := by
  intro K hK hPK
  rfl

/-- At the parameter `s`, the family of the exponent height on the untwisted
normalized induced space is equivalent to the actual normalized product of the
blocks twisted by `ν ^ (s u_i)`. -/
def exponentFamilyEquiv
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier)))
      (hPK : ∀ g : GeneralLinear n F.Carrier, ∃ (q : B.parabolic F.Carrier) (k : K),
        g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier))
      (s : ℝ),
      ((T.exponentHeight B u K hK hPK).family
          (twist (T.parabolicHalfModulus B)
            ((B.blockTensor (fun i => (A i).representation)).comp
              (B.leviProjection F.Carrier))) s).Equiv
        (T.twistedProductInduced B A (fun i => s * u i)).representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  intro K hK hPK s
  exact ((T.exponentHeight B u K hK hPK).familyEquiv _ s).trans
    (Induction.smoothInducedEquiv _
      (equivOfRepresentationEq
        (T.realPowerTwist_exponentModulus B (fun i => (A i).representation) u s)))

end Height

section Pairing

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (B.Levi F.Carrier) V)

/-- The compact integral form of the untwisted normalized induction pairs the
members of any Iwasawa-height family at `s` and `-s` invariantly. -/
theorem normalizedIntegralForm_family_neg (b : InvariantPositiveForm σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (K : Subgroup (GeneralLinear n F.Carrier)) [MeasurableSpace K]
      (μ : Measure K) [μ.IsOpenPosMeasure]
      (hPK : ∀ g : GeneralLinear n F.Carrier, ∃ (q : B.parabolic F.Carrier) (k : K),
        g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier))
      (hscalar : ∀ φ : GeneralLinear n F.Carrier → ℂ, IsLocallyConstant φ →
        (∀ (q : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier),
          φ ((q : GeneralLinear n F.Carrier) * x) =
            (((T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) * φ x) →
        ∀ g : GeneralLinear n F.Carrier,
          Integrable (fun k : K => φ ((k : GeneralLinear n F.Carrier) * g)) μ ∧
          (∫ k : K, φ ((k : GeneralLinear n F.Carrier) * g) ∂μ) =
            ∫ k : K, φ k ∂μ)
      (H : Induction.IwasawaHeight (B.parabolic F.Carrier)) (s : ℝ)
      (g : GeneralLinear n F.Carrier)
      (f h : Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))),
      (T.normalizedIntegralForm B σ b K μ hPK hscalar).inner
          (H.family _ s g f) (H.family _ (-s) g h) =
        (T.normalizedIntegralForm B σ b K μ hPK hscalar).inner f h := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro K _ μ _ hPK hscalar H s g f h
  rw [← (T.normalizedIntegralForm B σ b K μ hPK hscalar).invariant g f h]
  change (∫ k : K, b.inner (Induction.eval _ _ (H.family _ s g f) k)
      (Induction.eval _ _ (H.family _ (-s) g h) k) ∂μ) =
    ∫ k : K, b.inner (Induction.eval _ _ (T.normalizedParabolicInduced B σ g f) k)
      (Induction.eval _ _ (T.normalizedParabolicInduced B σ g h) k) ∂μ
  congr 1
  funext k
  rw [H.inner_eval_family_neg b.toInnerProductCore]
  rfl

/-- The compact integral form is an invariant positive form for the member of an
Iwasawa-height family at `0`. -/
def familyZeroForm (b : InvariantPositiveForm σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (K : Subgroup (GeneralLinear n F.Carrier)) [MeasurableSpace K]
      (μ : Measure K) [μ.IsOpenPosMeasure]
      (_hPK : ∀ g : GeneralLinear n F.Carrier, ∃ (q : B.parabolic F.Carrier) (k : K),
        g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier))
      (_hscalar : ∀ φ : GeneralLinear n F.Carrier → ℂ, IsLocallyConstant φ →
        (∀ (q : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier),
          φ ((q : GeneralLinear n F.Carrier) * x) =
            (((T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) * φ x) →
        ∀ g : GeneralLinear n F.Carrier,
          Integrable (fun k : K => φ ((k : GeneralLinear n F.Carrier) * g)) μ ∧
          (∫ k : K, φ ((k : GeneralLinear n F.Carrier) * g) ∂μ) =
            ∫ k : K, φ k ∂μ)
      (H : Induction.IwasawaHeight (B.parabolic F.Carrier)),
      InvariantPositiveForm (H.family
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) 0) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  intro K _ μ _ hPK hscalar H
  exact
    { (T.normalizedIntegralForm B σ b K μ hPK hscalar).toInnerProductCore with
      invariant := fun g f h => by
        have := T.normalizedIntegralForm_family_neg B σ b K μ hPK hscalar H 0 g f h
        rwa [neg_zero] at this }

end Pairing

section Sesquilinear

variable {G : Type*} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The form `(v, w) ↦ c (v, e w)` attached to a positive form `c` and a linear
map `e`. -/
def pairingSesquilinear (c : InnerProductSpace.Core ℂ W) (e : W →ₗ[ℂ] W) :
    W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ := by
  letI : InnerProductSpace.Core ℂ W := c
  exact LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun v w => c.inner v (e w))
    (fun v v' w => c.add_left v v' (e w))
    (fun a v w => c.smul_left v (e w) a)
    (fun v w w' => by rw [map_add, InnerProductSpace.Core.inner_add_right])
    (fun a v w => by
      rw [map_smul, InnerProductSpace.Core.inner_smul_right, smul_eq_mul, RingHom.id_apply])

@[simp]
theorem pairingSesquilinear_apply (c : InnerProductSpace.Core ℂ W) (e : W →ₗ[ℂ] W)
    (v w : W) : pairingSesquilinear c e v w = c.inner v (e w) := rfl

/-- If `c` pairs `π` with `π'` invariantly and `e` is an equivalence from `π` to
`π'`, then `(v, w) ↦ c (v, e w)` is a nonzero invariant sesquilinear form for
`π` on a nonzero space. -/
theorem pairingSesquilinear_invariant (c : InnerProductSpace.Core ℂ W)
    {π π' : Representation ℂ G W}
    (hc : ∀ (g : G) (v w : W), c.inner (π g v) (π' g w) = c.inner v w)
    (e : π.Equiv π') (g : G) (v w : W) :
    pairingSesquilinear c e.toLinearMap (π g v) (π g w) =
      pairingSesquilinear c e.toLinearMap v w := by
  simp only [pairingSesquilinear_apply]
  rw [show e.toLinearMap (π g w) = π' g (e.toLinearMap w) from
    Representation.IntertwiningMap.isIntertwining π π' e.toIntertwiningMap g w]
  exact hc g v _

theorem pairingSesquilinear_ne_zero (c : InnerProductSpace.Core ℂ W) [Nontrivial W]
    (e : W ≃ₗ[ℂ] W) : pairingSesquilinear c e.toLinearMap ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have h0 := congrArg (fun φ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ => φ v (e.symm v)) h
  simp only [pairingSesquilinear_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.zero_apply] at h0
  exact hv (c.definite v h0)

end Sesquilinear

end Langlands.PadicField.TopologicalData
