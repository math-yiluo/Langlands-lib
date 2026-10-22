import Langlands.Representation.Hecke.NormalizedIndicator
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-! # Bi-invariant convolution and compact-open unital corners -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Hecke

open HarmonicAnalysis (SchwartzBruhat)

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

namespace TestFunction

omit [BorelSpace G] in
theorem convolution_rightTranslate (f g : SchwartzBruhat G) (a : G) :
    convolution μ f (rightTranslate a g) = rightTranslate a (convolution μ f g) := by
  ext x
  simp [convolution_apply, mul_assoc]

variable [IsMulLeftInvariant μ]

theorem convolution_leftTranslate (f g : SchwartzBruhat G) (a : G) :
    convolution μ (leftTranslate a f) g = leftTranslate a (convolution μ f g) := by
  ext x
  change (∫ y, f (a⁻¹ * y) * g (y⁻¹ * x) ∂μ) =
    ∫ y, f y * g (y⁻¹ * (a⁻¹ * x)) ∂μ
  rw [← integral_mul_left_eq_self (fun y => f (a⁻¹ * y) * g (y⁻¹ * x)) a]
  simp only [inv_mul_cancel_left, mul_inv_rev, mul_assoc]

theorem convolution_leftInvariant {K : Subgroup G} {f : SchwartzBruhat G}
    (hf : ∀ k : K, ∀ x, f ((k : G) * x) = f x) (g : SchwartzBruhat G) :
    ∀ k : K, ∀ x, convolution μ f g ((k : G) * x) = convolution μ f g x := by
  intro k x
  have h : leftTranslate ((k : G)⁻¹) f = f := by
    ext y
    simpa using hf k y
  have ht := convolution_leftTranslate μ f g ((k : G)⁻¹)
  rw [h] at ht
  simpa using (congrArg (fun q : SchwartzBruhat G => q x) ht).symm

omit [BorelSpace G] [IsMulLeftInvariant μ] in
theorem convolution_rightInvariant {L : Subgroup G} (f : SchwartzBruhat G)
    {g : SchwartzBruhat G} (hg : ∀ l : L, ∀ x, g (x * (l : G)) = g x) :
    ∀ l : L, ∀ x, convolution μ f g (x * (l : G)) = convolution μ f g x := by
  intro l x
  have h : rightTranslate (l : G) g = g := ext (hg l)
  have ht := convolution_rightTranslate μ f g (l : G)
  rw [h] at ht
  exact (congrArg (fun q : SchwartzBruhat G => q x) ht).symm

theorem convolution_mem_biInvariant_of_left_right {K L : Subgroup G}
    {f g : SchwartzBruhat G} (hf : ∀ k : K, ∀ x, f ((k : G) * x) = f x)
    (hg : ∀ l : L, ∀ x, g (x * (l : G)) = g x) :
    convolution μ f g ∈ biInvariant K L :=
  ⟨convolution_leftInvariant μ hf g, convolution_rightInvariant μ f hg⟩

theorem convolution_mem_biInvariant {K L M N : Subgroup G}
    {f g : SchwartzBruhat G} (hf : f ∈ biInvariant K L) (hg : g ∈ biInvariant M N) :
    convolution μ f g ∈ biInvariant K N :=
  convolution_mem_biInvariant_of_left_right μ hf.1 hg.2

/-- The mixed bi-invariant convolution map uses the original test-function subspaces. -/
def biInvariantConvolution [IsFiniteMeasureOnCompacts μ] (K L M N : Subgroup G) :
    biInvariant K L →ₗ[ℂ] biInvariant M N →ₗ[ℂ] biInvariant K N where
  toFun f :=
    { toFun := fun g => ⟨convolution μ f g, convolution_mem_biInvariant μ f.property g.property⟩
      map_add' := fun g h => Subtype.ext (convolution_add_right μ f g h)
      map_smul' := fun c g => Subtype.ext (convolution_smul_right μ c f g) }
  map_add' f g := by
    ext h x
    exact congrArg (fun q : SchwartzBruhat G => q x) (convolution_add_left μ f g h)
  map_smul' c f := by
    ext g x
    exact congrArg (fun q : SchwartzBruhat G => q x) (convolution_smul_left μ c f g)

end TestFunction

namespace HeckeAlgebra

section Subalgebra

variable [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]

/-- Actual bi-K-invariant functions, closed under the Haar convolution. -/
def biInvariantSubalgebra (K : Subgroup G) : NonUnitalSubalgebra ℂ (HeckeAlgebra μ) where
  toSubmodule := (TestFunction.biInvariant K K).comap (toTestFunction μ).toLinearMap
  mul_mem' := fun hf hg => TestFunction.convolution_mem_biInvariant μ hf hg

@[simp] theorem mem_biInvariantSubalgebra (K : Subgroup G) (f : HeckeAlgebra μ) :
    f ∈ biInvariantSubalgebra μ K ↔
      (f : SchwartzBruhat G) ∈ TestFunction.biInvariant K K := Iff.rfl

theorem biInvariantSubalgebra_antitone {K L : Subgroup G} (hLK : L ≤ K) :
    biInvariantSubalgebra μ K ≤ biInvariantSubalgebra μ L :=
  TestFunction.biInvariant_antitone hLK hLK

/-- Refinement embeds the larger subgroup's invariants into the smaller subgroup's. -/
def biInvariantInclusion {K L : Subgroup G} (hLK : L ≤ K) :
    biInvariantSubalgebra μ K →ₙₐ[ℂ] biInvariantSubalgebra μ L :=
  NonUnitalSubalgebra.inclusion (biInvariantSubalgebra_antitone μ hLK)

theorem biInvariantInclusion_injective {K L : Subgroup G} (hLK : L ≤ K) :
    Function.Injective (biInvariantInclusion μ hLK) :=
  NonUnitalSubalgebra.inclusion_injective _

end Subalgebra

variable [μ.IsHaarMeasure] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

theorem sandwich_mem_biInvariant (f : HeckeAlgebra μ) :
    (normalizedIndicator μ K hK * f * normalizedIndicator μ K hK : SchwartzBruhat G) ∈
      TestFunction.biInvariant K.toSubgroup K.toSubgroup :=
  TestFunction.convolution_mem_biInvariant_of_left_right μ
    (TestFunction.convolution_leftInvariant μ (normalizedIndicator_mem_biInvariant μ K hK).1 f)
    (normalizedIndicator_mem_biInvariant μ K hK).2

theorem mem_biInvariant_iff_sandwich (f : HeckeAlgebra μ) :
    (f : SchwartzBruhat G) ∈ TestFunction.biInvariant K.toSubgroup K.toSubgroup ↔
      normalizedIndicator μ K hK * f * normalizedIndicator μ K hK = f := by
  constructor
  · intro hf
    rw [normalizedIndicator_mul_of_leftInvariant μ K hK f hf.1,
      mul_normalizedIndicator_of_rightInvariant μ K hK f hf.2]
  · intro hf
    exact hf ▸ sandwich_mem_biInvariant μ K hK f

/-- Equality with the actual set-theoretic corner e_K H(G) e_K. -/
theorem mem_biInvariant_iff_exists_sandwich (f : HeckeAlgebra μ) :
    (f : SchwartzBruhat G) ∈ TestFunction.biInvariant K.toSubgroup K.toSubgroup ↔
      ∃ g : HeckeAlgebra μ, normalizedIndicator μ K hK * g * normalizedIndicator μ K hK = f := by
  constructor
  · intro hf
    exact ⟨f, (mem_biInvariant_iff_sandwich μ K hK f).mp hf⟩
  · rintro ⟨g, rfl⟩
    exact sandwich_mem_biInvariant μ K hK g

/-- The actual bi-invariant corner carrier; compactness is retained for its unit. -/
def Corner (_hK : IsCompact (K : Set G)) := ↥(biInvariantSubalgebra μ K.toSubgroup)

namespace Corner

instance : NonUnitalRing (Corner μ K hK) :=
  inferInstanceAs (NonUnitalRing ↥(biInvariantSubalgebra μ K.toSubgroup))
instance : Module ℂ (Corner μ K hK) :=
  inferInstanceAs (Module ℂ ↥(biInvariantSubalgebra μ K.toSubgroup))
instance : IsScalarTower ℂ (Corner μ K hK) (Corner μ K hK) :=
  inferInstanceAs (IsScalarTower ℂ ↥(biInvariantSubalgebra μ K.toSubgroup)
    ↥(biInvariantSubalgebra μ K.toSubgroup))
instance : SMulCommClass ℂ (Corner μ K hK) (Corner μ K hK) :=
  inferInstanceAs (SMulCommClass ℂ ↥(biInvariantSubalgebra μ K.toSubgroup)
    ↥(biInvariantSubalgebra μ K.toSubgroup))

/-- The faithful embedding of the corner into the full, generally nonunital Hecke algebra. -/
def toHeckeAlgebra : Corner μ K hK →ₙₐ[ℂ] HeckeAlgebra μ :=
  NonUnitalSubalgebraClass.subtype (biInvariantSubalgebra μ K.toSubgroup)

theorem toHeckeAlgebra_injective : Function.Injective (toHeckeAlgebra μ K hK) :=
  Subtype.coe_injective

/-- The identity linear equivalence with the previously constructed bi-invariant subspace. -/
def toBiInvariant : Corner μ K hK ≃ₗ[ℂ]
    TestFunction.biInvariant K.toSubgroup K.toSubgroup := LinearEquiv.refl ℂ _

instance : CoeFun (Corner μ K hK) (fun _ => G → ℂ) :=
  ⟨fun f => toHeckeAlgebra μ K hK f⟩

@[simp] theorem toHeckeAlgebra_apply (f : Corner μ K hK) (x : G) :
    toHeckeAlgebra μ K hK f x = f x := rfl

@[simp] theorem mul_apply (f g : Corner μ K hK) (x : G) :
    (f * g) x = ∫ y, f y * g (y⁻¹ * x) ∂μ := rfl

theorem leftInvariant (f : Corner μ K hK) (k : K) (x : G) :
    f ((k : G) * x) = f x := f.property.1 k x

theorem rightInvariant (f : Corner μ K hK) (k : K) (x : G) :
    f (x * (k : G)) = f x := f.property.2 k x

/-- Double averaging projects the full Hecke space onto its actual compact-open corner. -/
def project : HeckeAlgebra μ →ₗ[ℂ] Corner μ K hK where
  toFun f := ⟨normalizedIndicator μ K hK * f * normalizedIndicator μ K hK,
    sandwich_mem_biInvariant μ K hK f⟩
  map_add' f g := by
    apply Subtype.ext
    change normalizedIndicator μ K hK * (f + g) * normalizedIndicator μ K hK = _
    simp only [mul_add, add_mul]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    change normalizedIndicator μ K hK * (c • f) * normalizedIndicator μ K hK = _
    simp only [mul_smul_comm, smul_mul_assoc]
    rfl

@[simp] theorem toHeckeAlgebra_project (f : HeckeAlgebra μ) :
    toHeckeAlgebra μ K hK (project μ K hK f) =
      normalizedIndicator μ K hK * f * normalizedIndicator μ K hK := rfl

@[simp] theorem project_toHeckeAlgebra (f : Corner μ K hK) :
    project μ K hK (toHeckeAlgebra μ K hK f) = f :=
  Subtype.ext ((mem_biInvariant_iff_sandwich μ K hK _).mp f.property)

theorem range_toHeckeAlgebra :
    Set.range (toHeckeAlgebra μ K hK) =
      Set.range (fun f : HeckeAlgebra μ =>
        normalizedIndicator μ K hK * f * normalizedIndicator μ K hK) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact (mem_biInvariant_iff_exists_sandwich μ K hK _).mp g.property
  · rintro ⟨g, rfl⟩
    exact ⟨project μ K hK g, rfl⟩

instance : One (Corner μ K hK) :=
  ⟨⟨normalizedIndicator μ K hK, normalizedIndicator_mem_biInvariant μ K hK⟩⟩

@[simp] theorem toHeckeAlgebra_one :
    toHeckeAlgebra μ K hK 1 = normalizedIndicator μ K hK := rfl

instance ring : Ring (Corner μ K hK) where
  __ : NonUnitalRing (Corner μ K hK) := inferInstance
  one := 1
  one_mul f := Subtype.ext
    (normalizedIndicator_mul_of_leftInvariant μ K hK _ f.property.1)
  mul_one f := Subtype.ext
    (mul_normalizedIndicator_of_rightInvariant μ K hK _ f.property.2)
  natCast n := n • (1 : Corner μ K hK)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast z := z • (1 : Corner μ K hK)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

instance : Algebra ℂ (Corner μ K hK) := Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- Refinement inclusions preserve convolution and complex scalars; their units may differ. -/
def inclusion {L : OpenSubgroup G} (hL : IsCompact (L : Set G)) (hLK : L ≤ K) :
    Corner μ K hK →ₙₐ[ℂ] Corner μ L hL := biInvariantInclusion μ hLK

theorem inclusion_injective {L : OpenSubgroup G} (hL : IsCompact (L : Set G)) (hLK : L ≤ K) :
    Function.Injective (inclusion μ K hK hL hLK) := biInvariantInclusion_injective μ hLK

@[simp] theorem toHeckeAlgebra_inclusion {L : OpenSubgroup G}
    (hL : IsCompact (L : Set G)) (hLK : L ≤ K) (f : Corner μ K hK) :
    toHeckeAlgebra μ L hL (inclusion μ K hK hL hLK f) = toHeckeAlgebra μ K hK f := rfl

@[simp] theorem inclusion_refl (f : Corner μ K hK) :
    inclusion μ K hK hK le_rfl f = f := rfl

theorem inclusion_trans {L M : OpenSubgroup G}
    (hL : IsCompact (L : Set G)) (hM : IsCompact (M : Set G))
    (hLK : L ≤ K) (hML : M ≤ L) (f : Corner μ K hK) :
    inclusion μ L hL hM hML (inclusion μ K hK hL hLK f) =
      inclusion μ K hK hM (hML.trans hLK) f := rfl

end Corner
end HeckeAlgebra
end Langlands.Hecke
