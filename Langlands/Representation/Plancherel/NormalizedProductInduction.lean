import Langlands.Representation.Induction.BinaryProductTensor
import Langlands.Representation.Aubert.General.Parabolic
import Langlands.HarmonicAnalysis.HaarConjugacy
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Actual normalized induction on a product

The product decomposition and Haar half-modulus are derived from the actual
factor subgroups, before applying the binary tensor comparison.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal TensorProduct

namespace Langlands.HaarModulus

universe uG uH

section Algebra

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- Products of actual normalizing subgroups normalize the product radical. -/
theorem prod_normalizes {U P : Subgroup G} {V Q : Subgroup H}
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V : Set H)) :
    P.prod Q ≤ Subgroup.normalizer (U.prod V : Set (G × H)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro x hx y hy
  exact ⟨(Subgroup.le_normalizer_iff.mp hPU) x.1 hx.1 y.1 hy.1,
    (Subgroup.le_normalizer_iff.mp hQV) x.2 hx.2 y.2 hy.2⟩

end Algebra

section Topology

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- The product subgroup with its subspace topology is the product of subgroups. -/
def subgroupProdEquiv (U : Subgroup G) (V : Subgroup H) : U.prod V ≃ₜ* U × V where
  toMulEquiv := U.prodEquiv V
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- Coordinatewise continuous group automorphisms. -/
def productAutomorphism (a : G ≃ₜ* G) (b : H ≃ₜ* H) : G × H ≃ₜ* G × H where
  toFun x := (a x.1, b x.2)
  invFun x := (a.symm x.1, b.symm x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp
  continuous_toFun := a.continuous.prodMap b.continuous
  continuous_invFun := a.symm.continuous.prodMap b.symm.continuous

end Topology

section ProductHaar

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [SecondCountableTopology G] [SecondCountableTopology H]
  [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]

/-- Product Haar measure gives the product of the two actual scaling factors. -/
theorem haarChar_productAutomorphism (a : G ≃ₜ* G) (b : H ≃ₜ* H) :
    mulEquivHaarChar (productAutomorphism a b) =
      mulEquivHaarChar a * mulEquivHaarChar b := by
  let μ : Measure G := haar
  let ν : Measure H := haar
  let ρ : Measure (G × H) := μ.prod ν
  have ha : Measurable (a : G → G) := a.continuous.measurable
  have hb : Measurable (b : H → H) := b.continuous.measurable
  have hscale : (mulEquivHaarChar a * mulEquivHaarChar b) •
      ρ.map (productAutomorphism a b) = ρ := by
    change (mulEquivHaarChar a * mulEquivHaarChar b) •
      (μ.prod ν).map (Prod.map a b) = μ.prod ν
    rw [← Measure.map_prod_map μ ν ha hb]
    calc
      _ = (mulEquivHaarChar a • μ.map a).prod
          (mulEquivHaarChar b • ν.map b) := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
      _ = μ.prod ν := by
        rw [mulEquivHaarChar_smul_map μ a, mulEquivHaarChar_smul_map ν b]
  rw [mulEquivHaarChar_eq ρ]
  have hs := haarScalarFactor_smul (ρ.map (productAutomorphism a b))
    (ρ.map (productAutomorphism a b))
    (c := mulEquivHaarChar a * mulEquivHaarChar b)
  rw! [hscale] at hs
  simpa using hs

end ProductHaar

section Closed

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [SecondCountableTopology G] [SecondCountableTopology H]
  (U P : Subgroup G) (V Q : Subgroup H)
  (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set H))
  (hPU : P ≤ Subgroup.normalizer (U : Set G))
  (hQV : Q ≤ Subgroup.normalizer (V : Set H))

/-- The actual positive modulus on the product radical factors coordinatewise. -/
theorem closedRestrictCharacter_prod (p : P.prod Q) :
    closedRestrictCharacter (U.prod V) (hU.prod hV) (P.prod Q)
        (prod_normalizes hPU hQV) p =
      closedRestrictCharacter U hU P hPU ⟨p.1.1, p.2.1⟩ *
        closedRestrictCharacter V hV Q hQV ⟨p.1.2, p.2.2⟩ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let : LocallyCompactSpace (U.prod V) := (hU.prod hV).locallyCompactSpace
  let : SecondCountableTopology U :=
    TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  let : SecondCountableTopology V :=
    TopologicalSpace.Subtype.secondCountableTopology (V : Set H)
  let : MeasurableSpace U := borel U
  let : MeasurableSpace V := borel V
  let : MeasurableSpace (U.prod V) := borel (U.prod V)
  let : BorelSpace U := ⟨rfl⟩
  let : BorelSpace V := ⟨rfl⟩
  let : BorelSpace (U.prod V) := ⟨rfl⟩
  let : BorelSpace (U × V) := Prod.borelSpace
  let a := normalizerConj U ⟨p.1.1, hPU p.2.1⟩
  let b := normalizerConj V ⟨p.1.2, hQV p.2.2⟩
  apply Units.ext
  change mulEquivHaarChar
      (normalizerConj (U.prod V) ⟨p, prod_normalizes hPU hQV p.2⟩) =
    mulEquivHaarChar a * mulEquivHaarChar b
  calc
    _ = mulEquivHaarChar (productAutomorphism a b) := by
      apply Geometric.haarChar_eq_of_conjugacy (subgroupProdEquiv U V)
      intro x
      rfl
    _ = _ := haarChar_productAutomorphism a b

/-- The canonical positive square roots multiply; no sign choice is added. -/
theorem closedHalfCharacter_prod (p : P.prod Q) :
    closedHalfCharacter (U.prod V) (hU.prod hV) (P.prod Q)
        (prod_normalizes hPU hQV) p =
      closedHalfCharacter U hU P hPU ⟨p.1.1, p.2.1⟩ *
        closedHalfCharacter V hV Q hQV ⟨p.1.2, p.2.2⟩ := by
  apply Units.ext
  change ((NNReal.sqrt
      (closedRestrictCharacter (U.prod V) (hU.prod hV) (P.prod Q)
        (prod_normalizes hPU hQV) p : ℝ≥0) : ℝ) : ℂ) =
    ((NNReal.sqrt (closedRestrictCharacter U hU P hPU ⟨p.1.1, p.2.1⟩ : ℝ≥0) : ℝ) : ℂ) *
      ((NNReal.sqrt (closedRestrictCharacter V hV Q hQV ⟨p.1.2, p.2.2⟩ : ℝ≥0) : ℝ) : ℂ)
  rw [closedRestrictCharacter_prod U P V Q hU hV hPU hQV p, Units.val_mul,
    NNReal.sqrt_mul, NNReal.coe_mul, Complex.ofReal_mul]

end Closed

end Langlands.HaarModulus

namespace Langlands.Aubert.General.IsSemidirectDecomposition

universe uG uH

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  {P M U : Subgroup G} {Q N V : Subgroup H}

/-- Actual semidirect decompositions give the semidirect decomposition of the
literal product subgroups. -/
theorem prod (h : IsSemidirectDecomposition P M U)
    (k : IsSemidirectDecomposition Q N V) :
    IsSemidirectDecomposition (P.prod Q) (M.prod N) (U.prod V) := by
  refine ⟨fun x hx => ⟨h.levi_le hx.1, k.levi_le hx.2⟩,
    fun x hx => ⟨h.unipotent_le hx.1, k.unipotent_le hx.2⟩,
    HaarModulus.prod_normalizes h.le_normalizer k.le_normalizer, ?_⟩
  rw [Subgroup.isComplement'_def,
    Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro p
  let p₁ : P := ⟨p.1.1, p.2.1⟩
  let p₂ : Q := ⟨p.1.2, p.2.2⟩
  let m : M.prod N :=
    ⟨(h.projection p₁, k.projection p₂),
      (h.projection p₁).2, (k.projection p₂).2⟩
  let s : (M.prod N).subgroupOf (P.prod Q) :=
    ⟨⟨m, h.levi_le m.2.1, k.levi_le m.2.2⟩, m.2⟩
  refine ⟨s, ⟨h.projection_inv_mul_mem p₁, k.projection_inv_mul_mem p₂⟩, ?_⟩
  intro t ht
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val
      ((h.projection_eq_iff p₁ ⟨t.1.1.1, t.2.1⟩).mpr ht.1).symm
  · exact congrArg Subtype.val
      ((k.projection_eq_iff p₂ ⟨t.1.1.2, t.2.2⟩).mpr ht.2).symm

/-- The actual quotient-defined product projection is coordinatewise. -/
theorem prod_projection (h : IsSemidirectDecomposition P M U)
    (k : IsSemidirectDecomposition Q N V) (p : P.prod Q) :
    (h.prod k).projection p =
      ⟨(h.projection ⟨p.1.1, p.2.1⟩, k.projection ⟨p.1.2, p.2.2⟩),
        (h.projection ⟨p.1.1, p.2.1⟩).2,
        (k.projection ⟨p.1.2, p.2.2⟩).2⟩ := by
  apply ((h.prod k).projection_eq_iff p _).mpr
  exact ⟨h.projection_inv_mul_mem ⟨p.1.1, p.2.1⟩,
    k.projection_inv_mul_mem ⟨p.1.2, p.2.2⟩⟩

end Langlands.Aubert.General.IsSemidirectDecomposition

namespace Langlands.Plancherel

open Langlands.Aubert.General

universe uG uH uV uW

section SmoothExternal

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  (A : SmoothRep.{0, uG, uV} ℂ G) (B : SmoothRep.{0, uH, uW} ℂ H)

/-- Product open stabilizers prove smoothness with independent factor universes. -/
theorem isSmooth_binaryExternal :
    IsSmooth (Induction.BinaryTensor.external A.representation B.representation) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨K, hK⟩ := A.isSmooth v
    obtain ⟨L, hL⟩ := B.isSmooth w
    refine ⟨K.prod L, ?_⟩
    intro x
    change A.representation (x : G × H).1 v ⊗ₜ[ℂ]
      B.representation (x : G × H).2 w = v ⊗ₜ[ℂ] w
    have hv : A.representation (x : G × H).1 v = v := hK ⟨_, x.2.1⟩
    have hw : B.representation (x : G × H).2 w = w := hL ⟨_, x.2.2⟩
    rw [hv, hw]
  | add t s ht hs => exact isSmoothVector_add ht hs

/-- The actual smooth external tensor on the ordinary binary group. -/
def binaryExternalObject : SmoothRep.{0, max uG uH, max uV uW} ℂ (G × H) :=
  SmoothRep.of (Induction.BinaryTensor.external A.representation B.representation)
    (isSmooth_binaryExternal A B)

end SmoothExternal

section LeviObject

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  {M : Subgroup G} {N : Subgroup H}

/-- The external tensor on the literal product Levi, through its actual
continuous identification with the product of the factor Levis. -/
def productLeviObject (A : SmoothRep.{0, uG, uV} ℂ M)
    (B : SmoothRep.{0, uH, uW} ℂ N) :
    SmoothRep.{0, max uG uH, max uV uW} ℂ (M.prod N) :=
  SmoothRep.pullback (HaarModulus.subgroupProdEquiv M N) (binaryExternalObject A B)

@[simp]
theorem productLeviObject_representation (A : SmoothRep.{0, uG, uV} ℂ M)
    (B : SmoothRep.{0, uH, uW} ℂ N) :
    (productLeviObject A B).representation =
      Induction.BinaryTensor.inducing M N A.representation B.representation :=
  rfl

end LeviObject

section Normalized

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  [SecondCountableTopology G] [SecondCountableTopology H]
  {P M U : Subgroup G} {Q N V : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N V)
  (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set H))
  (A : SmoothRep.{0, uG, uV} ℂ M) (B : SmoothRep.{0, uH, uW} ℂ N)

/-- The actual product inducing action equals the product of the two normalized
inducing actions; both the projection and the Haar half-character are proved. -/
theorem product_inducingRepresentation :
    inducingRepresentation (h.prod k) (hU.prod hV) (productLeviObject A B) =
      Induction.BinaryTensor.inducing P Q
        (inducingRepresentation h hU A) (inducingRepresentation k hV B) := by
  apply MonoidHom.ext
  intro p
  apply TensorProduct.ext
  ext v w
  change ((HaarModulus.closedHalfCharacter (U.prod V) (hU.prod hV) (P.prod Q)
        (h.prod k).le_normalizer p : ℂˣ) : ℂ) •
      (Induction.BinaryTensor.inducing M N A.representation B.representation
        ((h.prod k).projection p) (v ⊗ₜ[ℂ] w)) = _
  rw [h.prod_projection k p,
      HaarModulus.closedHalfCharacter_prod U P V Q hU hV
        h.le_normalizer k.le_normalizer p]
  change (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer
        ⟨p.1.1, p.2.1⟩ : ℂˣ) : ℂ) *
      ((HaarModulus.closedHalfCharacter V hV Q k.le_normalizer
        ⟨p.1.2, p.2.2⟩ : ℂˣ) : ℂ)) •
      (A.representation (h.projection ⟨p.1.1, p.2.1⟩) v ⊗ₜ[ℂ]
        B.representation (k.projection ⟨p.1.2, p.2.2⟩) w) =
      (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer
        ⟨p.1.1, p.2.1⟩ : ℂˣ) : ℂ) •
        A.representation (h.projection ⟨p.1.1, p.2.1⟩) v) ⊗ₜ[ℂ]
      (((HaarModulus.closedHalfCharacter V hV Q k.le_normalizer
        ⟨p.1.2, p.2.2⟩ : ℂˣ) : ℂ) •
        B.representation (k.projection ⟨p.1.2, p.2.2⟩) w)
  exact (TensorProduct.smul_tmul_smul _ _ _ _).symm

/-- The identity on coefficient tensors intertwines the proved equal actions. -/
def productInducingEquiv :
    Representation.Equiv
      (Induction.BinaryTensor.inducing P Q
        (inducingRepresentation h hU A) (inducingRepresentation k hV B))
      (inducingRepresentation (h.prod k) (hU.prod hV) (productLeviObject A B)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) (by
    intro p
    change Induction.BinaryTensor.inducing P Q
        (inducingRepresentation h hU A) (inducingRepresentation k hV B) p =
      inducingRepresentation (h.prod k) (hU.prod hV) (productLeviObject A B) p
    exact congrArg (fun ρ : Representation ℂ (P.prod Q) (A ⊗[ℂ] B) => ρ p)
      (product_inducingRepresentation h k hU hV A B).symm)

variable [CompactSpace (Induction.LeftQuotient P)]
  [CompactSpace (Induction.LeftQuotient Q)]

set_option maxHeartbeats 800000 in
/-- The actual normalized product induction is the tensor of the two actual
normalized inductions. No product modulus or induction equivalence is assumed. -/
def normalizedProductInductionTensorEquiv :
    Representation.Equiv
      (Induction.BinaryTensor.external
        ((normalizedInductionFunctor h hU).obj A).representation
        ((normalizedInductionFunctor k hV).obj B).representation)
      ((normalizedInductionFunctor (h.prod k) (hU.prod hV)).obj
        (productLeviObject A B)).representation :=
  (Induction.BinaryTensor.equiv P Q
    (inducingRepresentation h hU A) (inducingRepresentation k hV B)).trans
    (Induction.smoothInducedEquiv (P.prod Q) (productInducingEquiv h k hU hV A B))

/-- On pure tensors, the comparison is the pointwise tensor of the two
normalized induced functions. -/
@[simp]
theorem normalizedProductInductionTensorEquiv_tmul_eval
    (f : (normalizedInductionFunctor h hU).obj A)
    (j : (normalizedInductionFunctor k hV).obj B) (x : G × H) :
    Induction.eval (P.prod Q)
        (inducingRepresentation (h.prod k) (hU.prod hV) (productLeviObject A B))
        (normalizedProductInductionTensorEquiv h k hU hV A B (f ⊗ₜ[ℂ] j)) x =
      Induction.eval P (inducingRepresentation h hU A) f x.1 ⊗ₜ[ℂ]
        Induction.eval Q (inducingRepresentation k hV B) j x.2 :=
  Induction.BinaryTensor.equiv_tmul_eval P Q
    (inducingRepresentation h hU A) (inducingRepresentation k hV B) f j x

end Normalized

end Langlands.Plancherel
