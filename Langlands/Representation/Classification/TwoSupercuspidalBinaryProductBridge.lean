import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement

/-!
# Binary products in the two-supercuspidal argument

Unconditional comparisons between the all-rank binary normalized product
`T.binaryNormalizedProductFunctor a b` and the objects used by the
two-supercuspidal irreducibility argument:

* for positive ranks, the binary product of `(A, B)` is the normalized product
  on the standard two-block shape `Shahidi.twoBlocks a c` of `twoBlockFactors A B`;
* a product with a zero factor is zero, also after a rank cast;
* a product with a one-dimensional factor on a rank-zero group is equivalent to
  the rank cast of the other factor;
* the product of two one-dimensional factors on rank-zero groups is
  one-dimensional.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.Classification.BinaryProductBridge

open GeneralLinear BinaryTensor Derivative

universe uF uV

/-- The published binary shape is the standard two-block shape. -/
theorem binary_eq_twoBlocks {a c : ℕ} (ha : 0 < a) (hc : 0 < c) :
    BlockShape.binary a c ha hc = Shahidi.twoBlocks a c ha hc := by
  unfold BlockShape.binary Shahidi.twoBlocks
  congr 1
  funext i
  fin_cases i <;> rfl

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Normalized products on equal shapes agree on heterogeneously equal factors. -/
theorem normalizedProductInductionFunctor_obj_congr {n : ℕ} {B B' : BlockShape n}
    (h : B = B')
    (X : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B'.size i) F.Carrier))
    (hXY : HEq X Y) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj X =
      (T.normalizedProductInductionFunctor B').obj Y := by
  subst h
  cases hXY
  rfl

/-- For positive ranks, the binary product of `(A, B)` is the normalized product
of `twoBlockFactors A B` on the standard two-block shape. -/
theorem binaryNormalizedProductFunctor_obj_eq_twoBlocks {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear c F.Carrier)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor a c).obj (A, B) =
      (T.normalizedProductInductionFunctor (Shahidi.twoBlocks a c ha hc)).obj
        (twoBlockFactors ha hc A B) := by
  let _ := T.topology
  rw [T.binaryNormalizedProductFunctor_of_pos ha hc]
  change (T.normalizedProductInductionFunctor (BlockShape.binary a c ha hc)).obj
      ((T.binaryPairFamilyFunctor ha hc).obj (A, B)) = _
  apply normalizedProductInductionFunctor_obj_congr F T (binary_eq_twoBlocks ha hc)
  apply Function.hfunext rfl
  intro i i' hi
  cases hi
  fin_cases i <;> rfl

/-- A zero smooth representation has a subsingleton carrier. -/
theorem subsingleton_of_isZero {n : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hA : letI := T.topology; IsZero A) : Subsingleton A := by
  let _ := T.topology
  refine ⟨fun v w => ?_⟩
  have h0 : ∀ u : A, u = 0 := fun u =>
    congrArg (fun φ => SmoothRep.hom φ u) (hA.eq_of_src (𝟙 A) 0)
  rw [h0 v, h0 w]

/-- A smooth representation with a subsingleton carrier is zero. -/
theorem isZero_of_subsingleton {n : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hA : Subsingleton A) : letI := T.topology; IsZero A := by
  let _ := T.topology
  rw [IsZero.iff_id_eq_zero]
  ext v
  exact Subsingleton.elim _ _

/-- Rank casts preserve subsingleton carriers. -/
theorem subsingleton_rankCast {a b : ℕ} (h : a = b)
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    (hA : Subsingleton A) : Subsingleton ((generalLinearRankCast T h).obj A) := by
  subst h
  exact hA

/-- A rank-cast product with a subsingleton factor has a subsingleton carrier. -/
theorem subsingleton_rankCast_product {a b m : ℕ} (h : a + b = m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hAB : Subsingleton A ∨ Subsingleton B) :
    Subsingleton ((generalLinearRankCast T h).obj ((T.binaryNormalizedProductFunctor a b).obj
      (A, B))) := by
  let _ := T.topology
  apply subsingleton_rankCast
  apply subsingleton_of_isZero
  apply T.isZero_binaryNormalizedProductFunctor_obj
  rcases hAB with hA | hB
  · exact Or.inl (isZero_of_subsingleton F T hA)
  · exact Or.inr (isZero_of_subsingleton F T hB)

/-- A one-dimensional representation of `GL_0` is isomorphic to the unit. -/
theorem nonempty_iso_unit
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) :
    letI := T.topology; Nonempty (Z ≅ T.binaryProductUnit) := by
  let _ := T.topology
  have : Module.Finite ℂ Z := Module.finite_of_finrank_eq_succ hZ
  have : Module.Finite ℂ (T.binaryProductUnit.{uF, uV}) :=
    Module.finite_of_finrank_eq_succ (T.finrank_binaryProductUnit)
  let e : Z ≃ₗ[ℂ] T.binaryProductUnit.{uF, uV} :=
    LinearEquiv.ofFinrankEq _ _ (hZ.trans T.finrank_binaryProductUnit.symm)
  refine ⟨SmoothRep.mkIso (Representation.Equiv.mk e fun g => ?_)⟩
  rw [representation_apply_of_rank_eq_zero rfl Z.representation g,
    representation_apply_of_rank_eq_zero rfl (T.binaryProductUnit.{uF, uV}).representation g]
  rfl

/-- The rank cast of `B` is `B` composed with the entry-preserving reindex. -/
def rankCastEquiv {b c : ℕ} (h : b = c)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (B.representation.comp (reindex (R := F.Carrier) (finCongr h.symm)).toMonoidHom)
      ((generalLinearRankCast T h).obj B).representation := by
  let _ := T.topology
  subst h
  exact Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => by
    change B.representation (reindex (R := F.Carrier) (finCongr rfl) g) = B.representation g
    rw [reindex_finCongr_rfl]
    rfl

/-- A product `A × Z` with a one-dimensional factor `Z` on a rank-zero group is
equivalent, after rank casts, to `A`. -/
theorem nonempty_equiv_rankCast_product_right {a b m : ℕ} (hb : b = 0) (h : a + b = m)
    (h' : a = m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) :
    letI := T.topology
    Nonempty (((generalLinearRankCast T h').obj A).representation.Equiv
      ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, Z))).representation) := by
  let _ := T.topology
  subst hb h
  obtain ⟨eZ⟩ := nonempty_iso_unit F T Z hZ
  let e1 := SmoothRep.equivOfIso
    ((T.binaryNormalizedProductFunctor a 0).mapIso (Iso.prod (Iso.refl A) eZ))
  let e2 := T.binaryProductRightUnitEquiv A
  let e3 := rankCastEquiv F T (Nat.add_zero a).symm A
  exact ⟨((e3.symm.trans (liftEquiv _)).trans e2.symm).trans e1.symm⟩

/-- A product `Z × B` with a one-dimensional factor `Z` on a rank-zero group is
equivalent, after rank casts, to `B`. -/
theorem nonempty_equiv_rankCast_product_left {a b m : ℕ} (ha : a = 0) (h : a + b = m)
    (h' : b = m)
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) :
    letI := T.topology
    Nonempty (((generalLinearRankCast T h').obj B).representation.Equiv
      ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (Z, B))).representation) := by
  let _ := T.topology
  subst ha h
  obtain ⟨eZ⟩ := nonempty_iso_unit F T Z hZ
  let e1 := SmoothRep.equivOfIso
    ((T.binaryNormalizedProductFunctor 0 b).mapIso (Iso.prod eZ (Iso.refl B)))
  let e2 := T.binaryProductLeftUnitEquiv B
  let e3 := rankCastEquiv F T h' B
  exact ⟨((e3.symm.trans (liftEquiv _)).trans e2.symm).trans e1.symm⟩

/-- The product of two one-dimensional representations of rank-zero groups is
one-dimensional, also after a rank cast. -/
theorem finrank_rankCast_product_of_zero_zero {a b m : ℕ} (ha : a = 0) (hb : b = 0)
    (h : a + b = m)
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (Z' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) (hZ' : Module.finrank ℂ Z' = 1) :
    Module.finrank ℂ ((generalLinearRankCast T h).obj
      ((T.binaryNormalizedProductFunctor a b).obj (Z, Z'))) = 1 := by
  let _ := T.topology
  subst h
  change Module.finrank ℂ ((T.binaryNormalizedProductFunctor a b).obj (Z, Z')) = 1
  rw [(T.binaryZeroZeroTensorEquiv ha hb (Z, Z')).toLinearEquiv.finrank_eq]
  change Module.finrank ℂ (Z ⊗[ℂ] Z') = 1
  rw [Module.finrank_tensorProduct, hZ, hZ']

end Langlands.Classification.BinaryProductBridge
