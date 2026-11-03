import Langlands.GroupScheme.TriangularCoordinates
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.Global.AdelicGroupQuotient
import Langlands.Global.AdeleQuotientCompactProof

/-!
# Compactness of `U(F) \ U(𝔸_F)` for groups with triangular coordinates

Let `U` be an affine group scheme over a number field `F` with triangular polynomial
coordinates (`Langlands.GroupScheme.HasTriangularCoordinates`). Then some compact set of
adelic points meets every rational coset. Hence the actual rational quotient
`RationalQuotient F U = U(F) \ U(𝔸_F)` is compact. Combined with the algebraic statement
`UnipotentTriangularCoordinatesStatement`, this gives compactness for every smooth connected
unipotent `U`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology
open IsDedekindDomain.HeightOneSpectrum
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.Global.AdelicGroupPoints

section Adeles

variable (F : Type u) [Field F] [NumberField F]

/-- `𝔸_F = F + D` for a compact set `D`: every adele can be moved into `D` by adding a
principal adele. -/
theorem exists_isCompact_algebraMap_add_mem :
    ∃ D : Set (AdeleRing (𝓞 F) F), IsCompact D ∧
      ∀ a : AdeleRing (𝓞 F) F, ∃ f : F, algebraMap F (AdeleRing (𝓞 F) F) f + a ∈ D := by
  set C : Set (Adeles F) := archimedeanFundamentalSet F ×ˢ
    (integralFiniteAdeles F : Set (FiniteAdeles F))
  refine ⟨C, (isCompact_archimedeanFundamentalSet F).prod (isCompact_integralFiniteAdeles F),
    fun a => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_integralFiniteAdeles a.2
  obtain ⟨y, hy⟩ := exists_sub_integer_mem_archimedeanFundamentalSet F
    (a.1 - algebraMap F (InfiniteAdeles F) x)
  have hyf : algebraMap F (FiniteAdeles F) (y : F) ∈ integralFiniteAdeles F :=
    (mem_integralFiniteAdeles F _).mpr fun v ↦ coe_mem_adicCompletionIntegers v y
  refine ⟨-(x + (y : F)), ?_, ?_⟩
  · change algebraMap F (InfiniteAdeles F) (-(x + (y : F))) + a.1 ∈ archimedeanFundamentalSet F
    rw [map_neg, map_add, neg_add_eq_sub, ← sub_sub]
    exact hy
  · change algebraMap F (FiniteAdeles F) (-(x + (y : F))) + a.2 ∈ integralFiniteAdeles F
    rw [map_neg, map_add, neg_add_eq_sub, ← sub_sub]
    exact (integralFiniteAdeles F).sub_mem hx hyf

end Adeles

section Triangular

variable {F : Type u} [Field F]

/-- A polynomial takes the same value at two points that agree on its variables. -/
theorem aeval_eq_of_forall_mem_vars {σ A : Type*} [CommRing A] [Algebra F A]
    {g₁ g₂ : σ → A} {p : MvPolynomial σ F} (h : ∀ v ∈ p.vars, g₁ v = g₂ v) :
    MvPolynomial.aeval g₁ p = MvPolynomial.aeval g₂ p :=
  MvPolynomial.eval₂Hom_congr' rfl (fun v hv _ => h v hv) rfl

/-- **Triangular solving.** If `F + D = A` and each `P i` involves only variables of index
`< i`, then for every `a : Fin d → A` there are rational `c : Fin d → F` with
`c i + a i + P i (c, a) ∈ D` for all `i`. The values `c i` are chosen by induction on `i`. -/
theorem exists_triangular_translate {A : Type*} [CommRing A] [Algebra F A] {d : ℕ}
    (P : Fin d → MvPolynomial (Fin d ⊕ Fin d) F)
    (hP : ∀ i, ∀ v ∈ (P i).vars, Sum.elim id id v < i) {D : Set A}
    (hD : ∀ a : A, ∃ f : F, algebraMap F A f + a ∈ D) (a : Fin d → A) :
    ∃ c : Fin d → F, ∀ i, algebraMap F A (c i) + a i +
      MvPolynomial.aeval (Sum.elim (fun j => algebraMap F A (c j)) a) (P i) ∈ D := by
  suffices h : ∀ k ≤ d, ∃ c : Fin d → F, ∀ i : Fin d, (i : ℕ) < k →
      algebraMap F A (c i) + a i +
        MvPolynomial.aeval (Sum.elim (fun j => algebraMap F A (c j)) a) (P i) ∈ D by
    obtain ⟨c, hc⟩ := h d le_rfl
    exact ⟨c, fun i => hc i i.isLt⟩
  intro k
  induction k with
  | zero => exact fun _ => ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨c, hc⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨f, hf⟩ := hD (a ⟨k, hk⟩ +
      MvPolynomial.aeval (Sum.elim (fun j => algebraMap F A (c j)) a) (P ⟨k, hk⟩))
    refine ⟨Function.update c ⟨k, hk⟩ f, fun i hi => ?_⟩
    have hcongr :
        MvPolynomial.aeval (Sum.elim (fun j => algebraMap F A (Function.update c ⟨k, hk⟩ f j)) a)
            (P i) =
          MvPolynomial.aeval (Sum.elim (fun j => algebraMap F A (c j)) a) (P i) := by
      apply aeval_eq_of_forall_mem_vars
      intro v hv
      have hlt := hP i v hv
      rcases v with j | j
      · have hj : j ≠ ⟨k, hk⟩ := by
          rintro rfl
          have : k < (i : ℕ) := hlt
          omega
        simp only [Sum.elim_inl, Function.update_of_ne hj]
      · rfl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · have hne : i ≠ ⟨k, hk⟩ := fun h => by
        rw [h] at hi
        exact lt_irrefl _ hi
      rw [hcongr, Function.update_of_ne hne]
      exact hc i hi
    · obtain rfl : i = ⟨k, hk⟩ := Fin.ext hi
      rw [hcongr, Function.update_self, add_assoc]
      exact hf

variable (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left]

/-- If global functions `t` identify the coordinate ring with a polynomial ring, then every
`c : Fin d → F` is the coordinate vector of a rational point. -/
theorem exists_rationalPoint_evaluation {d : ℕ} {t : Fin d → AffineCoordinateRing F U.X}
    (ht : Function.Bijective
      (MvPolynomial.aeval t : MvPolynomial (Fin d) F →ₐ[F] AffineCoordinateRing F U.X))
    (c : Fin d → F) :
    ∃ γ : U.affinePoints (CommAlgCat.of F F),
      ∀ i, U.affinePointEvaluation (CommAlgCat.of F F) γ (t i) = c i := by
  let e := AlgEquiv.ofBijective _ ht
  let φ : AffineCoordinateRing F U.X →ₐ[F] F := (MvPolynomial.aeval c).comp e.symm.toAlgHom
  refine ⟨(affineSchemePointEquiv F U.X F).symm (AlgPoint.ofAlgHom φ), fun i => ?_⟩
  have h := U.affineSchemePointEquiv_evaluation (CommAlgCat.of F F)
    ((affineSchemePointEquiv F U.X F).symm (AlgPoint.ofAlgHom φ)) (t i)
  rw [Equiv.apply_symm_apply, AlgPoint.ofAlgHom_apply] at h
  rw [← h]
  have he : e.symm (t i) = MvPolynomial.X i :=
    e.symm_apply_eq.mpr (MvPolynomial.aeval_X t i).symm
  simp [φ, he]

end Triangular

section Quotient

variable {F : Type u} [Field F] [NumberField F]
  (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left]

omit [IsAffine U.X.left] in
/-- The principal adelic image of a rational point has the principal images of its
coordinates as coordinates. -/
theorem affinePointEvaluation_rational (γ : RationalGroupPoints F U)
    (a : Γ(U.X.left, ⊤)) :
    U.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (rational F U γ) a =
      algebraMap F (AdeleRing (𝓞 F) F) (U.affinePointEvaluation (CommAlgCat.of F F) γ a) := by
  rw [rational, affinePointEvaluation_map]
  rfl

/-- **A compact set meeting every rational coset.** For an affine group scheme with
triangular coordinates over a number field, some compact `K ⊆ U(𝔸_F)` satisfies: every
`x ∈ U(𝔸_F)` has a rational `γ` with `γ * x ∈ K`. -/
theorem exists_isCompact_rational_mul_mem (hU : HasTriangularCoordinates U) :
    ∃ K : Set (AdelicGroupPoints F U), IsCompact K ∧
      ∀ x : AdelicGroupPoints F U, ∃ γ ∈ rationalSubgroup F U, γ * x ∈ K := by
  obtain ⟨d, t, P, ht, hP, hmul⟩ := hU
  obtain ⟨D, hDc, hD⟩ := exists_isCompact_algebraMap_add_mem F
  let Φ : AdelicGroupPoints F U → (Fin d → AdeleRing (𝓞 F) F) :=
    fun x i => U.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x (t i)
  have hgen : Algebra.adjoin (CommRingCat.of F) (Set.range t) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).mpr ht.2
  have hΦ : IsClosedEmbedding Φ := by
    let : T2Space (InfiniteAdeleRing F) :=
      inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
    let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
      inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
        [FiniteCompletion F v, v.adicCompletionIntegers F]))
    let : T2Space (AdeleRing (𝓞 F) F) :=
      inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    exact U.isClosedEmbedding_affinePointFiniteEvaluation
      (CommAlgCat.of F (AdeleRing (𝓞 F) F)) d t hgen
  refine ⟨Φ ⁻¹' Set.univ.pi fun _ => D,
    hΦ.isCompact_preimage (isCompact_univ_pi fun _ => hDc), fun x => ?_⟩
  obtain ⟨c, hc⟩ := exists_triangular_translate P hP hD (Φ x)
  obtain ⟨γ, hγ⟩ := exists_rationalPoint_evaluation U ht c
  have hγA : ∀ j, U.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F))
      (rational F U γ) (t j) = algebraMap F (AdeleRing (𝓞 F) F) (c j) := fun j => by
    exact (affinePointEvaluation_rational U γ (t j)).trans (congrArg _ (hγ j))
  refine ⟨rational F U γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩,
    Set.mem_preimage.mpr (Set.mem_univ_pi.mpr fun i => ?_)⟩
  change U.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F))
    (rational F U γ * x) (t i) ∈ D
  rw [hmul]
  simp_rw [hγA]
  exact hc i

/-- `exists_isCompact_rational_mul_mem` in the form of compactness of `U(F) \ U(𝔸_F)`. -/
theorem compactSpace_rationalQuotient_of_hasTriangularCoordinates
    (hU : HasTriangularCoordinates U) : CompactSpace (RationalQuotient F U) := by
  obtain ⟨K, hK, hcover⟩ := exists_isCompact_rational_mul_mem U hU
  have himage : LeftCosetSpace.mk (rationalSubgroup F U) '' K = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    obtain ⟨γ, hγ, hγx⟩ := hcover x
    exact ⟨γ * x, hγx, LeftCosetSpace.mk_subgroup_mul _ ⟨γ, hγ⟩ x⟩
  exact isCompact_univ_iff.mp (himage ▸ hK.image (LeftCosetSpace.continuous_mk _))

end Quotient

/-- Compactness of `U(F) \ U(𝔸_F)` for every affine group scheme `U` with triangular
coordinates over a number field `F`. -/
def TriangularRationalQuotientCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine U.X.left], HasTriangularCoordinates U → CompactSpace (RationalQuotient F U)

/-- **Compactness for unipotent groups.** For every smooth connected unipotent affine group
scheme `U` of finite type over a number field `F`, `U(F) \ U(𝔸_F)` is compact. -/
def UnipotentRationalQuotientCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom],
    Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
      CompactSpace (RationalQuotient F U)

/-- The adelic half is proved: triangular coordinates give a compact rational quotient. -/
theorem triangularRationalQuotientCompact : TriangularRationalQuotientCompactStatement.{u} :=
  fun _ _ _ U _ hU => compactSpace_rationalQuotient_of_hasTriangularCoordinates U hU

/-- The algebraic triangular-coordinate statement implies compactness for unipotent groups. -/
theorem unipotentRationalQuotientCompact_of_triangularCoordinates
    (h : UnipotentTriangularCoordinatesStatement.{u}) :
    UnipotentRationalQuotientCompactStatement.{u} :=
  fun F _ _ U _ _ hs hc hu => triangularRationalQuotientCompact F U (h F U hs hc hu)

/-- The covering form of `unipotentRationalQuotientCompact_of_triangularCoordinates`: a
compact set of adelic points meeting every rational coset. -/
theorem exists_isCompact_rational_mul_mem_of_isUnipotent
    (h : UnipotentTriangularCoordinatesStatement.{u})
    (F : Type u) [Field F] [NumberField F] (U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
    (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U) :
    ∃ K : Set (AdelicGroupPoints F U), IsCompact K ∧
      ∀ x : AdelicGroupPoints F U, ∃ γ ∈ rationalSubgroup F U, γ * x ∈ K :=
  exists_isCompact_rational_mul_mem U (h F U hs hc hu)

end Langlands.Global.AdelicGroupPoints
