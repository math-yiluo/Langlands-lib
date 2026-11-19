import Langlands.Geometry.Analytic.FinitePieceEngine
import Langlands.Geometry.Analytic.FiniteAlgebraNormedModel
import Langlands.Geometry.Analytic.FinitePieceLocalAlgebra
import Langlands.Geometry.Analytic.FiniteBoundedMaps
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.AffineAnalytificationFinitePieceLocalStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian

/-! # Proof of the local structure of the finite pieces of an affine analytification map -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification.FinitePieceLocal

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace IndexedAffinoidAtlas
open scoped TensorProduct

/-- Two ring maps out of a tensor product of commutative algebras agree if they agree on
both legs. -/
theorem tensor_ringHom_ext {A R B T : Type*} [CommRing A] [CommRing R] [CommRing B] [Ring T]
    [Algebra A R] [Algebra A B] (ψ ψ' : R ⊗[A] B →+* T)
    (h₁ : ∀ x, ψ (x ⊗ₜ 1) = ψ' (x ⊗ₜ 1)) (h₂ : ∀ b, ψ (1 ⊗ₜ b) = ψ' (1 ⊗ₜ b)) : ψ = ψ' := by
  refine RingHom.ext fun c => ?_
  induction c using TensorProduct.inductionOn with
  | tmul x b =>
    have e : x ⊗ₜ[A] b = (x ⊗ₜ 1) * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h₁, h₂]
  | add c c' hc hc' => rw [map_add, map_add, hc, hc']

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

omit [IsUltrametricDist K] [CompleteSpace K] in
include Q in
/-- Base changes of `B` along `A`-algebras are of finite type. -/
theorem finiteType_tensor (R : Type*) [CommRing R] [Algebra A R] [Algebra A B]
    (hf : ∀ a, algebraMap A B a = f a) : Algebra.FiniteType R (R ⊗[A] B) := by
  have : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun c => by
    rw [hf, f.commutes]
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
  infer_instance

section Piece

variable (V : Set (presentation K Q).space) (hVo : IsOpen V)
  (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
  (V' : (presentation K Q).atlas.saturatedAtlas.RecognizedSubset)
  (h : (saturatedHom K P Q f).baseMap '' range V'.chart ⊆ range W.chart)
  (hV' : V'.locus = V ∩ (saturatedHom K P Q f).baseMap ⁻¹' W.locus)
  (j₀ : (presentation K P).atlas.saturatedAtlas.Index)
  (hW₀ : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j₀))
  (i₀ : (presentation K Q).atlas.saturatedAtlas.Index)
  (hV₀ : V'.locus ⊆ range ((presentation K Q).atlas.saturatedAtlas.chart i₀))
  [Algebra A W.algebra] (hα : ∀ a, algebraMap A W.algebra a = recMap P W j₀ hW₀ a)
  [Algebra A B] (hf : ∀ a, algebraMap A B a = f a)
  (χ : W.algebra ⊗[A] B →+* V'.algebra)
  (hχ₁ : ∀ x, χ (x ⊗ₜ 1) = (saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h x)
  (hχ₂ : ∀ b, χ (1 ⊗ₜ b) = recMap Q V' i₀ hV₀ b)

include hVo hV' hα hf hχ₁ hχ₂

/-- Test maps out of `W.algebra ⊗[A] B`. A ring map `τ` to a complete ultrametric normed
`K`-algebra that is bounded on `W.algebra` factors through an affinoid algebra `D` that maps
onto `V'.algebra` by the restriction `ρ` to an idempotent. Bounded maps out of `D` are
determined by their composites with `κ`. -/
theorem exists_test_comparison
    (E : Type*) [NormedCommRing E] [NormedAlgebra K E] [IsUltrametricDist E] [CompleteSpace E]
    (τR : BoundedAlgHom K W.algebra E) (τ : W.algebra ⊗[A] B →+* E)
    (hτ : ∀ x, τ (x ⊗ₜ 1) = τR x) :
    ∃ (D : PresentedAffinoidAlgebra K) (κ : W.algebra ⊗[A] B →+* D)
      (ρ : BoundedAlgHom K D V'.algebra) (θ : BoundedAlgHom K D E) (e : D),
      (∀ c, ρ (κ c) = χ c) ∧ (∀ c, θ (κ c) = τ c) ∧
      IsIdempotentElem e ∧ ρ e = 1 ∧ (∀ x, ρ x = 0 → e * x = 0) ∧
      Function.Surjective ρ ∧
      ∀ (E' : Type u) [NormedCommRing E'] [NormedAlgebra K E'] (ψ ψ' : BoundedAlgHom K D E'),
        (∀ c, ψ (κ c) = ψ' (κ c)) → ψ = ψ' := by
  have hKB : ∀ c : K,
      (1 : W.algebra) ⊗ₜ[A] algebraMap K B c = algebraMap K W.algebra c ⊗ₜ 1 := by
    intro c
    rw [← f.commutes, ← hf, ← Algebra.TensorProduct.tmul_one_eq_one_tmul, hα, AlgHom.commutes]
  let τB : B →ₐ[K] E :=
    { toFun := fun b => τ (1 ⊗ₜ b)
      map_one' := by
        change τ (1 ⊗ₜ 1) = 1
        rw [← Algebra.TensorProduct.one_def, map_one]
      map_mul' := fun b b' => by
        change τ (1 ⊗ₜ (b * b')) = τ (1 ⊗ₜ b) * τ (1 ⊗ₜ b')
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      map_zero' := by
        change τ (1 ⊗ₜ 0) = 0
        rw [TensorProduct.tmul_zero, map_zero]
      map_add' := fun b b' => by
        change τ (1 ⊗ₜ (b + b')) = τ (1 ⊗ₜ b) + τ (1 ⊗ₜ b')
        rw [TensorProduct.tmul_add, map_add]
      commutes' := fun c => by
        change τ (1 ⊗ₜ algebraMap K B c) = algebraMap K E c
        rw [hKB, hτ]
        exact τR.toAlgHom.commutes c }
  have hτB : ∀ a, τB (f a) = τR (recMap P W j₀ hW₀ a) := by
    intro a
    change τ (1 ⊗ₜ f a) = τR (recMap P W j₀ hW₀ a)
    rw [← hf, ← Algebra.TensorProduct.tmul_one_eq_one_tmul, hα, hτ]
  obtain ⟨D, r, bm, ρ, θ, e, hρr, hρb, hθr, hθb, hrb, he, hρe, he0, hρs, huniq⟩ :=
    exists_test_factorization P Q f V hVo W V' h hV' j₀ hW₀ i₀ hV₀ E τR τB hτB
  let _ : Algebra A D := (r.toAlgHom.toRingHom.comp (algebraMap A W.algebra)).toAlgebra
  let rA : W.algebra →ₐ[A] D := { r.toAlgHom.toRingHom with commutes' := fun _ => rfl }
  let bA : B →ₐ[A] D :=
    { bm.toRingHom with
      commutes' := fun a => by
        change bm (algebraMap A B a) = r (algebraMap A W.algebra a)
        rw [hf, hα]
        exact (hrb a).symm }
  let κ : W.algebra ⊗[A] B →+* D :=
    (Algebra.TensorProduct.lift rA bA fun _ _ => Commute.all _ _).toRingHom
  have hκ : ∀ x b, κ (x ⊗ₜ b) = r x * bm b := fun _ _ => rfl
  have hκ₁ : ∀ x, κ (x ⊗ₜ 1) = r x := fun x => by rw [hκ, map_one, mul_one]
  have hκ₂ : ∀ b, κ (1 ⊗ₜ b) = bm b := fun b => by
    rw [hκ]
    exact (congrArg (· * bm b) (map_one r.toAlgHom)).trans (one_mul _)
  refine ⟨D, κ, ρ, θ, e, fun c => ?_, fun c => ?_, he, hρe, he0, hρs, ?_⟩
  · have := tensor_ringHom_ext (ρ.toAlgHom.toRingHom.comp κ) χ
      (fun x => by
        change ρ (κ (x ⊗ₜ 1)) = χ (x ⊗ₜ 1)
        rw [hκ₁, hρr, hχ₁])
      (fun b => by
        change ρ (κ (1 ⊗ₜ b)) = χ (1 ⊗ₜ b)
        rw [hκ₂, hρb, hχ₂])
    exact congrArg (fun q => q c) this
  · have := tensor_ringHom_ext (θ.toAlgHom.toRingHom.comp κ) τ
      (fun x => by
        change θ (κ (x ⊗ₜ 1)) = τ (x ⊗ₜ 1)
        rw [hκ₁, hθr, hτ])
      (fun b => by
        change θ (κ (1 ⊗ₜ b)) = τ (1 ⊗ₜ b)
        rw [hκ₂, hθb]
        rfl)
    exact congrArg (fun q => q c) this
  · intro E' _ _ ψ ψ' hψ
    apply huniq E' ψ ψ'
    · intro x
      have := hψ (x ⊗ₜ 1)
      rwa [hκ₁] at this
    · intro b
      have := hψ (1 ⊗ₜ b)
      rwa [hκ₂] at this

/-- The ring map `χ` is surjective when the piece is finite Banach. -/
theorem surjective_of_isFiniteBanach
    (hφ : ((saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h).IsFiniteBanach) :
    Function.Surjective χ := by
  set φ := (saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h with hφdef
  let _ : Algebra W.algebra V'.algebra := φ.toAlgHom.toRingHom.toAlgebra
  have : Module.Finite W.algebra V'.algebra := hφ.finite
  let S₀ : Subalgebra W.algebra V'.algebra :=
    { carrier := Set.range χ
      mul_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        exact ⟨c * c', map_mul χ c c'⟩
      one_mem' := ⟨1, map_one χ⟩
      add_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        exact ⟨c + c', map_add χ c c'⟩
      zero_mem' := ⟨0, map_zero χ⟩
      algebraMap_mem' := fun x => ⟨x ⊗ₜ 1, hχ₁ x⟩ }
  have : Module.Finite W.algebra S₀ :=
    Module.Finite.of_injective S₀.val.toLinearMap Subtype.val_injective
  let E := FiniteNormedModel.Model K W.algebra S₀
  let τ : W.algebra ⊗[A] B →+* E :=
    (FiniteNormedModel.ofModel K W.algebra S₀).symm.toAlgHom.toRingHom.comp
      (χ.codRestrict S₀ fun c => ⟨c, rfl⟩)
  have hτ : ∀ x, τ (x ⊗ₜ 1) = FiniteNormedModel.baseHom K W.algebra S₀ x := fun x =>
    (FiniteNormedModel.ofModel K W.algebra S₀).injective (Subtype.ext (hχ₁ x))
  obtain ⟨D, κ, ρ, θ, e, hρκ, hθκ, -, -, -, hρs, huniq⟩ :=
    exists_test_comparison P Q f V hVo W V' h hV' j₀ hW₀ i₀ hV₀ hα hf χ hχ₁ hχ₂ E
      (FiniteNormedModel.baseHom K W.algebra S₀) τ hτ
  have hfin : (FiniteNormedModel.baseHom K W.algebra S₀).toAlgHom.toRingHom.Finite := by
    change (algebraMap W.algebra E).Finite
    exact RingHom.finite_algebraMap.2 (inferInstanceAs (Module.Finite W.algebra S₀))
  let ιK : E →ₐ[K] V'.algebra :=
    { toFun := fun z => (FiniteNormedModel.ofModel K W.algebra S₀ z : V'.algebra)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun c => φ.toAlgHom.commutes c }
  let ι : BoundedAlgHom K E V'.algebra :=
    BoundedAlgHom.ofFiniteTriangle (FiniteNormedModel.baseHom K W.algebra S₀) hfin φ ιK
      (AlgHom.ext fun _ => rfl)
  have hιθ : ι.comp θ = ρ := huniq V'.algebra (ι.comp θ) ρ fun c => by
    change ι (θ (κ c)) = ρ (κ c)
    rw [hθκ, hρκ]
    rfl
  intro z
  obtain ⟨d, rfl⟩ := hρs z
  have hd : ρ d = ι (θ d) := (congrArg (fun q => q d) hιθ).symm
  rw [hd]
  exact (FiniteNormedModel.ofModel K W.algebra S₀ (θ d)).2

/-- When the piece is finite Banach, the kernel of `χ` lies in every power of the inverse
image of every maximal ideal. -/
theorem ker_le_pow
    (hφ : ((saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h).IsFiniteBanach)
    (n : Ideal V'.algebra) (hn : n.IsMaximal) (k : ℕ) :
    RingHom.ker χ ≤ (n.comap χ) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, Ideal.one_eq_top]
    exact le_top
  have hk : k ≠ 0 := hk0.ne'
  set φ := (saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h with hφdef
  let _ : Algebra W.algebra V'.algebra := φ.toAlgHom.toRingHom.toAlgebra
  have : Module.Finite W.algebra V'.algebra := hφ.finite
  have : Algebra.FiniteType W.algebra (W.algebra ⊗[A] B) := finiteType_tensor Q f W.algebra hf
  let χR : W.algebra ⊗[A] B →ₐ[W.algebra] V'.algebra :=
    { χ with commutes' := fun x => hχ₁ x }
  set p := n.comap χ with hp
  have hmon : ∀ x : W.algebra ⊗[A] B, ∃ g : Polynomial W.algebra,
      g.Monic ∧ Polynomial.aeval x g ∈ p :=
    FinitePieceLocalAlgebra.exists_monic_aeval_mem_of_ker_le χR p fun c hc => by
      have hc' : χ c = 0 := hc
      rw [hp, Ideal.mem_comap, hc']
      exact n.zero_mem
  have : Module.Finite W.algebra (W.algebra ⊗[A] B ⧸ p ^ k) :=
    FinitePieceLocalAlgebra.finite_quotient_pow p hmon k
  let Ck := W.algebra ⊗[A] B ⧸ p ^ k
  let E := FiniteNormedModel.Model K W.algebra Ck
  let τ : W.algebra ⊗[A] B →+* E :=
    (FiniteNormedModel.ofModel K W.algebra Ck).symm.toAlgHom.toRingHom.comp
      (Ideal.Quotient.mk (p ^ k))
  have hτ : ∀ x, τ (x ⊗ₜ 1) = FiniteNormedModel.baseHom K W.algebra Ck x := fun x =>
    (FiniteNormedModel.ofModel K W.algebra Ck).injective (by
      rw [FiniteNormedModel.ofModel_baseHom]
      rfl)
  obtain ⟨D, κ, ρ, θ, e, hρκ, hθκ, he, hρe, he0, -, huniq⟩ :=
    exists_test_comparison P Q f V hVo W V' h hV' j₀ hW₀ i₀ hV₀ hα hf χ hχ₁ hχ₂ E
      (FiniteNormedModel.baseHom K W.algebra Ck) τ hτ
  have := hn
  let qn : BoundedAlgHom K V'.algebra (V'.algebra ⧸ n) :=
    { toAlgHom := Ideal.Quotient.mkₐ K n
      bounded := ⟨1, one_pos, fun x => by
        rw [one_mul]
        exact Ideal.Quotient.norm_mk_le n x⟩ }
  have hlift := FinitePieceLocalAlgebra.lift_pow_comap_aux χ n k hk
  let lam0 : Ck →+* V'.algebra ⧸ n :=
    Ideal.Quotient.lift (p ^ k) ((Ideal.Quotient.mk n).comp χ) hlift
  have hfin : (FiniteNormedModel.baseHom K W.algebra Ck).toAlgHom.toRingHom.Finite := by
    change (algebraMap W.algebra E).Finite
    exact RingHom.finite_algebraMap.2 (inferInstanceAs (Module.Finite W.algebra Ck))
  have hlamφ : ∀ x : W.algebra,
      lam0 (FiniteNormedModel.ofModel K W.algebra Ck (FiniteNormedModel.baseHom K W.algebra Ck x))
        = Ideal.Quotient.mk n (φ x) := fun x => by
    rw [← hχ₁, ← hτ]
    rfl
  let lamK : E →ₐ[K] V'.algebra ⧸ n :=
    { lam0.comp (FiniteNormedModel.ofModel K W.algebra Ck).toAlgHom.toRingHom with
      commutes' := fun c => by
        have e1 : algebraMap K E c =
            FiniteNormedModel.baseHom K W.algebra Ck (algebraMap K W.algebra c) :=
          ((FiniteNormedModel.baseHom K W.algebra Ck).toAlgHom.commutes c).symm
        change lam0 (FiniteNormedModel.ofModel K W.algebra Ck (algebraMap K E c)) = _
        rw [e1, hlamφ]
        exact (congrArg (Ideal.Quotient.mk n) (φ.toAlgHom.commutes c)).trans rfl }
  let lam : BoundedAlgHom K E (V'.algebra ⧸ n) :=
    BoundedAlgHom.ofFiniteTriangle (FiniteNormedModel.baseHom K W.algebra Ck) hfin (qn.comp φ)
      lamK (AlgHom.ext fun x => hlamφ x)
  have hcomp : lam.comp θ = qn.comp ρ := huniq _ (lam.comp θ) (qn.comp ρ) fun c => by
    change lam0 (FiniteNormedModel.ofModel K W.algebra Ck (θ (κ c))) = qn (ρ (κ c))
    rw [hθκ, hρκ]
    rfl
  have hθe : θ e = 1 := by
    have h1 : lam0 (FiniteNormedModel.ofModel K W.algebra Ck (θ e)) = 1 := by
      have h2 := congrArg (fun q : BoundedAlgHom K D (V'.algebra ⧸ n) => q e) hcomp
      change lam0 (FiniteNormedModel.ofModel K W.algebra Ck (θ e)) = qn (ρ e) at h2
      rw [h2, hρe]
      exact map_one qn.toAlgHom
    have hu := FinitePieceLocalAlgebra.isUnit_of_lift_eq_one χ n k hlift _ h1
    have hid : IsIdempotentElem (FiniteNormedModel.ofModel K W.algebra Ck (θ e)) := by
      change _ * _ = _
      rw [← map_mul, ← map_mul θ.toAlgHom]
      change FiniteNormedModel.ofModel K W.algebra Ck (θ (e * e)) = _
      rw [he.eq]
    have h3 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).1 hid
    exact (FiniteNormedModel.ofModel K W.algebra Ck).injective (h3.trans (map_one _).symm)
  intro c hc
  have hχc : χ c = 0 := hc
  have h0 : e * κ c = 0 := he0 _ (by rw [hρκ, hχc])
  have hτc : τ c = 0 := by
    rw [← hθκ, ← one_mul (θ (κ c)), ← hθe]
    change θ.toAlgHom e * θ.toAlgHom (κ c) = 0
    rw [← map_mul, h0, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 hτc

end Piece

/-- The local structure of the finite pieces of an affine analytification map, given
flatness of the chart algebras over the coordinate algebra and of the structural maps of
affinoid domains. -/
theorem affineAnalytificationFinitePieceLocal
    (hchart : AffineAnalytificationChartFlatStatement.{u, v})
    (hdom : Domain.FlatnessStatement.{u}) :
    AffineAnalytificationFinitePieceLocalStatement.{u, v, w} := by
  intro K _ _ _ A _ _ B _ _ P Q f V U g hVo _ _ W _ V' h hV' hφ
  -- Saturated charts containing the two loci, with `g` mapping the first into the second.
  obtain ⟨m₂, hm₂⟩ := exists_orig_superset Q (isCompact_recognized_locus V')
  let i₀ := origIndex Q (representative K Q m₂)
  have hV₀ : V'.locus ⊆ range ((presentation K Q).atlas.saturatedAtlas.chart i₀) :=
    hm₂ m₂ le_rfl
  have hZ : IsCompact (W.locus ∪ (saturatedHom K P Q f).baseMap ''
      range ((presentation K Q).atlas.saturatedAtlas.chart i₀)) :=
    (isCompact_recognized_locus W).union ((isCompact_range
      ((presentation K Q).atlas.saturatedAtlas.isEmbedding_chart i₀).continuous).image
        (saturatedHom K P Q f).baseMap.continuous)
  obtain ⟨m₃, hm₃⟩ := exists_orig_superset P hZ
  let j₀ := origIndex P (representative K P m₃)
  have hjZ := hm₃ m₃ le_rfl
  have hW₀ : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j₀) :=
    subset_union_left.trans hjZ
  have hij : (saturatedHom K P Q f).baseMap ''
      range ((presentation K Q).atlas.saturatedAtlas.chart i₀) ⊆
      range ((presentation K P).atlas.saturatedAtlas.chart j₀) :=
    subset_union_right.trans hjZ
  refine ⟨recMap P W j₀ hW₀, recMap Q V' i₀ hV₀, recMap_flat P hchart hdom W j₀ hW₀,
    recMap_pointSeminorm P W j₀ hW₀, recMap_pointSeminorm Q V' i₀ hV₀, ?_⟩
  let φ := (saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h
  let _ : Algebra A W.algebra := (recMap P W j₀ hW₀).toRingHom.toAlgebra
  let _ : Algebra A B := f.toRingHom.toAlgebra
  let _ : Algebra A V'.algebra :=
    (φ.toAlgHom.toRingHom.comp (recMap P W j₀ hW₀).toRingHom).toAlgebra
  let φA : W.algebra →ₐ[A] V'.algebra := { φ.toAlgHom.toRingHom with commutes' := fun _ => rfl }
  let βA : B →ₐ[A] V'.algebra :=
    { (recMap Q V' i₀ hV₀).toRingHom with
      commutes' := fun a => (pullback_recMap P Q f V' W h i₀ j₀ hV₀ hW₀ hij a).symm }
  let χ : W.algebra ⊗[A] B →+* V'.algebra :=
    (Algebra.TensorProduct.lift φA βA fun _ _ => Commute.all _ _).toRingHom
  have hχ₁ : ∀ x, χ (x ⊗ₜ 1) = φ x := fun x => by
    change φA x * βA 1 = φ x
    rw [map_one, mul_one]
    rfl
  have hχ₂ : ∀ b, χ (1 ⊗ₜ b) = recMap Q V' i₀ hV₀ b := fun b => by
    change φA 1 * βA b = _
    rw [map_one, one_mul]
    rfl
  refine ⟨χ, hχ₁, hχ₂, fun s => ?_⟩
  have : Algebra.FiniteType W.algebra (W.algebra ⊗[A] B) :=
    finiteType_tensor Q f W.algebra fun _ => rfl
  have : IsNoetherianRing (W.algebra ⊗[A] B) :=
    Algebra.FiniteType.isNoetherianRing W.algebra _
  exact FinitePieceLocalAlgebra.bijective_localRingHom_of_ker_le_pow χ
    (surjective_of_isFiniteBanach P Q f V hVo W V' h hV' j₀ hW₀ i₀ hV₀ (fun _ => rfl)
      (fun _ => rfl) χ hχ₁ hχ₂ hφ)
    (fun n hn k => ker_le_pow P Q f V hVo W V' h hV' j₀ hW₀ i₀ hV₀ (fun _ => rfl)
      (fun _ => rfl) χ hχ₁ hχ₂ hφ n hn k) s.kernel

end Langlands.Analytic.AffineAnalytification.FinitePieceLocal
