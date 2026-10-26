import Langlands.Representation.Exponents.DualJacquet
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Classification.MaximalConePolygon

/-!
# Dual Jacquet exponents through source functionals

A dual Jacquet exponent along `B` is the same as a nonzero functional on the
source that is invariant under the opposite radical of `B` and is an eigenvector
of the block scalars, with the half modulus of `B` in its eigenvalue. Through this
criterion, a dual exponent along `B` restricts to a dual exponent along every
consecutive coarsening `C` of `B`, and an irreducible admissible representation
has its central character as a dual exponent along a one-block shape.
-/

noncomputable section

namespace Langlands

open GeneralLinear
open scoped BigOperators NNReal

universe uF uV

/-- A subrepresentation is nonzero exactly when it has a nonzero vector. -/
theorem Subrepresentation.ne_bot_iff_exists {k G W : Type*} [CommRing k] [Monoid G]
    [AddCommGroup W] [Module k W] {ρ : Representation k G W} (S : Subrepresentation ρ) :
    S ≠ ⊥ ↔ ∃ v ∈ S, v ≠ 0 := by
  have h1 : S ≠ ⊥ ↔ S.toSubmodule ≠ ⊥ :=
    not_congr ⟨fun h => by subst h; rfl, fun h => Subrepresentation.toSubmodule_injective h⟩
  exact h1.trans (Submodule.ne_bot_iff _)

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (R : Type*) [CommRing R]

theorem index_eq_indexEquiv (i : Fin B.length) (a : Fin (B.size i)) :
    B.index i a = B.indexEquiv ⟨i, a⟩ := rfl

@[simp] theorem blockIndex_indexEquiv (i : Fin B.length) (a : Fin (B.size i)) :
    Geometric.blockIndex B (B.indexEquiv ⟨i, a⟩) = i :=
  Geometric.blockIndex_index B i a

/-- Lower block triangularity in ambient coordinates. -/
theorem mem_oppositeParabolic_iff_blockIndex (g : GeneralLinear n R) :
    g ∈ B.oppositeParabolic R ↔
      ∀ x y : Fin n, Geometric.blockIndex B x < Geometric.blockIndex B y → g x y = 0 := by
  rw [B.mem_oppositeParabolic_iff R]
  constructor
  · intro h x y hxy
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    rw [blockIndex_indexEquiv, blockIndex_indexEquiv] at hxy
    exact h i j a b hxy
  · intro h i j a b hij
    apply h
    simpa [index_eq_indexEquiv] using hij

/-- The opposite radical in ambient coordinates. -/
theorem mem_oppositeUnipotentSubgroup_iff_blockIndex (g : GeneralLinear n R) :
    g ∈ B.oppositeUnipotentSubgroup R ↔
      (∀ x y : Fin n, Geometric.blockIndex B x < Geometric.blockIndex B y → g x y = 0) ∧
        ∀ x y : Fin n, Geometric.blockIndex B x = Geometric.blockIndex B y → g x y = if x = y then 1 else 0 := by
  rw [B.mem_oppositeUnipotentSubgroup_iff R, B.mem_oppositeParabolic_iff_blockIndex R]
  refine and_congr Iff.rfl ⟨fun h x y hxy => ?_, fun h i a b => ?_⟩
  · obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    rw [blockIndex_indexEquiv, blockIndex_indexEquiv] at hxy
    subst hxy
    refine (h i a b).trans ?_
    simp
  · refine (h (B.index i a) (B.index i b) (by simp [index_eq_indexEquiv])).trans ?_
    simp

/-- Entries of embedded block scalars. -/
theorem leviEmbedding_blockScalarLevi_apply (a : Fin B.length → Rˣ) (x y : Fin n) :
    B.leviEmbedding R (B.blockScalarLevi R a) x y =
      if x = y then (a (Geometric.blockIndex B x) : R) else 0 := by
  obtain ⟨⟨i, α⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, β⟩, rfl⟩ := B.indexEquiv.surjective y
  rw [blockIndex_indexEquiv, ← index_eq_indexEquiv, ← index_eq_indexEquiv]
  by_cases h : i = j
  · subst h
    exact (B.blockScalar_apply_same R a i α β).trans (by simp)
  · rw [B.leviEmbedding_apply_ne R _ _ _ h]
    refine (ite_eq_right_iff.mpr fun he => absurd ?_ h).symm
    simpa [index_eq_indexEquiv] using congrArg (Geometric.blockIndex B) he

/-! ### Consecutive coarsenings -/

variable {B} {C : BlockShape n} {q : Fin B.length → Fin C.length}

/-- The opposite radical of a coarsening lies in the opposite radical of the finer
shape. -/
theorem oppositeUnipotentSubgroup_le_of_coarsen (hq : Monotone q)
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i) :
    C.oppositeUnipotentSubgroup R ≤ B.oppositeUnipotentSubgroup R := by
  intro g hg
  rw [C.mem_oppositeUnipotentSubgroup_iff_blockIndex] at hg
  rw [B.mem_oppositeUnipotentSubgroup_iff_blockIndex]
  simp only [blockIndex_coarsening B C q hq hsize] at hg
  refine ⟨fun x y hxy => ?_, fun x y hxy => hg.2 x y (by rw [hxy])⟩
  rcases (hq hxy.le).lt_or_eq with h | h
  · exact hg.1 x y h
  · have hne : x ≠ y := by
      rintro rfl
      exact lt_irrefl _ hxy
    rw [hg.2 x y h]
    simp [hne]

/-- Block scalars of a coarsening are block scalars of the finer shape. -/
theorem leviEmbedding_blockScalarLevi_coarsen (hq : Monotone q)
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    (a : Fin C.length → Rˣ) :
    B.leviEmbedding R (B.blockScalarLevi R (a ∘ q)) =
      C.leviEmbedding R (C.blockScalarLevi R a) := by
  refine Matrix.GeneralLinearGroup.ext fun x y => ?_
  rw [leviEmbedding_blockScalarLevi_apply, leviEmbedding_blockScalarLevi_apply,
    blockIndex_coarsening B C q hq hsize]
  rfl

end GeneralLinear.BlockShape

namespace MaximalConePolygon

/-- Pair products over a consecutive coarsening: pairs inside one coarse block
contribute nothing, and the pairs between two coarse blocks multiply their sizes. -/
theorem prod_pairs_coarsen {G : Type*} [CommGroup G] {ℓ m : ℕ} (b : Fin ℓ → ℕ)
    (c : Fin m → ℕ) (q : Fin ℓ → Fin m) (hq : Monotone q)
    (hc : ∀ j, c j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), b i) (w : Fin m → G) :
    ∏ i : Fin ℓ, ∏ i' ∈ Finset.univ.filter (fun i' => i < i'),
        (w (q i) ^ b i) ^ b i' / (w (q i') ^ b i') ^ b i =
      ∏ j : Fin m, ∏ j' ∈ Finset.univ.filter (fun j' => j < j'),
        (w j ^ c j) ^ c j' / (w j' ^ c j') ^ c j := by
  have hfac : ∀ (x y : G) (s u : ℕ), (x ^ s) ^ u / (y ^ u) ^ s = (x / y) ^ (s * u) := by
    intro x y s u
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm u s]
  simp only [hfac, Finset.prod_filter]
  have hL : ∀ i i' : Fin ℓ, (if i < i' then (w (q i) / w (q i')) ^ (b i * b i') else 1) =
      if q i < q i' then (w (q i) / w (q i')) ^ (b i * b i') else 1 := by
    intro i i'
    by_cases h1 : q i < q i'
    · have h2 : i < i' := hq.reflect_lt h1
      simp only [h1, h2, ↓reduceIte]
    · by_cases h2 : i < i'
      · have h3 : q i = q i' := le_antisymm (hq h2.le) (not_lt.mp h1)
        simp [h2, h3]
      · simp [h1, h2]
  simp only [hL]
  have hfib : ∀ j j' : Fin m,
      ∏ i ∈ Finset.univ.filter (fun i => q i = j),
        ∏ i' ∈ Finset.univ.filter (fun i' => q i' = j'),
          (if q i < q i' then (w (q i) / w (q i')) ^ (b i * b i') else 1) =
        if j < j' then (w j / w j') ^ (c j * c j') else 1 := by
    intro j j'
    have hcongr : ∀ i ∈ Finset.univ.filter (fun i => q i = j),
        ∏ i' ∈ Finset.univ.filter (fun i' => q i' = j'),
          (if q i < q i' then (w (q i) / w (q i')) ^ (b i * b i') else 1) =
        ∏ i' ∈ Finset.univ.filter (fun i' => q i' = j'),
          (if j < j' then (w j / w j') ^ (b i * b i') else 1) := by
      intro i hi
      refine Finset.prod_congr rfl fun i' hi' => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
      rw [hi, hi']
    rw [Finset.prod_congr rfl hcongr]
    split_ifs with h
    · rw [hc j, hc j', Finset.sum_mul_sum]
      simp only [Finset.prod_pow_eq_pow_sum]
    · simp
  calc _ = ∏ j : Fin m, ∏ i ∈ Finset.univ.filter (fun i => q i = j), ∏ i' : Fin ℓ,
        (if q i < q i' then (w (q i) / w (q i')) ^ (b i * b i') else 1) :=
          (Finset.prod_fiberwise _ q _).symm
    _ = ∏ j : Fin m, ∏ i ∈ Finset.univ.filter (fun i => q i = j), ∏ j' : Fin m,
        ∏ i' ∈ Finset.univ.filter (fun i' => q i' = j'),
          (if q i < q i' then (w (q i) / w (q i')) ^ (b i * b i') else 1) :=
          Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ =>
            (Finset.prod_fiberwise _ q _).symm
    _ = ∏ j : Fin m, ∏ j' : Fin m, ∏ i ∈ Finset.univ.filter (fun i => q i = j),
        ∏ i' ∈ Finset.univ.filter (fun i' => q i' = j'),
          (if q i < q i' then (w (q i) / w (q i')) ^ (b i * b i') else 1) :=
          Finset.prod_congr rfl fun j _ => Finset.prod_comm
    _ = _ := Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun j' _ => hfib j j'

end MaximalConePolygon

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-! ## The source criterion -/

/-- A dual Jacquet exponent is a smooth character together with a nonzero source
functional invariant under the opposite radical, on which the block scalars act by
the character times the inverse half modulus. -/
theorem isDualJacquetExponent_iff (B : BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) :
    T.IsDualJacquetExponent B A χ ↔
      (letI := T.topology; IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ))) ∧
        ∃ ℓ : Module.Dual ℂ A, ℓ ≠ 0 ∧
          (∀ g ∈ B.oppositeUnipotentSubgroup F.Carrier, ∀ v : A, ℓ (A.ρ g v) = ℓ v) ∧
          ∀ (a : Fin B.length → F.Carrierˣ) (v : A),
            ℓ (A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v) =
              (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)⁻¹ * (χ a : ℂ) *
                ℓ v := by
  unfold IsDualJacquetExponent
  refine and_congr Iff.rfl ?_
  rw [Subrepresentation.ne_bot_iff_exists]
  constructor
  · rintro ⟨φ₀, hφ, hne⟩
    let φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A) := φ₀
    refine ⟨φ.comp (T.splitCentreOppositeJacquetMk B A), ?_, ?_, ?_⟩
    · intro h
      apply hne
      apply LinearMap.ext
      intro x
      obtain ⟨v, rfl⟩ := T.splitCentreOppositeJacquetMk_surjective B A x
      exact LinearMap.congr_fun h v
    · intro g hg v
      exact congrArg (fun z => φ z) (Jacquet.mk_apply_subgroup A.ρ _ ⟨g, hg⟩ v)
    · exact (T.mem_dualJacquet_eigenspace_iff B A χ φ).mp hφ
  · rintro ⟨ℓ, hne, hinv, heig⟩
    let φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A) :=
      Jacquet.lift A.ρ (B.oppositeUnipotentSubgroup F.Carrier) ℓ (by
        intro g
        ext v
        exact hinv g g.property v)
    refine ⟨φ, (T.mem_dualJacquet_eigenspace_iff B A χ φ).mpr heig, ?_⟩
    intro h
    apply hne
    ext v
    exact LinearMap.congr_fun h (T.splitCentreOppositeJacquetMk B A v)

/-! ## Restriction to a consecutive coarsening -/

/-- The full modulus of a coarsening agrees with the finer one on its block scalars. -/
theorem leviModulus_blockScalarLevi_coarsen {B C : BlockShape n}
    {q : Fin B.length → Fin C.length} (hq : Monotone q)
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    (a : Fin C.length → F.Carrierˣ) :
    T.leviModulus B (B.blockScalarLevi F.Carrier (a ∘ q)) =
      T.leviModulus C (C.blockScalarLevi F.Carrier a) := by
  have hs : ∀ (D : BlockShape n) (b : Fin D.length → F.Carrierˣ) (i : Fin D.length),
      T.determinantNorm (D.size i) (D.blockScalarLevi F.Carrier b i) =
        T.normalizedAbsUnits (b i) ^ D.size i :=
    fun D b i => T.determinantNorm_scalar _ _
  rw [T.leviModulus_apply, T.leviModulus_apply]
  simp only [hs, Function.comp_apply]
  exact MaximalConePolygon.prod_pairs_coarsen B.size C.size q hq hsize
    fun j => T.normalizedAbsUnits (a j)

/-- A dual exponent along `B` restricts to a dual exponent along every consecutive
coarsening of `B`. -/
theorem isDualJacquetExponent_coarsen {B C : BlockShape n}
    {q : Fin B.length → Fin C.length} (hq : Monotone q)
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} {χ : (Fin B.length → F.Carrierˣ) →* ℂˣ}
    (h : T.IsDualJacquetExponent B A χ) {χC : (Fin C.length → F.Carrierˣ) →* ℂˣ}
    (hχC : ∀ a, χC a = χ (a ∘ q)) : T.IsDualJacquetExponent C A χC := by
  let := T.topology
  rw [T.isDualJacquetExponent_iff] at h ⊢
  obtain ⟨hopen, ℓ, hne, hinv, heig⟩ := h
  refine ⟨?_, ℓ, hne, fun g hg v =>
    hinv g (BlockShape.oppositeUnipotentSubgroup_le_of_coarsen F.Carrier hq hsize hg) v,
    fun a v => ?_⟩
  · have hcont : Continuous (fun a : Fin C.length → F.Carrierˣ => a ∘ q) :=
      continuous_pi fun i => continuous_apply (q i)
    have hk : (χC.ker : Set (Fin C.length → F.Carrierˣ)) =
        (fun a => a ∘ q) ⁻¹' (χ.ker : Set (Fin B.length → F.Carrierˣ)) := by
      ext a
      simp [MonoidHom.mem_ker, hχC]
    rw [hk]
    exact hopen.preimage hcont
  · have := heig (a ∘ q) v
    rw [BlockShape.leviEmbedding_blockScalarLevi_coarsen F.Carrier hq hsize, ← hχC,
      leviHalfModulus_apply, T.leviModulus_blockScalarLevi_coarsen hq hsize] at this
    rw [leviHalfModulus_apply]
    exact this

/-- Real parts add along the fibres of a coarsening. -/
theorem isRealPartOf_coarsen {ℓ m : ℕ} {q : Fin ℓ → Fin m}
    {χ : (Fin ℓ → F.Carrierˣ) →* ℂˣ} {r : Fin ℓ → ℝ} (hr : T.IsRealPartOf χ r)
    {χC : (Fin m → F.Carrierˣ) →* ℂˣ} (hχC : ∀ a, χC a = χ (a ∘ q)) (s : Fin m → ℝ)
    (hs : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => q i = j), r i = s j) :
    T.IsRealPartOf χC s := by
  intro a
  rw [hχC, hr, ← Finset.prod_fiberwise Finset.univ q]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← hs j, Real.rpow_sum_of_pos (T.normalizedAbs_pos (a j).ne_zero)]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp [hi]

/-! ## One block -/

/-- Along a one-block shape, the central character of an irreducible admissible
representation is a dual exponent. -/
theorem exists_isDualJacquetExponent_of_length_eq_one {B : BlockShape n} (hB : B.length = 1)
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} (hi : Representation.IsIrreducible A.ρ)
    (ha : letI := T.topology; IsAdmissible A.ρ) :
    ∃ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ, T.IsDualJacquetExponent B A χ := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  have := T.generalLinearTopologicalGroup n
  have hsub : ∀ i j : Fin B.length, i = j := fun i j => Fin.ext (by omega)
  let i₀ : Fin B.length := ⟨0, by omega⟩
  obtain ⟨ω, ⟨-, hω⟩, -⟩ := admissibleSchur_centralCharacter A.ρ ha hi
  let χ : (Fin B.length → F.Carrierˣ) →* ℂˣ :=
    (ω.comp GeneralLinear.scalarToCenter).comp (Pi.evalMonoidHom _ i₀)
  have hscalar : ∀ a : Fin B.length → F.Carrierˣ,
      B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a) =
        GeneralLinear.scalar (a i₀) := by
    intro a
    refine Matrix.GeneralLinearGroup.ext fun x y => ?_
    rw [BlockShape.leviEmbedding_blockScalarLevi_apply, hsub (Geometric.blockIndex B x) i₀]
    simp [GeneralLinear.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hact : ∀ (a : Fin B.length → F.Carrierˣ) (v : A),
      A.ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v = (χ a : ℂ) • v := by
    intro a v
    rw [hscalar]
    exact hω (GeneralLinear.scalarToCenter (a i₀)) v
  have : Nontrivial A :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  refine ⟨χ, (T.isDualJacquetExponent_iff B A χ).mpr ⟨?_, ℓ, ?_, ?_, ?_⟩⟩
  · obtain ⟨K, hK⟩ := ha.1 v
    have hf : Continuous fun a : Fin B.length → F.Carrierˣ => GeneralLinear.scalar (n := n) (a i₀) :=
      GeneralLinear.scalarContinuous.continuous.comp (continuous_apply i₀)
    let f : (Fin B.length → F.Carrierˣ) →* GeneralLinear n F.Carrier :=
      (GeneralLinear.scalar (n := n)).comp (Pi.evalMonoidHom (fun _ => F.Carrierˣ) i₀)
    refine Subgroup.isOpen_mono (H₁ := K.toSubgroup.comap f) ?_
      (by rw [Subgroup.coe_comap]; exact K.isOpen.preimage hf)
    intro a haK
    change χ a = 1
    apply Units.ext
    apply smul_left_injective ℂ hv
    change (χ a : ℂ) • v = (1 : ℂ) • v
    rw [← hact, hscalar, one_smul]
    exact hK ⟨_, haK⟩
  · intro h
    exact hℓ (LinearMap.congr_fun h v)
  · intro g hg w
    have hg1 : g = 1 := by
      rw [BlockShape.mem_oppositeUnipotentSubgroup_iff_blockIndex] at hg
      refine Matrix.GeneralLinearGroup.ext fun x y => ?_
      rw [hg.2 x y (hsub _ _)]
      simp [Matrix.one_apply]
    rw [hg1, map_one, Module.End.one_apply]
  · intro a w
    have hδ : T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) = 1 := by
      rw [leviHalfModulus_eq_one, T.leviModulus_apply]
      refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j hj => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact absurd hj (by rw [hsub i j]; exact lt_irrefl j)
    rw [hact, hδ, map_smul, smul_eq_mul]
    simp

end PadicField.TopologicalData

end Langlands
