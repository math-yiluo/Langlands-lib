import Langlands.Global.Factors.CuspidalPairEisensteinOneplace

/-! # The transformation law of the Levi Whittaker coefficient at one unramified place

For a section built from cusp forms spherical outside `S` and a finite place `v ∉ S`, the
Levi Whittaker coefficient `W_M(φ_s)` of the twisted section transforms under right
translation by a matrix supported at `v` by the normalized spherical section of the local
two-block induced representation. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairEisenstein.Oneplace

open MeasureTheory NumberField Automorphic AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight
open scoped CategoryTheory.MonObj

section Naturality

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_reindex {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (g : Matrix.GeneralLinearGroup α R) :
    Matrix.GeneralLinearGroup.map f (GeneralLinear.reindex e g) =
      GeneralLinear.reindex e (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  rfl

theorem map_sumBlockUnipotent {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) :
    Matrix.GeneralLinearGroup.map f (GeneralLinear.sumBlockUnipotent X) =
      GeneralLinear.sumBlockUnipotent (X.map f) := by
  apply Units.ext
  change (Matrix.fromBlocks 1 X 0 1).map f = Matrix.fromBlocks 1 (X.map f) 0 1
  rw [Matrix.fromBlocks_map]
  simp

theorem map_upper (m n : ℕ) (a : Matrix (Fin m) (Fin n) R) :
    Matrix.GeneralLinearGroup.map f (Shahidi.upper m n R a) =
      Shahidi.upper m n S (a.map f) := by
  unfold Shahidi.upper
  rw [map_reindex, map_sumBlockUnipotent]

theorem map_intertwiningUnipotent (m n : ℕ) (a : Matrix (Fin n) (Fin m) R) :
    Matrix.GeneralLinearGroup.map f (Shahidi.intertwiningUnipotent m n R a) =
      Shahidi.intertwiningUnipotent m n S (a.map f) := by
  unfold Shahidi.intertwiningUnipotent Shahidi.swapRank
  rw [map_reindex, map_upper]

theorem map_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Matrix.GeneralLinearGroup.map f (GeneralLinear.permutation n R σ) =
      GeneralLinear.permutation n S σ := by
  apply Units.ext
  funext i j
  change f (GeneralLinear.permutation n R σ i j) = GeneralLinear.permutation n S σ i j
  rw [GeneralLinear.permutation_entry, GeneralLinear.permutation_entry, apply_ite f, f.map_one,
    f.map_zero]

theorem map_blockWeyl (m n : ℕ) :
    Matrix.GeneralLinearGroup.map f (Shahidi.blockWeyl m n R) = Shahidi.blockWeyl m n S :=
  map_permutation f _ _

theorem map_leviEmbedding {n : ℕ} (B : GeneralLinear.BlockShape n) (m : B.Levi R) :
    Matrix.GeneralLinearGroup.map f (B.leviEmbedding R m) =
      B.leviEmbedding S (fun i => Matrix.GeneralLinearGroup.map f (m i)) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change f (B.leviEmbedding R m (B.index i a) (B.index j b)) =
    B.leviEmbedding S (fun k => Matrix.GeneralLinearGroup.map f (m k))
      (B.index i a) (B.index j b)
  by_cases h : i = j
  · subst j
    simp only [B.leviEmbedding_apply_same]
    rfl
  · rw [B.leviEmbedding_apply_ne R m a b h,
      B.leviEmbedding_apply_ne S _ a b h, map_zero]

end Naturality

section RankCast

variable {R : Type*} [CommRing R]

theorem leviEmbedding_rankCast {m n : ℕ} (C : GeneralLinear.BlockShape m) (h : m = n)
    (M : C.Levi R) :
    (C.rankCast h).leviEmbedding R M =
      GeneralLinear.reindex (finCongr h) (C.leviEmbedding R M) := by
  apply Units.ext
  rfl

theorem reindex_mem_unipotentSubgroup_rankCast {m n : ℕ} (C : GeneralLinear.BlockShape m)
    (h : m = n) {g : Langlands.GeneralLinear m R} (hg : g ∈ C.unipotentSubgroup R) :
    GeneralLinear.reindex (finCongr h) g ∈ (C.rankCast h).unipotentSubgroup R := by
  rw [GeneralLinear.BlockShape.mem_unipotentSubgroup_iff] at hg ⊢
  obtain ⟨hp, hd⟩ := hg
  rw [GeneralLinear.BlockShape.mem_parabolic_iff] at hp ⊢
  exact ⟨fun i j a b hji => hp i j a b hji, fun i a b => hd i a b⟩

end RankCast

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

section Components

variable (F) in
/-- The adelic matrix with component `x` at the finite place `v` and `1` at every other place. -/
abbrev adelicAt (n : ℕ) (v : FinitePlace F) (x : FiniteLocalGL F n v) : AdelicGL F n :=
  AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v x)

theorem adelicAt_mul (n : ℕ) (v : FinitePlace F) (x y : FiniteLocalGL F n v) :
    adelicAt F n v (x * y) = adelicAt F n v x * adelicAt F n v y := by
  simp only [adelicAt, map_mul]

theorem comp_eq_map (n : ℕ) (v : FinitePlace F) (g : AdelicGL F n) :
    comp F n v g = Matrix.GeneralLinearGroup.map (finiteProjection F v) g := by
  apply Units.ext
  rfl

theorem infinite_eq_map (n : ℕ) (g : AdelicGL F n) :
    AdelicGL.infinite F n g =
      Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeles F)) g := by
  apply Units.ext
  rfl

theorem comp_adelicAt (n : ℕ) (v : FinitePlace F) (x : FiniteLocalGL F n v) :
    comp F n v (adelicAt F n v x) = x := by
  change FiniteAdelicGL.localProjection F n v
    (AdelicGL.finite F n (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v x))) = x
  rw [RankinSelbergGlobal.LocalPointFactorization.finite_ofFinite,
    FiniteAdelicGL.localProjection_localInclusion]

theorem comp_adelicAt_of_ne (n : ℕ) {v w : FinitePlace F} (h : w ≠ v) (x : FiniteLocalGL F n v) :
    comp F n w (adelicAt F n v x) = 1 := by
  change FiniteAdelicGL.localProjection F n w
    (AdelicGL.finite F n (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v x))) = 1
  rw [RankinSelbergGlobal.LocalPointFactorization.finite_ofFinite,
    FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w h]

theorem infinite_adelicAt (n : ℕ) (v : FinitePlace F) (x : FiniteLocalGL F n v) :
    AdelicGL.infinite F n (adelicAt F n v x) = 1 :=
  RankinSelbergGlobal.LocalPointFactorization.infinite_ofFinite F n _

/-- An adelic matrix is determined by its archimedean component and its components at the
finite places. -/
theorem adelic_ext {n : ℕ} {g h : AdelicGL F n}
    (h1 : AdelicGL.infinite F n g = AdelicGL.infinite F n h)
    (h2 : ∀ w, comp F n w g = comp F n w h) : g = h := by
  rw [← AdelicGL.pair_projections F n g, ← AdelicGL.pair_projections F n h, h1]
  exact congrArg _ (FiniteAdelicGL.ext_localProjection F n (fun w => h2 w))

/-- An adelic matrix with trivial component at `v` commutes with every matrix supported
at `v`. -/
theorem commute_adelicAt {n : ℕ} (v : FinitePlace F) {g : AdelicGL F n}
    (hg : comp F n v g = 1) (x : FiniteLocalGL F n v) : Commute g (adelicAt F n v x) := by
  refine adelic_ext ?_ fun w => ?_
  · rw [map_mul, map_mul, infinite_adelicAt, mul_one, one_mul]
  · rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hg, one_mul, mul_one]
    · rw [comp_adelicAt_of_ne n hw, mul_one, one_mul]

theorem adelicAt_mem_standardCompact {n : ℕ} (v : FinitePlace F) {x : FiniteLocalGL F n v}
    (hx : x ∈ FiniteAdelicGL.localIntegral F n v) :
    adelicAt F n v x ∈ standardCompact F n := by
  rw [mem_standardCompact_iff]
  refine ⟨?_, ?_⟩
  · rw [infinite_adelicAt]
    exact one_mem _
  · rw [RankinSelbergGlobal.LocalPointFactorization.finite_ofFinite]
    exact (FiniteAdelicGL.localInclusion_mem_standardIntegral F n v x).2 hx

theorem adelicAt_apply_eq_zero {n : ℕ} (v : FinitePlace F) (x : FiniteLocalGL F n v)
    {I J : Fin n} (hIJ : I ≠ J) (h : x I J = 0) :
    (adelicAt F n v x : Matrix (Fin n) (Fin n) (Adeles F)) I J = 0 := by
  refine Prod.ext ?_ ?_
  · exact Matrix.one_apply_ne hIJ
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    change FiniteAdelicGL.localProjection F n w (FiniteAdelicGL.localInclusion F n v x) I J = 0
    by_cases hw : w = v
    · subst hw
      rw [FiniteAdelicGL.localProjection_localInclusion]
      exact h
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw]
      exact Matrix.one_apply_ne hIJ

theorem adelicAt_apply_eq_one {n : ℕ} (v : FinitePlace F) (x : FiniteLocalGL F n v)
    {I : Fin n} (h : x I I = 1) :
    (adelicAt F n v x : Matrix (Fin n) (Fin n) (Adeles F)) I I = 1 := by
  refine Prod.ext ?_ ?_
  · exact Matrix.one_apply_eq I
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    change FiniteAdelicGL.localProjection F n w (FiniteAdelicGL.localInclusion F n v x) I I = 1
    by_cases hw : w = v
    · subst hw
      rw [FiniteAdelicGL.localProjection_localInclusion]
      exact h
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw]
      exact Matrix.one_apply_eq I

/-- A matrix of the unipotent radical of a block parabolic, placed at `v`, lies in the adelic
unipotent radical. -/
theorem adelicAt_mem_unipotentSubgroup {n : ℕ} (B : GeneralLinear.BlockShape n)
    (v : FinitePlace F) {x : FiniteLocalGL F n v}
    (hx : x ∈ B.unipotentSubgroup (FiniteCompletion F v)) :
    adelicAt F n v x ∈ B.unipotentSubgroup (Adeles F) := by
  rw [GeneralLinear.BlockShape.mem_unipotentSubgroup_iff] at hx ⊢
  obtain ⟨hp, hd⟩ := hx
  rw [GeneralLinear.BlockShape.mem_parabolic_iff] at hp ⊢
  refine ⟨fun i j a b hji => adelicAt_apply_eq_zero v x ?_ (hp i j a b hji), fun i a b => ?_⟩
  · intro he
    have h' := congrArg Sigma.fst (B.indexEquiv.injective he)
    exact absurd h' (ne_of_gt hji)
  · by_cases hab : a = b
    · subst hab
      have h := hd i a a
      simp only [↓reduceIte] at h ⊢
      exact adelicAt_apply_eq_one v x h
    · have h := hd i a b
      simp only [hab, ↓reduceIte] at h ⊢
      exact adelicAt_apply_eq_zero v x (fun he => hab ((B.index i).injective he)) h

/-- A Levi element placed at `v` is the Levi element with components placed at `v`. -/
theorem adelicAt_leviEmbedding {n : ℕ} (B : GeneralLinear.BlockShape n) (v : FinitePlace F)
    (M : B.Levi (FiniteCompletion F v)) :
    adelicAt F n v (B.leviEmbedding (FiniteCompletion F v) M) =
      B.leviEmbedding (Adeles F) (fun i => adelicAt F (B.size i) v (M i)) := by
  refine adelic_ext ?_ fun w => ?_
  · rw [infinite_adelicAt]
    rw [show AdelicGL.infinite F n
        (B.leviEmbedding (Adeles F) (fun i => adelicAt F (B.size i) v (M i))) =
      B.leviEmbedding (InfiniteAdeleRing F)
        (fun i => AdelicGL.infinite F (B.size i) (adelicAt F (B.size i) v (M i))) from
      map_leviEmbedding (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeles F)) B _]
    simp only [infinite_adelicAt]
    exact (map_one _).symm
  · by_cases hw : w = v
    · subst hw
      rw [comp_adelicAt, comp_eq_map, map_leviEmbedding]
      simp only [← comp_eq_map, comp_adelicAt]
    · rw [comp_adelicAt_of_ne n hw, comp_eq_map, map_leviEmbedding]
      simp only [← comp_eq_map, comp_adelicAt_of_ne _ hw]
      exact (map_one _).symm

end Components

section TwoBlock

/-- The identification of `Fin ((r + 1) + (t + 1))` with `Fin (r + t + 2)`. -/
abbrev blockEquiv (r t : ℕ) : Fin (r + 1 + (t + 1)) ≃ Fin (r + t + 2) := finCongr (by omega)

variable (F r t) in
/-- The adelic matrix with component `x ∈ GL_((r+1)+(t+1))(F_v)` at `v`, as a matrix of size
`r + t + 2`, and `1` at every other place. -/
abbrev blockAt (v : FinitePlace F)
    (x : Langlands.GeneralLinear (r + 1 + (t + 1)) (FiniteCompletion F v)) :
    AdelicGL F (r + t + 2) :=
  adelicAt F (r + t + 2) v (GeneralLinear.reindex (blockEquiv r t) x)

theorem blockAt_mul (v : FinitePlace F)
    (x y : Langlands.GeneralLinear (r + 1 + (t + 1)) (FiniteCompletion F v)) :
    blockAt F r t v (x * y) = blockAt F r t v x * blockAt F r t v y := by
  simp only [blockAt, map_mul, adelicAt_mul]

/-- The unipotent radical of the local upper two-block parabolic, placed at `v`, lies in the
adelic unipotent radical. -/
theorem blockAt_mem_unipotentSubgroup (v : FinitePlace F)
    {u : Langlands.GeneralLinear (r + 1 + (t + 1)) (FiniteCompletion F v)}
    (hu : u ∈ (Shahidi.UnramifiedSection.shape r t).unipotentSubgroup (FiniteCompletion F v)) :
    blockAt F r t v u ∈ (blockShape r t).unipotentSubgroup (Adeles F) :=
  adelicAt_mem_unipotentSubgroup _ v (reindex_mem_unipotentSubgroup_rankCast _ _ hu)

/-- The block-diagonal matrix `diag(m₁, m₂)` placed at `v` is the adelic Levi element
`localLevi`. -/
theorem blockAt_blockSum (v : FinitePlace F) (m₁ : FiniteLocalGL F (r + 1) v)
    (m₂ : FiniteLocalGL F (t + 1) v) :
    blockAt F r t v (GeneralLinear.blockSum (m₁, m₂)) =
      (blockShape r t).leviEmbedding (Adeles F) (localLevi F r t v m₁ m₂) := by
  have e1 : GeneralLinear.blockSum (m₁, m₂) =
      (Shahidi.UnramifiedSection.shape r t).leviEmbedding (FiniteCompletion F v)
        ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) _).symm (m₁, m₂)) :=
    (Shahidi.twoBlocks_leviEmbedding _ _ _ _).symm
  have e2 : (fun i => adelicAt F ((blockShape r t).size i) v
      ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) _).symm (m₁, m₂) i)) =
      localLevi F r t v m₁ m₂ := by
    funext i
    fin_cases i <;> rfl
  rw [blockAt, e1]
  exact (congrArg (adelicAt F (r + t + 2) v) (leviEmbedding_rankCast _ _ _).symm).trans
    ((adelicAt_leviEmbedding (blockShape r t) v _).trans (congrArg _ e2))

/-- An integral matrix of `GL_((r+1)+(t+1))(F_v)`, for the canonical valuation, is integral as a
matrix of size `r + t + 2`. -/
theorem reindex_mem_localIntegral (v : FinitePlace F)
    {k : Langlands.GeneralLinear (r + 1 + (t + 1)) (FiniteCompletion F v)}
    (hk : k ∈ Shahidi.UnramifiedSection.integralGroup (CompletionPadic.padicField v) r t) :
    GeneralLinear.reindex (blockEquiv r t) k ∈ FiniteAdelicGL.localIntegral F (r + t + 2) v := by
  obtain ⟨h1, h2⟩ := (Shahidi.UnramifiedSection.mem_integralGroup_iff (CompletionPadic.padicField v) r t k).1 hk
  rw [FiniteAdelicGL.mem_localIntegral]
  refine ⟨fun i j => (OpenCellExhaustion.mem_adicCompletionIntegers_iff_canonical v _).2
    (h1 _ _), fun i j => ?_⟩
  rw [← map_inv]
  exact (OpenCellExhaustion.mem_adicCompletionIntegers_iff_canonical v _).2 (h2 _ _)

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 1600000 in
open RankinSelbergGlobal ClassFieldTheory.Global.RelativeWeilGroup in
/-- **The transformation law at an unramified place.** For a section built from cusp forms
spherical outside `S`, a finite place `v ∉ S` where the component `ψ_v` has conductor `𝒪_v`,
an adelic matrix `g` with component `1` at `v`, and `x ∈ GL_((r+1)+(t+1))(F_v)`,
`W_M(φ_s)(g ι_v(x)) = f_v(x) W_M(φ_s)(g)`, where `f_v` is the normalized spherical section
`Shahidi.UnramifiedSection.sectionFunction` for the Satake tuples `a` of `P` and `c` of `Pd`
at `v`. -/
theorem leviWhittaker_mul_blockAt
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (Pd : CuspidalSpectralPresentation.{u, uQ} (dualRealization T'))
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {φ : AdelicGL F (r + t + 2) → ℂ} (hφ : IsSection T T' φ)
    (hsph : IsSphericalSectionOutside T T' S φ) (s : ℂ) (v : FinitePlace F) (hv : v ∉ S)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (hψv0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (ϖ : (CompletionPadic.padicField v).Carrierˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) ϖ)
    (a : Fin (r + 1) → ℂˣ)
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (c : Fin (t + 1) → ℂˣ)
    (hc : Unramified.Eigenvalues.ofTuple c =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    (g : AdelicGL F (r + t + 2)) (hg : comp F (r + t + 2) v g = 1)
    (x : Langlands.GeneralLinear (r + 1 + (t + 1)) (FiniteCompletion F v)) :
    leviWhittaker F r t ψ.complex (twisted φ s) (g * blockAt F r t v x) =
      Shahidi.UnramifiedSection.sectionFunction hϖ ψv a c s x *
        leviWhittaker F r t ψ.complex (twisted φ s) g := by
  obtain ⟨p, hp, k, hk, hx⟩ :=
    Shahidi.UnramifiedSection.exists_parabolic_mul (CompletionPadic.padicField v) r t hϖ x
  let P₀ : (Shahidi.UnramifiedSection.shape r t).parabolic (FiniteCompletion F v) := ⟨p, hp⟩
  have hsec : Shahidi.UnramifiedSection.sectionFunction hϖ ψv a c s x =
      Shahidi.UnramifiedSection.leviValue hϖ ψv a c s
        (Shahidi.UnramifiedSection.leviFirst (CompletionPadic.padicField v) r t P₀)
        (Shahidi.UnramifiedSection.leviSecond (CompletionPadic.padicField v) r t P₀) := by
    rw [hx]
    exact Shahidi.UnramifiedSection.sectionFunction_parabolic_mul hϖ a c s hψv0 P₀ k hk
  let u : Langlands.GeneralLinear (r + 1 + (t + 1)) (FiniteCompletion F v) :=
    (((Shahidi.UnramifiedSection.shape r t).unipotentPart (FiniteCompletion F v) P₀ :
      (Shahidi.UnramifiedSection.shape r t).parabolic (FiniteCompletion F v)) :
        Langlands.GeneralLinear (r + 1 + (t + 1)) (FiniteCompletion F v))
  have hu : u ∈ (Shahidi.UnramifiedSection.shape r t).unipotentSubgroup (FiniteCompletion F v) :=
    ⟨(Shahidi.UnramifiedSection.shape r t).unipotentPart (FiniteCompletion F v) P₀,
      ((Shahidi.UnramifiedSection.shape r t).unipotentPart (FiniteCompletion F v) P₀).property,
      rfl⟩
  have hp' : p = u * GeneralLinear.blockSum (Shahidi.UnramifiedSection.leviFirst (CompletionPadic.padicField v) r t P₀,
      Shahidi.UnramifiedSection.leviSecond (CompletionPadic.padicField v) r t P₀) := by
    have e : P₀ = ((Shahidi.UnramifiedSection.shape r t).unipotentPart (FiniteCompletion F v) P₀ :
        (Shahidi.UnramifiedSection.shape r t).parabolic (FiniteCompletion F v)) *
        (Shahidi.UnramifiedSection.shape r t).leviInParabolic (FiniteCompletion F v)
          ((Shahidi.UnramifiedSection.shape r t).leviProjection (FiniteCompletion F v) P₀) :=
      (inv_mul_cancel_right _ _).symm
    have e' := congrArg Subtype.val e
    rw [Subgroup.coe_mul, GeneralLinear.BlockShape.leviInParabolic_val,
      Shahidi.twoBlocks_leviEmbedding] at e'
    exact e'
  set m₁ := Shahidi.UnramifiedSection.leviFirst (CompletionPadic.padicField v) r t P₀
  set m₂ := Shahidi.UnramifiedSection.leviSecond (CompletionPadic.padicField v) r t P₀
  set U := blockAt F r t v u with hU
  set M := blockAt F r t v (GeneralLinear.blockSum (m₁, m₂)) with hM
  set Kk := blockAt F r t v k with hKk
  have hKkint := reindex_mem_localIntegral v hk
  have hinv : ∀ y, twisted φ s (y * Kk) = twisted φ s y := by
    intro y
    rw [twisted, twisted, hsph.1 v hv _ hKkint y,
      heightPower_mul_compact s y Kk (adelicAt_mem_standardCompact v hKkint)]
  have hcomm : g * (U * M) = U * (M * g) := by
    have c1 : g * U = U * g := (commute_adelicAt v hg _).eq
    have c2 : g * M = M * g := (commute_adelicAt v hg _).eq
    rw [← mul_assoc, c1, mul_assoc, c2]
  have hxU : g * blockAt F r t v x = g * (U * M) * Kk := by
    rw [hx, hp', blockAt_mul, blockAt_mul]
    exact (mul_assoc _ _ _).symm
  have hθ := RankinSelbergGlobal.UnequalEulerFactorization.isIntegrallyTrivial_standardCharacters
    v ψv hψv0
  rw [hxU, leviWhittaker_mul_right_of_invariant _ _ _ _ hinv, hcomm,
    leviWhittaker_unipotent_mul _ _ (twisted_unipotent_mul hφ s) _ _
      (blockAt_mem_unipotentSubgroup v hu),
    hM, blockAt_blockSum, hsec]
  exact leviWhittaker_localLevi_mul P Pd hP hPd ψ hψF hS hφ hsph s v hv ψv hψv ϖ hϖ
    (hθ r).1 (hθ t).1 a ha c hc g (by rw [hg]; exact one_mem _) m₁ m₂

end TwoBlock

end Langlands.Global.CuspidalPairEisenstein.Oneplace
