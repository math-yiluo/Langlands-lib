import Langlands.GroupScheme.Absolute.BorelFieldExtensionDescent
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

/-! # Normal law systems: descent of normal unipotent groups of points

This extends the law systems of `BorelFieldExtensionDescent` by a conjugation law and finitely
many fixed vanishing conditions with coefficients in `k`. A solvable group of `K`-points normal
in all `K`-points and killing the fixed functions specializes to a normal solvable group of
`k`-points killing the same functions. -/

noncomputable section

namespace Langlands.GroupScheme.RadicalFieldExtension

open TensorProduct WithConv BorelFieldExtension
open scoped commutatorElement

section Separation

/-- Two separating families of algebra maps `Q₁ → K` and `Q₂ → K` separate the elements of
`Q₁ ⊗[K] Q₂` by the products of their members. -/
theorem tensor_eq_zero_of_separating₂ {K Q₁ Q₂ J₁ J₂ : Type*} [Field K] [CommRing Q₁]
    [Algebra K Q₁] [CommRing Q₂] [Algebra K Q₂]
    (χ₁ : J₁ → Q₁ →ₐ[K] K) (hχ₁ : ∀ q, (∀ i, χ₁ i q = 0) → q = 0)
    (χ₂ : J₂ → Q₂ →ₐ[K] K) (hχ₂ : ∀ q, (∀ i, χ₂ i q = 0) → q = 0) (t : Q₁ ⊗[K] Q₂)
    (ht : ∀ i i', Algebra.TensorProduct.lift (χ₁ i) (χ₂ i') (fun _ _ => Commute.all _ _) t = 0) :
    t = 0 := by
  let b := Module.Basis.ofVectorSpace K Q₁
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  suffices hc : c = 0 by simp [hc]
  ext a
  rw [Finsupp.coe_zero, Pi.zero_apply]
  apply hχ₂
  intro i'
  have hd : Finsupp.linearCombination K b (c.mapRange (χ₂ i') (map_zero _)) = 0 := by
    apply hχ₁
    intro i
    have h := ht i i'
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (h := fun j (x : K) => x • b j)
      (fun _ => zero_smul K _)]
    simp only [Finsupp.sum, map_sum, Algebra.TensorProduct.lift_tmul] at h
    simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h0 := (linearIndependent_iff.mp b.linearIndependent) _ hd
  simpa using congrArg (fun f : _ →₀ K => f a) h0

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {H : Type*} [CommRing H] [Algebra k H]

/-- **One-sided separation.** Suppose the `K`-points separate the elements of `K ⊗[k] H`. If a
law `w : H → H ⊗[k] H` sends every pair `(x, y)` with `x` arbitrary and `y ∈ Γ₁` into `Γ₂`,
then it pulls the vanishing ideal of `Γ₂` back into the pullback of the vanishing ideal of `Γ₁`
along the second projection. -/
theorem baseMap_mem_map_includeRight {Γ₁ Γ₂ : Set (H →ₐ[k] K)}
    (hsep : ∀ t : K ⊗[k] H, (∀ x : H →ₐ[k] K, extPoint x t = 0) → t = 0)
    (w : H →ₐ[k] H ⊗[k] H) (hw : ∀ x : H →ₐ[k] K, ∀ y ∈ Γ₁, (pairLift x y).comp w ∈ Γ₂)
    {f : K ⊗[k] H} (hf : f ∈ vanishingIdeal Γ₂) :
    baseMap w f ∈ (vanishingIdeal Γ₁).map
      (baseMap (K := K) (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)) := by
  set I := vanishingIdeal Γ₁ with hI
  set N := I.map (baseMap (K := K) (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H))
    with hN
  let q : H →ₐ[k] (K ⊗[k] H) ⧸ I :=
    ((Ideal.Quotient.mkₐ K I).restrictScalars k).comp Algebra.TensorProduct.includeRight
  let Φ₀ : H ⊗[k] H →ₐ[k] (K ⊗[k] H) ⊗[K] ((K ⊗[k] H) ⧸ I) :=
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : _ →ₐ[k] (K ⊗[k] H) ⊗[K] ((K ⊗[k] H) ⧸ I)).comp
        Algebra.TensorProduct.includeRight)
      ((Algebra.TensorProduct.includeRight.restrictScalars k).comp q)
      fun _ _ => Commute.all (S := (K ⊗[k] H) ⊗[K] ((K ⊗[k] H) ⧸ I)) _ _
  let Φ : K ⊗[k] (H ⊗[k] H) →ₐ[K] (K ⊗[k] H) ⊗[K] ((K ⊗[k] H) ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId K _) Φ₀
      fun _ _ => Commute.all (S := (K ⊗[k] H) ⊗[K] ((K ⊗[k] H) ⧸ I)) _ _
  let u₁ : K ⊗[k] H →ₐ[K] (K ⊗[k] (H ⊗[k] H)) ⧸ N :=
    (Ideal.Quotient.mkₐ K N).comp (baseMap Algebra.TensorProduct.includeLeft)
  let u₂ : (K ⊗[k] H) ⧸ I →ₐ[K] (K ⊗[k] (H ⊗[k] H)) ⧸ N :=
    Ideal.Quotient.liftₐ I
      ((Ideal.Quotient.mkₐ K N).comp (baseMap Algebra.TensorProduct.includeRight))
      fun a ha => by
        rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha
  let L := Algebra.TensorProduct.lift u₁ u₂
    fun _ _ => Commute.all (S := (K ⊗[k] (H ⊗[k] H)) ⧸ N) _ _
  have hΦ_tmul : ∀ a b : H, Φ (1 ⊗ₜ (a ⊗ₜ b)) =
      ((1 : K) ⊗ₜ[k] a) ⊗ₜ Ideal.Quotient.mk I (1 ⊗ₜ b) := by
    intro a b
    simp only [Φ, Φ₀, q, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk, one_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [Algebra.ofId_apply, map_one]
    exact one_mul (M := (K ⊗[k] H) ⊗[K] ((K ⊗[k] H) ⧸ I)) _
  have hLΦ : L.comp Φ = Ideal.Quotient.mkₐ K N := by
    apply Algebra.TensorProduct.ext_ring
    apply Algebra.TensorProduct.ext'
    intro a b
    change L (Φ (1 ⊗ₜ (a ⊗ₜ b))) = Ideal.Quotient.mk N (1 ⊗ₜ (a ⊗ₜ b))
    rw [hΦ_tmul, Algebra.TensorProduct.lift_tmul]
    change Ideal.Quotient.mk N (baseMap Algebra.TensorProduct.includeLeft (1 ⊗ₜ a)) *
      Ideal.Quotient.mk N (baseMap Algebra.TensorProduct.includeRight (1 ⊗ₜ b)) = _
    rw [baseMap_tmul, baseMap_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let χ₁ : (H →ₐ[k] K) → (K ⊗[k] H) →ₐ[K] K := fun x => extPoint x
  let χ₂ : Γ₁ → ((K ⊗[k] H) ⧸ I) →ₐ[K] K := fun x =>
    Ideal.Quotient.liftₐ I (extPoint x.1) fun a ha => ha x.1 x.2
  have hχ₂ : ∀ t, (∀ x, χ₂ x t = 0) → t = 0 := by
    intro t ht
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [Ideal.Quotient.eq_zero_iff_mem]
    intro x hx
    exact ht ⟨x, hx⟩
  have hΦ : Φ (baseMap w f) = 0 := by
    refine tensor_eq_zero_of_separating₂ χ₁ hsep χ₂ hχ₂ _ fun x y => ?_
    have hcomp : (Algebra.TensorProduct.lift (χ₁ x) (χ₂ y)
        fun _ _ => Commute.all (S := K) _ _).comp Φ =
        extPoint (pairLift x y.1) := by
      apply Algebra.TensorProduct.ext_ring
      apply Algebra.TensorProduct.ext'
      intro a b
      change Algebra.TensorProduct.lift (χ₁ x) (χ₂ y) (fun _ _ => Commute.all (S := K) _ _)
          (Φ (1 ⊗ₜ (a ⊗ₜ b))) =
        extPoint (pairLift x y.1) (1 ⊗ₜ (a ⊗ₜ b))
      rw [hΦ_tmul, Algebra.TensorProduct.lift_tmul]
      change extPoint x (1 ⊗ₜ a) * extPoint y.1 (1 ⊗ₜ b) = _
      simp
    rw [← AlgHom.comp_apply, hcomp, extPoint_baseMap]
    exact hf _ (hw x y.1 y.2)
  have h := AlgHom.congr_fun hLΦ (baseMap w f)
  rw [AlgHom.comp_apply, hΦ, map_zero, Ideal.Quotient.mkₐ_eq_mk, eq_comm,
    Ideal.Quotient.eq_zero_iff_mem] at h
  exact h

open P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.GeomIntegralOfIsAlgClosed in
/-- If `K ⊗[k] H` is reduced and of finite type over an algebraically closed field `K`, its
elements are separated by the `K`-points of `H`. -/
theorem eq_zero_of_forall_extPoint [IsAlgClosed K] [Algebra.FiniteType k H]
    [IsReduced (K ⊗[k] H)] (t : K ⊗[k] H) (ht : ∀ x : H →ₐ[k] K, extPoint x t = 0) : t = 0 := by
  have : IsJacobsonRing (K ⊗[k] H) := isJacobsonRing_of_finiteType (A := K)
  have hbot : (⊥ : Ideal (K ⊗[k] H)).jacobson = ⊥ := IsJacobsonRing.out this Ideal.isRadical_bot
  have ht' : t ∈ (⊥ : Ideal (K ⊗[k] H)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    let φ : K ⊗[k] H →ₐ[K] K := pointOfMaximal K m
    let x : H →ₐ[k] K := (φ.restrictScalars k).comp Algebra.TensorProduct.includeRight
    have hx : extPoint x = φ := by
      apply Algebra.TensorProduct.ext_ring
      ext h
      change extPoint x (1 ⊗ₜ h) = φ (1 ⊗ₜ h)
      rw [extPoint_tmul, one_mul]
      rfl
    rw [← pointOfMaximal_eq_zero_iff (K := K) m t]
    change φ t = 0
    rw [← hx]
    exact ht x
  rw [hbot] at ht'
  exact Ideal.mem_bot.1 ht'

end Separation

section Words

variable (k H : Type*) [Field k] [CommRing H] [HopfAlgebra k H]

/-- The conjugation law `(x, y) ↦ x * y * x⁻¹`. -/
def wConj : WithConv (H →ₐ[k] H ⊗[k] H) := univL k H * univR k H * (univL k H)⁻¹

variable {k H} {K : Type*} [CommRing K] [Algebra k K]

theorem pairLift_comp_wConj (x y : H →ₐ[k] K) :
    (pairLift x y).comp (wConj k H).ofConv = (toConv x * toConv y * (toConv x)⁻¹).ofConv := by
  have h : AlgHom.mapValue (pairLift x y) (wConj k H) = toConv x * toConv y * (toConv x)⁻¹ := by
    rw [wConj, map_mul, map_mul, map_inv, mapValue_pairLift_univL, mapValue_pairLift_univR]
  rw [← h, AlgHom.mapValue_apply, ofConv_toConv]

end Words

section LawSystem

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
variable {R : Type*} [CommRing R] [Algebra k R]

/-- The pullbacks of a family of functions along the second projection `H ⊗[k] H → H`. -/
def rightFam {ι : Type*} (v : ι → R ⊗[k] H) : ι → R ⊗[k] (H ⊗[k] H) :=
  fun i => baseMap (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H) (v i)

variable (R) in
/-- A *normal law system*: a law system whose first family is also stable under conjugation by
arbitrary points, and generates an ideal containing the functions `1 ⊗ u l`. -/
structure IsNormalLawSystem (n : ℕ) (s : Set H) {ι : Type*} (u : ι → H) {r : ℕ → ℕ}
    (g : (j : ℕ) → Fin (r j) → R ⊗[k] H) : Prop where
  law : IsLawSystem R n s g
  conj : ∀ i, baseMap (K := R) (wConj k H).ofConv (g 0 i) ∈ Ideal.span (Set.range (rightFam (g 0)))
  unip : ∀ l, (1 : R) ⊗ₜ[k] u l ∈ Ideal.span (Set.range (g 0))

/-- If `y` vanishes on a family `v` and a law `w` sends `t` into the ideal generated by the
pullbacks of `v` along the second projection, then `(x, y) ∘ w` vanishes on `t` for every
`x`. -/
theorem extPoint_pairLift_eq_zero_right {ι : Type*} {v : ι → R ⊗[k] H} (x : H →ₐ[k] R)
    {y : H →ₐ[k] R} (hy : ∀ i, extPoint y (v i) = 0) {w : H →ₐ[k] H ⊗[k] H} {t : R ⊗[k] H}
    (ht : baseMap w t ∈ Ideal.span (Set.range (rightFam v))) :
    extPoint ((pairLift x y).comp w) t = 0 := by
  rw [← extPoint_baseMap]
  have hle : Ideal.span (Set.range (rightFam v)) ≤ RingHom.ker (extPoint (pairLift x y)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [rightFam, SetLike.mem_coe, RingHom.mem_ker, extPoint_baseMap,
      pairLift_comp_includeRight, hy]
  exact hle ht

end LawSystem

section KSide

variable {k K H : Type*} [Field k] [Field K] [Algebra k K] [CommRing H] [HopfAlgebra k H]

theorem map_span_rightFam {ι : Type*} (v : ι → K ⊗[k] H) :
    (Ideal.span (Set.range v)).map
        (baseMap (K := K) (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)) =
      Ideal.span (Set.range (rightFam v)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- **The normal law system of a normal solvable group of points.** Let `S` be a solvable
group of `K`-points, normal in all `K`-points, killing the functions `u l`, and suppose the
`K`-points separate `K ⊗[k] H`. The vanishing ideals of the derived subgroups of `S` form a
normal law system over `K` whose first family vanishes on `S`. -/
theorem exists_isNormalLawSystem [Algebra.FiniteType k H] (S : Subgroup (WithConv (H →ₐ[k] K)))
    [Group.IsSolvable S] [S.Normal] (s : Set H) {ι : Type*} (u : ι → H)
    (hsep : ∀ t : K ⊗[k] H, (∀ x : H →ₐ[k] K, extPoint x t = 0) → t = 0)
    (hu : ∀ l, ∀ x : H →ₐ[k] K, toConv x ∈ S → x (u l) = 0) :
    ∃ n : ℕ, ∃ r : ℕ → ℕ, ∃ g : (j : ℕ) → Fin (r j) → K ⊗[k] H, IsNormalLawSystem K n s u g ∧
      ∀ i, ∀ x : H →ₐ[k] K, toConv x ∈ S → extPoint x (g 0 i) = 0 := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def S).1 ‹_›
  have : IsNoetherianRing (K ⊗[k] H) := Algebra.FiniteType.isNoetherianRing K _
  let Γ : ℕ → Set (H →ₐ[k] K) := fun j => {x | toConv x ∈ (derivedSeries S j).map S.subtype}
  have hΓ : ∀ j (x : H →ₐ[k] K), x ∈ Γ j ↔ toConv x ∈ (derivedSeries S j).map S.subtype :=
    fun _ _ => Iff.rfl
  have hΓ0 : ∀ x : H →ₐ[k] K, x ∈ Γ 0 ↔ toConv x ∈ S := by
    intro x
    rw [hΓ, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfg : ∀ j, ∃ m : ℕ, ∃ v : Fin m → K ⊗[k] H,
      Ideal.span (Set.range v) = vanishingIdeal (Γ j) := fun j =>
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian _)
  choose r g hg using hfg
  have hmem : ∀ j i, g j i ∈ vanishingIdeal (Γ j) := fun j i => hg j ▸ Ideal.subset_span ⟨i, rfl⟩
  have hspan : ∀ j, pairIdeal K (vanishingIdeal (Γ j)) = Ideal.span (Set.range (pairFam (g j))) :=
    fun j => by rw [← hg j, pairIdeal_span]
  refine ⟨n, r, g, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro j _ i
    apply hmem j i
    rw [hΓ, toConv_ofConv]
    exact Subgroup.one_mem _
  · intro j _ i
    rw [← hspan]
    refine baseMap_mem_pairIdeal _ (fun x hx y hy => ?_) (hmem j i)
    rw [hΓ, pairLift_comp_wMul, toConv_ofConv]
    exact Subgroup.mul_mem _ ((hΓ j x).1 hx) ((hΓ j y).1 hy)
  · intro j _ i
    rw [← hspan]
    refine baseMap_mem_pairIdeal _ (fun x hx y _ => ?_) (hmem j i)
    rw [hΓ, pairLift_comp_wInv, toConv_ofConv]
    exact Subgroup.inv_mem _ ((hΓ j x).1 hx)
  · intro j _ i
    rw [← hspan]
    refine baseMap_mem_pairIdeal _ (fun x hx y hy => ?_) (hmem (j + 1) i)
    rw [hΓ, pairLift_comp_wComm, toConv_ofConv]
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 ((hΓ j x).1 hx)
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 ((hΓ j y).1 hy)
    rw [← hax, ← hby, ← map_commutatorElement]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator ha hb
  · intro h _
    rw [hg n]
    intro x hx
    have h1 := (hΓ n x).1 hx
    rw [hn, Subgroup.map_bot, Subgroup.mem_bot] at h1
    have h2 : x = (1 : WithConv (H →ₐ[k] K)).ofConv := by rw [← h1]
    rw [map_sub, extPoint_tmul, one_mul, Algebra.TensorProduct.algebraMap_apply, extPoint_tmul,
      map_one, mul_one, h2, AlgHom.convOne_apply, sub_self]
  · intro i
    rw [← map_span_rightFam, hg 0]
    refine baseMap_mem_map_includeRight hsep _ (fun x y hy => ?_) (hmem 0 i)
    rw [hΓ0, pairLift_comp_wConj, toConv_ofConv]
    exact ‹S.Normal›.conj_mem _ ((hΓ0 y).1 hy) _
  · intro l
    rw [hg 0]
    intro x hx
    rw [extPoint_tmul, one_mul]
    exact hu l x ((hΓ0 x).1 hx)
  · intro i x hx
    exact hmem 0 i x ((hΓ0 x).2 hx)

end KSide

section Transfer

variable {k : Type*} [Field k]
variable {R R' : Type*} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
variable {H : Type*} [CommRing H] [HopfAlgebra k H]

theorem coeffMap_rightFam (ψ : R →ₐ[k] R') {ι : Type*} (v : ι → R ⊗[k] H) (l : ι) :
    coeffMap ψ (rightFam v l) = rightFam (fun i => coeffMap ψ (v i)) l := by
  simp [rightFam, coeffMap_baseMap]

/-- Normal law systems are stable under change of coefficients. -/
theorem IsNormalLawSystem.map {n : ℕ} {s : Set H} {ι : Type*} {u : ι → H} {r : ℕ → ℕ}
    {g : (j : ℕ) → Fin (r j) → R ⊗[k] H} (hg : IsNormalLawSystem R n s u g) (ψ : R →ₐ[k] R') :
    IsNormalLawSystem R' n s u (fun j i => coeffMap ψ (g j i)) where
  law := hg.law.map ψ
  conj i := by
    have h := map_mem_span (coeffMap ψ) (hg.conj i)
    rw [coeffMap_baseMap] at h
    simpa only [coeffMap_rightFam] using h
  unip l := by
    have h := map_mem_span (coeffMap ψ) (hg.unip l)
    rwa [coeffMap_tmul, map_one] at h

end Transfer

section Descent

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {H : Type*} [CommRing H] [HopfAlgebra k H]

/-- **Descent.** A normal law system over `K` with finitely many conditions in its last family
and finitely many fixed functions comes from a normal law system over a finitely generated
`k`-subalgebra of `K`. -/
theorem IsNormalLawSystem.descend {n : ℕ} {s : Set H} (hs : s.Finite) {ι : Type*} [Finite ι]
    {u : ι → H} {r : ℕ → ℕ} {g : (j : ℕ) → Fin (r j) → K ⊗[k] H}
    (hg : IsNormalLawSystem K n s u g) :
    ∃ F : Finset K, ∃ g' : (j : ℕ) → Fin (r j) → Algebra.adjoin k (F : Set K) ⊗[k] H,
      IsNormalLawSystem (Algebra.adjoin k (F : Set K)) n s u g' ∧
        ∀ j ≤ n, ∀ i, coeffMap (Algebra.adjoin k (F : Set K)).val (g' j i) = g j i := by
  have e1 : ∀ᶠ F : Finset K in Filter.atTop, ∀ j ∈ Set.Iic n, ∀ i,
      g j i ∈ (coeffMap (M := H) (Algebra.adjoin k (F : Set K)).val).range :=
    (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun j _ =>
      Filter.eventually_all.2 fun i => eventually_mem_range _
  have e2 := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun j hj =>
    Filter.eventually_all.2 fun i => eventually_coeffs (hg.law.mul j hj i)
  have e3 := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun j hj =>
    Filter.eventually_all.2 fun i => eventually_coeffs (hg.law.inv j hj i)
  have e4 := (Filter.eventually_all_finite (Set.finite_Iio n)).2 fun j hj =>
    Filter.eventually_all.2 fun i => eventually_coeffs (hg.law.comm j hj i)
  have e5 := (Filter.eventually_all_finite hs).2 fun h hh => eventually_coeffs (hg.law.fin h hh)
  have e6 := Filter.eventually_all.2 fun i => eventually_coeffs (hg.conj i)
  have e7 := Filter.eventually_all.2 fun l => eventually_coeffs (hg.unip l)
  obtain ⟨F, h1, h2, h3, h4, h5, h6, h7⟩ :=
    (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and e7)))))).exists
  set A := Algebra.adjoin k (F : Set K)
  let g' : (j : ℕ) → Fin (r j) → A ⊗[k] H := fun j i =>
    Function.invFun (coeffMap (M := H) A.val) (g j i)
  have hgg' : ∀ j ≤ n, ∀ i, coeffMap A.val (g' j i) = g j i := fun j hj i =>
    Function.invFun_eq ((AlgHom.mem_range _).1 (h1 j hj i))
  have hinj := coeffMap_injective (M := H ⊗[k] H) A.val Subtype.val_injective
  have hinj₁ := coeffMap_injective (M := H) A.val Subtype.val_injective
  have hpair : ∀ j ≤ n, ∀ l, coeffMap A.val (pairFam (g' j) l) = pairFam (g j) l := by
    intro j hj l
    rw [coeffMap_pairFam]
    simp only [hgg' j hj]
  have hright : ∀ l, coeffMap A.val (rightFam (g' 0) l) = rightFam (g 0) l := by
    intro l
    rw [coeffMap_rightFam]
    simp only [hgg' 0 (Nat.zero_le n)]
  refine ⟨F, g', ⟨⟨fun j hj i => ?_, fun j hj i => ?_, fun j hj i => ?_, fun j hj i => ?_,
    fun h hh => ?_⟩, fun i => ?_, fun l => ?_⟩, hgg'⟩
  · have h := extPoint_coeffMap A.val (1 : WithConv (H →ₐ[k] A)).ofConv (g' j i)
    rw [comp_one_ofConv, hgg' j hj i, hg.law.one j hj i] at h
    exact Subtype.ext h
  · obtain ⟨c, hc, hsum⟩ := h2 j hj i
    refine mem_span_of_injective _ hinj hc ?_
    rw [coeffMap_baseMap, hgg' j hj i, ← hsum]
    simp only [hpair j hj]
  · obtain ⟨c, hc, hsum⟩ := h3 j hj i
    refine mem_span_of_injective _ hinj hc ?_
    rw [coeffMap_baseMap, hgg' j hj i, ← hsum]
    simp only [hpair j hj]
  · obtain ⟨c, hc, hsum⟩ := h4 j hj i
    refine mem_span_of_injective _ hinj hc ?_
    rw [coeffMap_baseMap, hgg' (j + 1) hj i, ← hsum]
    simp only [hpair j (Nat.le_of_lt hj)]
  · obtain ⟨c, hc, hsum⟩ := h5 h hh
    refine mem_span_of_injective _ hinj₁ hc ?_
    rw [map_sub, coeffMap_tmul, map_one, AlgHom.commutes, ← hsum]
    simp only [hgg' n le_rfl]
  · obtain ⟨c, hc, hsum⟩ := h6 i
    refine mem_span_of_injective _ hinj hc ?_
    rw [coeffMap_baseMap, hgg' 0 (Nat.zero_le n) i, ← hsum]
    simp only [hright]
  · obtain ⟨c, hc, hsum⟩ := h7 l
    refine mem_span_of_injective _ hinj₁ hc ?_
    rw [coeffMap_tmul, map_one, ← hsum]
    simp only [hgg' 0 (Nat.zero_le n)]

end Descent

section Rational

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The `k`-points vanishing on the first family of a normal law system form a normal
subgroup. -/
theorem IsNormalLawSystem.normal {n : ℕ} {s : Set H} {ι : Type*} {u : ι → H} {r : ℕ → ℕ}
    {g : (j : ℕ) → Fin (r j) → k ⊗[k] H} (hg : IsNormalLawSystem k n s u g) :
    (lawSubgroup hg.law 0 (Nat.zero_le n)).Normal where
  conj_mem z hz x i := by
    obtain ⟨x, rfl⟩ := WithConv.toConv_surjective x
    obtain ⟨z, rfl⟩ := WithConv.toConv_surjective z
    have h := extPoint_pairLift_eq_zero_right x hz (hg.conj i)
    rwa [pairLift_comp_wConj] at h

/-- The `k`-points vanishing on the first family of a normal law system kill the functions
`u l`. -/
theorem IsNormalLawSystem.apply_eq_zero {n : ℕ} {s : Set H} {ι : Type*} {u : ι → H}
    {r : ℕ → ℕ} {g : (j : ℕ) → Fin (r j) → k ⊗[k] H} (hg : IsNormalLawSystem k n s u g)
    {z : WithConv (H →ₐ[k] k)} (hz : z ∈ lawSubgroup hg.law 0 (Nat.zero_le n)) (l : ι) :
    z.ofConv (u l) = 0 := by
  have hker : Ideal.span (Set.range (g 0)) ≤ RingHom.ker (extPoint z.ofConv) :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
  have h := hker (hg.unip l)
  rwa [RingHom.mem_ker, extPoint_tmul, one_mul] at h

end Rational

section Core

/-- **The algebraic core.** Let `k ⊆ K` with `k` algebraically closed, `H` a finitely generated
commutative Hopf algebra over `k` whose `K`-points separate `K ⊗[k] H`, and `S` a solvable
normal group of `K`-points killing finitely many functions `u l ∈ H`, whose vanishing ideal
`Q ⊆ K ⊗[k] H` is prime. Let `P` be a prime of `H` such that `Q` lies in the extension of `P`
without containing `1 ⊗ P`. Then there is a prime `𝔭 < P` of `H` and a normal solvable group
of `k`-points killing every `u l` and containing every `k`-point on which `𝔭` vanishes. -/
theorem exists_isPrime_lt_of_normal_solvable {k K H : Type*} [Field k] [IsAlgClosed k]
    [Field K] [Algebra k K] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (S : Subgroup (WithConv (H →ₐ[k] K))) [Group.IsSolvable S] [S.Normal]
    {ι : Type*} [Finite ι] (u : ι → H)
    (hsep : ∀ t : K ⊗[k] H, (∀ x : H →ₐ[k] K, extPoint x t = 0) → t = 0)
    (hu : ∀ l, ∀ x : H →ₐ[k] K, toConv x ∈ S → x (u l) = 0)
    (Q : Ideal (K ⊗[k] H)) [Q.IsPrime]
    (hSQ : ∀ q, q ∈ Q ↔ ∀ x : H →ₐ[k] K, toConv x ∈ S → extPoint x q = 0)
    (P : Ideal H) [P.IsPrime]
    (hQP : ∀ q ∈ Q, baseMap (K := K) (Ideal.Quotient.mkₐ k P) q = 0)
    (hlt : ∃ p ∈ P, (1 : K) ⊗ₜ[k] p ∉ Q) :
    ∃ 𝔭 : Ideal H, 𝔭.IsPrime ∧ 𝔭 < P ∧ ∃ Γ : Subgroup (WithConv (H →ₐ[k] k)),
      Γ.Normal ∧ Group.IsSolvable Γ ∧ (∀ z ∈ Γ, ∀ l, z.ofConv (u l) = 0) ∧
        ∀ x : H →ₐ[k] k, 𝔭 ≤ RingHom.ker x → toConv x ∈ Γ := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := H)
  obtain ⟨n, r, g, hg, hg0⟩ := exists_isNormalLawSystem S (s : Set H) u hsep hu
  obtain ⟨F, g', hg', hgg'⟩ := hg.descend s.finite_toSet
  have : Algebra.FiniteType k (Algebra.adjoin k (F : Set K)) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset F)
  have : IsNoetherianRing (Algebra.adjoin k (F : Set K)) :=
    Algebra.FiniteType.isNoetherianRing k _
  obtain ⟨φ⟩ := nonempty_algHom_of_finiteType (k := k) (Algebra.adjoin k (F : Set K))
  obtain ⟨𝔭, h𝔭, h𝔭P, h𝔭d⟩ :=
    exists_isPrime_lt_specMap (Algebra.adjoin k (F : Set K)).val Subtype.val_injective φ Q P hQP hlt
  have hgφ := hg'.map φ
  let Γ := lawSubgroup hgφ.law 0 (Nat.zero_le n)
  obtain ⟨Γ₀, hΓ₀, hΓ₀x⟩ := exists_solvable_of_isLawSystem hgφ.law hs
  have hle : Γ ≤ Γ₀ := fun z hz => by
    obtain ⟨z, rfl⟩ := WithConv.toConv_surjective z
    exact hΓ₀x z hz
  have : Group.IsSolvable Γ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  refine ⟨𝔭, h𝔭, h𝔭P, Γ, hgφ.normal, this, fun z hz l => hgφ.apply_eq_zero hz l,
    fun x hx i => ?_⟩
  have hQ : coeffMap (Algebra.adjoin k (F : Set K)).val (g' 0 i) ∈ Q := by
    rw [hgg' 0 (Nat.zero_le n) i, hSQ]
    exact fun x hx => hg0 i x hx
  change extPoint x (coeffMap φ (g' 0 i)) = 0
  rw [extPoint_eq_lid]
  exact hx (h𝔭d _ hQ)

end Core

end Langlands.GroupScheme.RadicalFieldExtension
