import Langlands.Weil.Representation.CyclicExtensionTwistStatement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Twists of an extension across a finite cyclic quotient: proof -/

noncomputable section

universe uK uG uV uW

set_option autoImplicit false

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- On a nonzero space the scalar of a scalar operator is determined. -/
private theorem eq_of_forall_smul_eq {V : Type uV} [AddCommGroup V] [Module K V]
    [Nontrivial V] {a b : K} (h : ∀ v : V, a • v = b • v) : a = b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hab : (a - b) • v = 0 := by rw [sub_smul, h v, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hab).resolve_right hv)

/-- Positive rank means a nonzero carrier. -/
private theorem nontrivial_of_rank_ne_zero (A : FiniteRepresentation.{uK, uG, uV} K G)
    (hA : A.rank ≠ 0) : Nontrivial A :=
  Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hA)

/-- Two successive actions are the action of the product. -/
private theorem rep_apply_apply {V : Type uV} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (g h : G) (v : V) : ρ g (ρ h v) = ρ (g * h) v := by
  rw [map_mul]
  rfl

/-- An equivalence of the restrictions to a normal subgroup yields a character of `G`,
trivial on the subgroup, whose twist of `A` is equivalent to `B`. -/
private theorem exists_twist_equiv_of_restriction_equiv
    (N : Subgroup G) [N.Normal]
    (A : FiniteRepresentation.{uK, uG, uV} K G) (hA : A.rank ≠ 0)
    (hs : HasScalarEndomorphisms (of (A.representation.comp N.subtype)))
    (B : FiniteRepresentation.{uK, uG, uW} K G)
    (e : Equiv (of (A.representation.comp N.subtype)) (of (B.representation.comp N.subtype))) :
    ∃ χ : G →* Kˣ, N ≤ χ.ker ∧ Nonempty (Equiv (twist χ A) B) := by
  classical
  have := nontrivial_of_rank_ne_zero A hA
  have he : ∀ n ∈ N, ∀ w : A, e (A.representation n w) = B.representation n (e w) :=
    fun n hn w =>
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap ⟨n, hn⟩ w
  have he' : ∀ n ∈ N, ∀ w : B,
      e.symm (B.representation n w) = A.representation n (e.symm w) :=
    fun n hn w =>
      Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap ⟨n, hn⟩ w
  -- The ratio of the transported action of `g` to the action of `g` is scalar.
  have hT : ∀ g : G, ∃ c : K, ∀ v : A,
      e.symm (B.representation g (e (A.representation g⁻¹ v))) = c • v := by
    intro g
    let T : (of (A.representation.comp N.subtype)).representation.IntertwiningMap
        (of (A.representation.comp N.subtype)).representation :=
      { toLinearMap := e.symm.toLinearMap ∘ₗ ((B.representation g : B →ₗ[K] B) ∘ₗ
          (e.toLinearMap ∘ₗ (A.representation g⁻¹ : A →ₗ[K] A)))
        isIntertwining' := by
          intro n
          ext v
          change e.symm (B.representation g (e (A.representation g⁻¹
              (A.representation n v)))) =
            A.representation n (e.symm (B.representation g (e (A.representation g⁻¹ v))))
          have hm : g⁻¹ * (n : G) * g ∈ N := by
            simpa using (inferInstance : N.Normal).conj_mem n n.2 g⁻¹
          rw [rep_apply_apply, show g⁻¹ * (n : G) = (g⁻¹ * n * g) * g⁻¹ by group,
            ← rep_apply_apply, he _ hm, rep_apply_apply B.representation g,
            show g * (g⁻¹ * (n : G) * g) = n * g by group, ← rep_apply_apply,
            he' n n.2] }
    obtain ⟨c, hc⟩ := hs T
    exact ⟨c, fun v => LinearMap.congr_fun hc v⟩
  choose c hc using hT
  have hB : ∀ (g : G) (v : A), B.representation g (e v) = e (c g • A.representation g v) := by
    intro g v
    have h := hc g (A.representation g v)
    rw [Representation.inv_self_apply] at h
    rw [← h, Representation.Equiv.apply_symm_apply]
  have h1 : c 1 = 1 := by
    refine eq_of_forall_smul_eq (V := A) fun v => ?_
    have h := hc 1 v
    simp only [inv_one, map_one, Module.End.one_apply,
      Representation.Equiv.symm_apply_apply] at h
    rw [one_smul]
    exact h.symm
  have hmul : ∀ g h : G, c (g * h) = c g * c h := by
    intro g h
    refine eq_of_forall_smul_eq (V := A) fun w => ?_
    have hinj : ∀ x y : A, e x = e y → x = y := fun x y hxy => e.injective hxy
    apply hinj
    have key := hB (g * h) (A.representation (g * h)⁻¹ w)
    rw [Representation.self_inv_apply] at key
    rw [← key, ← rep_apply_apply, hB, hB, map_smul (A.representation g), rep_apply_apply,
      Representation.self_inv_apply, smul_smul]
  let c₀ : G →* K := { toFun := c, map_one' := h1, map_mul' := hmul }
  let χ : G →* Kˣ := c₀.toHomUnits
  have hχ : ∀ g, (χ g : K) = c g := fun g => rfl
  refine ⟨χ, ?_, ?_⟩
  · intro n hn
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hχ, Units.val_one]
    refine (eq_of_forall_smul_eq (V := A) fun v => ?_).symm
    rw [← hc n v, ← he _ hn, Representation.self_inv_apply,
      Representation.Equiv.symm_apply_apply, one_smul]
  · change Nonempty (Equiv (of (Langlands.twist χ A.representation)) B)
    refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
    change e ((χ g : K) • A.representation g v) = B.representation g (e v)
    rw [hB, hχ]

/-- An equivalence of twists restricts to an equivalence of the restrictions to a subgroup
on which the character is trivial. -/
private def restrictionEquivOfTwistEquiv (N : Subgroup G) (χ : G →* Kˣ) (hχ : N ≤ χ.ker)
    (A : FiniteRepresentation.{uK, uG, uV} K G) (B : FiniteRepresentation.{uK, uG, uW} K G)
    (f : Equiv (twist χ A) B) :
    Equiv (of (A.representation.comp N.subtype)) (of (B.representation.comp N.subtype)) :=
  Representation.Equiv.mk f.toLinearEquiv fun n => by
    ext v
    have h :=
      Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (n : G) v
    change f ((χ n : K) • A.representation n v) = B.representation n (f v) at h
    rw [MonoidHom.mem_ker.mp (hχ n.2), Units.val_one, one_smul] at h
    exact h

/-- Two twists of `A` by characters trivial on `N` are equivalent only if the characters
agree, when the restriction of `A` to `N` is nonzero with scalar endomorphisms. -/
private theorem eq_of_twist_equiv (N : Subgroup G)
    (A : FiniteRepresentation.{uK, uG, uV} K G) (hA : A.rank ≠ 0)
    (hs : HasScalarEndomorphisms (of (A.representation.comp N.subtype)))
    (χ ψ : G →* Kˣ) (hχ : N ≤ χ.ker) (hψ : N ≤ ψ.ker)
    (φ : Equiv (twist χ A) (twist ψ A)) : χ = ψ := by
  have := nontrivial_of_rank_ne_zero A hA
  change Equiv (of (Langlands.twist χ A.representation))
    (of (Langlands.twist ψ A.representation)) at φ
  let T : (of (A.representation.comp N.subtype)).representation.IntertwiningMap
      (of (A.representation.comp N.subtype)).representation :=
    { toLinearMap := φ.toLinearMap
      isIntertwining' := fun n => by
        ext v
        have h :=
          Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (n : G) v
        change φ ((χ n : K) • A.representation n v) = (ψ n : K) • A.representation n (φ v) at h
        rw [MonoidHom.mem_ker.mp (hχ n.2), MonoidHom.mem_ker.mp (hψ n.2), Units.val_one,
          one_smul, one_smul] at h
        exact h }
  obtain ⟨a, ha⟩ := hs T
  have hφ : ∀ v : A, φ v = a • v := fun v => LinearMap.congr_fun ha v
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    have h0 : φ v = φ 0 := by rw [hφ, zero_smul, map_zero]
    exact φ.injective h0
  ext g
  refine mul_left_cancel₀ ha0 (eq_of_forall_smul_eq (V := A) fun w => ?_)
  have h := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g
    (A.representation g⁻¹ w)
  change φ ((χ g : K) • A.representation g (A.representation g⁻¹ w)) =
    (ψ g : K) • A.representation g (φ (A.representation g⁻¹ w)) at h
  rw [Representation.self_inv_apply, map_smul φ, hφ, hφ, map_smul (A.representation g),
    Representation.self_inv_apply, smul_smul, smul_smul] at h
  rw [mul_comm a, h, mul_comm]

/-- The kernel of an inflated character of `G ⧸ N` contains `N`. -/
private theorem le_ker_comp_mk' (N : Subgroup G) [N.Normal] (ψ : G ⧸ N →* Kˣ) :
    N ≤ (ψ.comp (QuotientGroup.mk' N)).ker := by
  intro n hn
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff n).mpr hn, map_one]

/-- The extensions of a nonzero restriction with scalar endomorphisms across a finite
cyclic quotient are exactly the pairwise distinct twists by the powers of a faithful
character of the quotient. -/
theorem cyclicExtensionTwistClassification :
    CyclicExtensionTwistClassificationStatement.{uK, uG, uV, uW} := by
  intro K G _ _ N _ _ _ η hη A hA hs B
  classical
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  have hηord : orderOf (η γ) = Nat.card (G ⧸ N) := by
    rw [orderOf_injective η hη, orderOf_eq_card_of_forall_mem_zpowers hγ]
  have : NeZero (Nat.card (G ⧸ N)) := ⟨Nat.card_pos.ne'⟩
  have hprim : IsPrimitiveRoot (η γ) (Nat.card (G ⧸ N)) :=
    hηord ▸ IsPrimitiveRoot.orderOf (η γ)
  -- Every character of the cyclic quotient is a power of `η`.
  have hpow : ∀ ψ : G ⧸ N →* Kˣ, ∃ i : Fin (Nat.card (G ⧸ N)), η ^ (i : ℕ) = ψ := by
    intro ψ
    have hmem : ψ γ ∈ rootsOfUnity (Nat.card (G ⧸ N)) K := by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]
    obtain ⟨i, hi, hiψ⟩ := hprim.eq_pow_of_mem_rootsOfUnity hmem
    refine ⟨⟨i, hi⟩, MonoidHom.ext fun x => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hγ x)
    rw [map_zpow, map_zpow, MonoidHom.pow_apply, hiψ]
  -- Distinct exponents give distinct inflated characters.
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective γ
  have hdist : ∀ i j : Fin (Nat.card (G ⧸ N)),
      (η ^ (i : ℕ)).comp (QuotientGroup.mk' N) = (η ^ (j : ℕ)).comp (QuotientGroup.mk' N) →
        i = j := by
    intro i j h
    have h' := congrArg (fun χ : G →* Kˣ => χ g₀) h
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hg₀, MonoidHom.pow_apply] at h'
    exact Fin.ext (pow_injOn_Iio_orderOf (by simp [hηord]) (by simp [hηord]) h')
  constructor
  · rintro ⟨e⟩
    obtain ⟨χ, hχN, ⟨f⟩⟩ := exists_twist_equiv_of_restriction_equiv N A hA hs B e
    have hχ : (QuotientGroup.lift N χ hχN).comp (QuotientGroup.mk' N) = χ := by
      ext g
      rfl
    obtain ⟨i, hi⟩ := hpow (QuotientGroup.lift N χ hχN)
    have hiχ : (η ^ (i : ℕ)).comp (QuotientGroup.mk' N) = χ := by rw [hi, hχ]
    have f' : Equiv (twist ((η ^ (i : ℕ)).comp (QuotientGroup.mk' N)) A) B := by
      rw [hiχ]
      exact f
    refine ⟨i, ⟨f'⟩, ?_⟩
    rintro j ⟨fj⟩
    exact hdist j i (eq_of_twist_equiv N A hA hs _ _ (le_ker_comp_mk' N _)
      (le_ker_comp_mk' N _) (fj.trans f'.symm))
  · rintro ⟨i, ⟨f⟩, -⟩
    exact ⟨restrictionEquivOfTwistEquiv N _ (le_ker_comp_mk' N _) A B f⟩

end Langlands.FiniteRepresentation
