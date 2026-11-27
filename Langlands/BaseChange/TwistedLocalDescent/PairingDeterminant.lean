import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Determinants of adjoint operators on a quotient and an orthogonal subspace

For a bilinear pairing `β` on a finite-dimensional vector space `V`, an operator `T` with
adjoint `T'` (`β (T x) y = β x (T' y)`), a `T`-stable subspace `W` and a `T'`-stable subspace
`W'` that pairs to zero with `W`, such that the descended pairing between `V ⧸ W` and `W'` is
nondegenerate on both sides (an element of `W'` orthogonal to all of `V` is zero, and an element
of `V` orthogonal to all of `W'` lies in `W`), the determinant of `T` on `V ⧸ W` equals that of
`T'` on `W'`. See the paired Markdown.
-/

namespace Langlands.BaseChange.TwistedLocalDescent

open Module

universe u v

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- **Pairing determinant lemma.** -/
theorem det_mapQ_eq_det_restrict_of_pairing (β : V →ₗ[F] V →ₗ[F] F) (W W' : Submodule F V)
    (T T' : V →ₗ[F] V) (hT : W ≤ W.comap T) (hT' : W' ≤ W'.comap T')
    (hadj : ∀ x y, β (T x) y = β x (T' y))
    (horth : ∀ x ∈ W, ∀ y ∈ W', β x y = 0)
    (hsep' : ∀ y ∈ W', (∀ x, β x y = 0) → y = 0)
    (hsep : ∀ x, (∀ y ∈ W', β x y = 0) → x ∈ W) :
    LinearMap.det (W.mapQ W T hT) = LinearMap.det (T'.restrict hT') := by
  -- `Φ : W' → (V ⧸ W)^*` and `Ψ : V ⧸ W → W'^*`.
  let Φ : W' →ₗ[F] Dual F (V ⧸ W) :=
    { toFun := fun y => W.liftQ (β.flip y) (fun x hx => by
        change β x y = 0
        exact horth x hx y y.property)
      map_add' := fun y z => by
        apply LinearMap.ext
        intro q
        refine Submodule.Quotient.induction_on W q ?_
        intro x
        simp
      map_smul' := fun c y => by
        apply LinearMap.ext
        intro q
        refine Submodule.Quotient.induction_on W q ?_
        intro x
        simp }
  have hΦ : ∀ (y : W') (x : V), Φ y (Submodule.Quotient.mk x) = β x y := fun _ _ => rfl
  let Ψ : (V ⧸ W) →ₗ[F] Dual F W' :=
    W.liftQ (LinearMap.domRestrict' W' ∘ₗ β) (fun x hx => by
      apply LinearMap.ext
      intro y
      exact horth x hx y y.property)
  have hΨ : ∀ (x : V) (y : W'), Ψ (Submodule.Quotient.mk x) y = β x y := fun _ _ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    apply hsep' y y.property
    intro x
    rw [← hΦ, hy]
    rfl
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    refine Submodule.Quotient.induction_on W q (fun x hq => ?_) hq
    rw [Submodule.Quotient.mk_eq_zero]
    apply hsep x
    intro y hy
    have := congrArg (fun f : Dual F W' => f ⟨y, hy⟩) hq
    simpa only [hΨ, LinearMap.zero_apply] using this
  have hdim1 := LinearMap.finrank_le_finrank_of_injective hΦinj
  have hdim2 := LinearMap.finrank_le_finrank_of_injective hΨinj
  rw [Subspace.dual_finrank_eq] at hdim1 hdim2
  have hbij : Function.Bijective Φ :=
    ⟨hΦinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq]; omega)).mp hΦinj⟩
  let e : W' ≃ₗ[F] Dual F (V ⧸ W) := LinearEquiv.ofBijective Φ hbij
  have hconj : T'.restrict hT' =
      (e.symm : Dual F (V ⧸ W) →ₗ[F] W') ∘ₗ (W.mapQ W T hT).dualMap ∘ₗ (e : W' →ₗ[F] _) := by
    apply LinearMap.ext
    intro y
    apply e.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on W q ?_
    intro x
    change Φ (T'.restrict hT' y) (Submodule.Quotient.mk x) =
      Φ y (W.mapQ W T hT (Submodule.Quotient.mk x))
    rw [Submodule.mapQ_apply, hΦ, hΦ, LinearMap.coe_restrict_apply, hadj]
  rw [hconj]
  have := LinearMap.det_conj (W.mapQ W T hT).dualMap e.symm
  simp only [LinearEquiv.symm_symm] at this
  rw [this, LinearMap.det_dualMap]

/-- If `P = D ⊔ L` with `D` and `L` disjoint, all stable under `T`, then the determinant of `T`
on `V ⧸ D` is the product of the determinants of `T` on `L` and on `V ⧸ P`. -/
theorem det_mapQ_eq_det_restrict_mul_det_mapQ (D P L : Submodule F V) (hle : D ≤ P)
    (hsup : P = D ⊔ L) (hdisj : Disjoint D L) (T : V →ₗ[F] V) (hD : D ≤ D.comap T)
    (hP : P ≤ P.comap T) (hL : L ≤ L.comap T) :
    LinearMap.det (D.mapQ D T hD) =
      LinearMap.det (T.restrict hL) * LinearMap.det (P.mapQ P T hP) := by
  let TQ := D.mapQ D T hD
  let W := P.map D.mkQ
  have hW : W ≤ W.comap TQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨T p, hP hp, rfl⟩
  rw [LinearMap.det_eq_det_mul_det W TQ hW]
  congr 1
  · -- `L ≃ P ⧸ D` inside `V ⧸ D`
    let φ₀ : L →ₗ[F] W :=
      LinearMap.codRestrict W (D.mkQ ∘ₗ L.subtype)
        (fun x => Submodule.mem_map_of_mem (hsup ▸ Submodule.mem_sup_right x.property))
    have hbij : Function.Bijective φ₀ := by
      constructor
      · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro x hx
        have h0 : D.mkQ (x : V) = 0 := congrArg Subtype.val hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
        exact Subtype.ext ((Submodule.disjoint_def.mp hdisj) _ h0 x.property)
      · rintro ⟨w, hw⟩
        obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hw
        rw [hsup] at hp
        obtain ⟨d, hd, l, hl, rfl⟩ := Submodule.mem_sup.mp hp
        refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
        have hd0 : D.mkQ d = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hd
        change D.mkQ l = D.mkQ (d + l)
        rw [map_add, hd0, zero_add]
    let φ := LinearEquiv.ofBijective φ₀ hbij
    rw [← LinearMap.det_conj (T.restrict hL) φ]
    congr 1
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := φ.surjective w
    apply Subtype.ext
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    rfl
  · let ψ := Submodule.quotientQuotientEquivQuotient D P hle
    rw [← LinearMap.det_conj (W.mapQ W TQ hW) ψ]
    congr 1
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on _ q ?_
    intro x
    have hψ : ψ.symm (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (Submodule.Quotient.mk x) := by
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hψ,
      Submodule.mapQ_apply]
    rfl

end Langlands.BaseChange.TwistedLocalDescent
