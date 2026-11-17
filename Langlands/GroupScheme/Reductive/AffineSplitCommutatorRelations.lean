import Langlands.GroupScheme.Reductive.LocalSplitConeCommutator
import Langlands.GroupScheme.Reductive.LocalSplitHeightCommutator
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField

/-! # Commutator relations of root groups on every test scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Cone

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {v : J → (Ga R ⟶ G)}

/-- **The commutator of two root groups along an ordered cone, on every test scheme.** This is
`exists_rootPoint_comm_cone` with the identity holding for global functions `x`, `y` on an
arbitrary scheme `Z` over `Spec R`, not only on affine tests. -/
theorem exists_rootPoint_comm_cone_sections (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {β ε : J} (hβε : P.root β ≠ -P.root ε) (hne : β ≠ ε) (L : List J) (hL : L.Nodup)
    (ex : Fin L.length → ℕ × ℕ)
    (hex : ∀ r, P.root (L.get r) = ((ex r).1 : ℤ) • P.root β + ((ex r).2 : ℤ) • P.root ε)
    (hex1 : ∀ r, 1 ≤ (ex r).1 ∧ 1 ≤ (ex r).2)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root β + (dT : ℤ) • P.root ε = P.root α → α ∈ L) :
    ∃ C : Fin L.length → R, ∀ (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)),
      (rootPoint (v β) Z x * rootPoint (v ε) Z y)⁻¹ *
          (rootPoint (v ε) Z y * rootPoint (v β) Z x) =
        (List.ofFn fun r => rootPoint (v (L.get r)) Z
          (scalarMap Z (C r) * x ^ (ex r).1 * y ^ (ex r).2)).prod := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b, hβ, hε⟩ := Langlands.LinearAlgebra.exists_base_isPos_pair P hβε
  have hli : LinearIndependent ℤ ![P.root β, P.root ε] :=
    RootPairing.IsReduced.linearIndependent P hne hβε
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  have hLpos : ∀ x ∈ L, b.IsPos x := by
    intro x hx
    obtain ⟨r, rfl⟩ := List.mem_iff_get.mp hx
    have h := hν (L.get r)
    rw [hex r, coPairing_combo, hν, hν] at h
    have h1 := hex1 r
    have hb : 0 < b.height β := hβ
    have he : 0 < b.height ε := hε
    rw [RootPairing.Base.isPos_iff]
    by_contra hneg
    have hneg := not_lt.mp hneg
    have : d * b.height (L.get r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le hneg
    have h2 : 0 < ((ex r).1 : ℤ) * (d * b.height β) + ((ex r).2 : ℤ) * (d * b.height ε) := by
      have : (1 : ℤ) ≤ (ex r).1 := by exact_mod_cast h1.1
      have : (1 : ℤ) ≤ (ex r).2 := by exact_mod_cast h1.2
      positivity
    linarith
  obtain ⟨m, n, neg, pos, hpos', hopen, ν', hneg, hpos⟩ :=
    exists_cell_initial hG hmax hP hv b L hL hLpos
  have := hopen
  have hTE : TorusEquivariant i (fun α => P.root α) v := fun α Z t c => (hv α).equivariant Z t c
  set k := pos.symm ⟨β, hβ⟩ with hkdef
  set l := pos.symm ⟨ε, hε⟩ with hldef
  have hk : ((pos k : {α // b.IsPos α}) : J) = β := by simp [k]
  have hl : ((pos l : {α // b.IsPos α}) : J) = ε := by simp [l]
  obtain ⟨E, hE⟩ := exists_isUnivComm (i := i) (neg := fun k => (neg k : J)) hTE ν' hneg hpos k l
  -- the coordinates outside the initial segment vanish
  have hzero : ∀ j : Fin n, E (Fin.natAdd L.length j) = 0 := by
    intro j
    refine hE.eq_zero_of_forall_ne (i := i) (neg := fun k => (neg k : J)) hTE _ ?_
    intro dS dT h1 h2 heq
    simp only [hk, hl] at heq
    obtain ⟨r, hr⟩ := List.mem_iff_get.mp (hcone _ dS dT h1 h2 heq)
    have : Fin.castAdd n r = Fin.natAdd L.length j := by
      apply pos.injective
      apply Subtype.ext
      rw [hpos' r, hr]
    have hv' := congrArg Fin.val this
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv'
    omega
  -- the coordinate at `L r` is a single monomial
  have hmono : ∀ r : Fin L.length, E (Fin.castAdd n r) =
      Polynomial.monomial (ex r).2 (Polynomial.monomial (ex r).1
        (((E (Fin.castAdd n r)).coeff (ex r).2).coeff (ex r).1)) := by
    intro r
    ext dT dS
    rw [Polynomial.coeff_monomial, apply_ite (fun p : Polynomial R => p.coeff dS),
      Polynomial.coeff_monomial, Polynomial.coeff_zero]
    by_cases hnz : ((E (Fin.castAdd n r)).coeff dT).coeff dS = 0
    · rw [hnz]
      split_ifs with h1 h2
      · subst h1; subst h2; exact hnz.symm.trans rfl
      · rfl
      · rfl
    · have hw := hE.weight (neg := fun k => (neg k : J)) hTE (Fin.castAdd n r) hnz
      simp only [hk, hl, hpos' r, hex r] at hw
      have h0 : ((dS : ℤ) - (ex r).1) • P.root β + ((dT : ℤ) - (ex r).2) • P.root ε = 0 := by
        rw [sub_smul, sub_smul]
        rw [← sub_eq_zero] at hw
        rw [← hw]
        abel
      have := LinearIndependent.pair_iff.mp hli _ _ h0
      have e1 : dS = (ex r).1 := by omega
      have e2 : dT = (ex r).2 := by omega
      subst e1; subst e2
      simp
  refine ⟨fun r => ((E (Fin.castAdd n r)).coeff (ex r).2).coeff (ex r).1, fun Z x y => ?_⟩
  have h := hE.posComm_eq_sections Z x y
  simp only [posComm, hk, hl] at h
  rw [h, orderedProduct_initial v (fun k => (pos k : J)) _ _ (fun j => by
    rw [hzero j, map_zero])]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  simp only [hpos' r]
  rw [hmono r]
  congr 1
  simp [lineEvalSections, Polynomial.eval₂_monomial, scalarMap, Gm.specHomEquiv]

/-- **Commutator relations of root groups on every test scheme** (Conrad, *Reductive group
schemes*, Proposition 5.1.14). For roots `a`, `c` with `c ≠ ±a` and every enumeration `e` of the
roots `pa + qc` with `p, q > 0`, there are such exponents `p k`, `q k` and constants `C k ∈ R` with
`u_a(x) u_c(y) u_a(-x) u_c(-y) = ∏ₖ u_{e k}(C_k xᵖ⁽ᵏ⁾ yᑫ⁽ᵏ⁾)` for all global functions `x`, `y`
on every scheme over `Spec R`. -/
theorem exists_commutator_orderedProduct (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    (a c : J) (hca : P.root c ≠ P.root a) (hcna : P.root c ≠ -P.root a) (n : ℕ)
    (e : Fin n ≃
      {d : J // ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root d = p • P.root a + q • P.root c}) :
    ∃ (p q : Fin n → ℕ) (C : Fin n → R),
      (∀ k, 0 < p k ∧ 0 < q k ∧ P.root (e k : J) = p k • P.root a + q k • P.root c) ∧
      ∀ (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)),
        rootPoint (v a) Z x * rootPoint (v c) Z y * rootPoint (v a) Z (-x) *
            rootPoint (v c) Z (-y) =
          orderedProduct v (fun k => (e k : J)) Z
            (fun k => scalarMap Z (C k) * x ^ p k * y ^ q k) := by
  classical
  choose p q hp hq hpq using fun k => (e k).2
  let L : List J := List.ofFn fun k => (e k : J)
  have hlen : L.length = n := List.length_ofFn
  have hLget : ∀ r : Fin L.length, L.get r = (e (Fin.cast hlen r) : J) := by
    intro r
    simp [L]
    rfl
  have hL : L.Nodup := by
    refine List.nodup_ofFn.mpr ?_
    intro k k' h
    exact e.injective (Subtype.ext h)
  have hne : c ≠ a := fun h => hca (by rw [h])
  let ex : Fin L.length → ℕ × ℕ := fun r => (q (Fin.cast hlen r), p (Fin.cast hlen r))
  have hex : ∀ r, P.root (L.get r) = ((ex r).1 : ℤ) • P.root c + ((ex r).2 : ℤ) • P.root a := by
    intro r
    rw [hLget r, hpq, natCast_zsmul, natCast_zsmul, add_comm]
  have hex1 : ∀ r, 1 ≤ (ex r).1 ∧ 1 ≤ (ex r).2 := fun r => ⟨hq _, hp _⟩
  have hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root c + (dT : ℤ) • P.root a = P.root α → α ∈ L := by
    intro α dS dT h1 h2 h
    have hα : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root α = p • P.root a + q • P.root c :=
      ⟨dT, dS, h2, h1, by rw [← h, natCast_zsmul, natCast_zsmul, add_comm]⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨α, hα⟩
    refine List.mem_ofFn.mpr ⟨k, ?_⟩
    rw [hk]
  obtain ⟨C', hC'⟩ := exists_rootPoint_comm_cone_sections hG hmax hP hv hcna hne L hL ex hex hex1
    hcone
  refine ⟨p, q, fun k => C' (Fin.cast hlen.symm k) * (-1) ^ (p k + q k),
    fun k => ⟨hp k, hq k, hpq k⟩, fun Z x y => ?_⟩
  have h := hC' Z (-y) (-x)
  simp only [rootPoint_neg] at h
  have hl : rootPoint (v a) Z x * rootPoint (v c) Z y * rootPoint (v a) Z (-x) *
      rootPoint (v c) Z (-y) =
      ((rootPoint (v c) Z y)⁻¹ * (rootPoint (v a) Z x)⁻¹)⁻¹ *
        ((rootPoint (v a) Z x)⁻¹ * (rootPoint (v c) Z y)⁻¹) := by
    rw [rootPoint_neg, rootPoint_neg]
    group
  rw [hl, h, orderedProduct, List.ofFn_congr hlen]
  congr 1
  apply List.ofFn_inj.mpr
  funext k
  have hk : Fin.cast hlen (Fin.cast hlen.symm k) = k := by ext; rfl
  simp only [hLget, ex, hk, map_mul, map_pow, map_neg, map_one]
  congr 1
  ring

end Cone

end LocalSplitCell

end Langlands.GroupScheme
