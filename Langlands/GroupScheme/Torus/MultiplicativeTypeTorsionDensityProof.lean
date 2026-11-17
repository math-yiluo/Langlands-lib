import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDensityStatement
import Langlands.GroupScheme.Torus.DiagonalizableTorsionDensity
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.AbelianScheme.KernelBaseChange

/-! # Proof: the torsion subgroups of a group of multiplicative type are dense -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorsionDensity

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
/-- **Descent of torsion density along a field extension.** Let `G` be a group scheme over `k`
whose base change to an extension `K` is isomorphic to `H`. If every closed immersion into `H`
through which all `n`-torsion points (`n ∈ P`) factor is an isomorphism, the same holds for `G`. -/
theorem isIso_of_baseChange (G : GroupScheme (Spec (CommRingCat.of k)))
    (H : GroupScheme (Spec (CommRingCat.of K)))
    (e : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅ H)
    (P : ℕ → Prop)
    (hH : ∀ (Z' : Scheme.{u}) (z' : Z' ⟶ H.X.left), IsClosedImmersion z' →
      (∀ n, P n → ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ H.X), x ^ n = 1 →
        ∃ y : T.left ⟶ Z', y ≫ z' = x.left) → IsIso z')
    (Z : Scheme.{u}) (z : Z ⟶ G.X.left) (hz : IsClosedImmersion z)
    (h : ∀ n, P n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1 →
      ∃ y : T.left ⟶ Z, y ≫ z = x.left) : IsIso z := by
  obtain ⟨h1, h2, h3⟩ := fieldExtension_fpqc k K
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K)) with hb
  let g := pullback.fst G.X.hom b
  let z' : pullback z g ⟶ pullback G.X.hom b := pullback.snd z g
  have hiso : IsIso (z' ≫ e.hom.hom.hom.left) := by
    apply hH _ _ inferInstance
    intro n hn T x hx
    let x1 : T ⟶ ((GroupScheme.baseChange b).obj G).X := x ≫ e.inv.hom.hom
    have hx1 : x1 ^ n = 1 := by
      have := congrArg (isoPointsEquiv e.symm T) hx
      rwa [map_pow, map_one] at this
    have hx2 : baseChangePointsEquiv b G T x1 ^ n = 1 := by
      rw [← map_pow, hx1, map_one]
    obtain ⟨y, hy⟩ := h n hn _ _ hx2
    refine ⟨pullback.lift y x1.left hy, ?_⟩
    rw [← Category.assoc, pullback.lift_snd, ← Over.comp_left]
    congr 1
    change x ≫ e.inv.hom.hom ≫ e.hom.hom.hom = x
    rw [← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have : IsIso z' := IsIso.of_isIso_comp_right z' e.hom.hom.hom.left
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := z) (g := g)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ this

end TorsionDensity

namespace TorsionDensity

variable {k : Type u} [Field k]

/-- **Torsion density for a group of multiplicative type**, for a set `P` of exponents which
contains arbitrarily large multiples of every `N > 0` whose prime divisors are orders of elements
of a character group `Λ` of `G`. -/
theorem isIso_of_isMultiplicativeType (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsMultiplicativeType G) (P : ℕ → Prop)
    (hP : ∀ (K : Type u) [Field K] [Algebra k K] (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) →
      ∀ N : ℕ, 0 < N → (∀ p : ℕ, p.Prime → p ∣ N → ∃ x : Λ, x ≠ 0 ∧ p • x = 0) →
        ∀ M : ℕ, ∃ n, P n ∧ N ∣ n ∧ M < n)
    (Z : Scheme.{u}) (z : Z ⟶ G.X.left) (hz : IsClosedImmersion z)
    (h : ∀ n, P n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1 →
      ∃ y : T.left ⟶ Z, y ≫ z = x.left) : IsIso z := by
  obtain ⟨K, _, _, Λ, _, _, ⟨e⟩⟩ := hG
  obtain ⟨N, hN0, hNp, hNsep⟩ := exists_separating Λ
  refine isIso_of_baseChange G _ e P ?_ Z z hz h
  intro Z' z' hz' h'
  have := hz'
  exact isIso_of_torsion_factors (CommRingCat.of K) (hNsep (CommRingCat.of K)) P
    (hP K Λ e N hN0 hNp) z' h'

set_option backward.isDefEq.respectTransparency false in
/-- A smooth group scheme over `k` whose base change to `K` is `D(Λ)` has no `p`-torsion in `Λ`,
for `p` the characteristic exponent of `k`. -/
theorem eq_zero_of_smooth {K : Type u} [Field K] [Algebra k K] {Λ : Type u} [AddCommGroup Λ]
    [AddGroup.FG Λ] (G : GroupScheme (Spec (CommRingCat.of k))) (hsm : Smooth G.X.hom)
    (e : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (p : ℕ) [ExpChar k p] (x : Λ) (hx : p • x = 0) : x = 0 := by
  have : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  let i := (Over.forget _).mapIso ((Grp.forget _).mapIso e)
  have hw : (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp.X.hom =
      i.inv ≫ pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (Over.w e.inv.hom.hom).symm
  have hsmD : Smooth (Diagonalizable.groupScheme (CommRingCat.of K) Λ).X.hom := by
    rw [hw]
    infer_instance
  exact ((Diagonalizable.diagonalizableSmoothConnectedCriteria K p Λ).2.1).mp hsmD x hx

set_option backward.isDefEq.respectTransparency false in
/-- Two homomorphisms out of a group scheme `G` over a field with dense torsion (in the sense of
part 1) which agree on all torsion points are equal. -/
theorem eq_of_torsion (G H : GroupScheme (Spec (CommRingCat.of k)))
    (hG : ∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
      (∀ n : ℕ, 0 < n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ^ n = 1 → ∃ y : T.left ⟶ Z, y ≫ z = x.left) → IsIso z)
    (f₁ f₂ : G ⟶ H)
    (h : ∀ n : ℕ, 0 < n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ^ n = 1 → x ≫ f₁.hom.hom = x ≫ f₂.hom.hom) : f₁ = f₂ := by
  have : IsSeparated H.X.hom := fieldSeparated k H
  have hw : f₁.hom.hom.left ≫ H.X.hom = f₂.hom.hom.left ≫ H.X.hom := by
    rw [Over.w, Over.w]
  let ℓ := pullback.lift f₁.hom.hom.left f₂.hom.hom.left hw
  let z := pullback.snd (pullback.diagonal H.X.hom) ℓ
  have hiso : IsIso z := by
    apply hG _ z inferInstance
    intro n hn T x hx
    have hx' : x.left ≫ f₁.hom.hom.left = x.left ≫ f₂.hom.hom.left := by
      have := congrArg CommaMorphism.left (h n hn T x hx)
      simpa using this
    refine ⟨pullback.lift (x.left ≫ f₁.hom.hom.left) x.left ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext <;> simp [ℓ, hx']
  have hc := pullback.condition (f := pullback.diagonal H.X.hom) (g := ℓ)
  have e1 : z ≫ f₁.hom.hom.left = pullback.fst (pullback.diagonal H.X.hom) ℓ := by
    have := congrArg (· ≫ pullback.fst H.X.hom H.X.hom) hc
    simpa [ℓ, z] using this.symm
  have e2 : z ≫ f₂.hom.hom.left = pullback.fst (pullback.diagonal H.X.hom) ℓ := by
    have := congrArg (· ≫ pullback.snd H.X.hom H.X.hom) hc
    simpa [ℓ, z] using this.symm
  have ha : f₁.hom.hom.left = f₂.hom.hom.left := (cancel_epi z).mp (e1.trans e2.symm)
  apply Grp.hom_ext
  exact Over.OverMorphism.ext ha

end TorsionDensity

open TorsionDensity in
/-- **Density of torsion in groups of multiplicative type** (Milne, *Algebraic Groups* (2017),
Theorems 12.32 and 12.33 and Corollary 12.34). -/
theorem multiplicativeTypeTorsionDensity : MultiplicativeTypeTorsionDensityStatement.{u} := by
  intro k _ G hG
  have part1 : ∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
      (∀ n : ℕ, 0 < n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ^ n = 1 → ∃ y : T.left ⟶ Z, y ≫ z = x.left) → IsIso z := by
    refine isIso_of_isMultiplicativeType G hG (fun n => 0 < n) ?_
    intro K _ _ Λ _ _ _ N hN0 _ M
    exact ⟨N * (M + 1), Nat.mul_pos hN0 M.succ_pos, dvd_mul_right N _,
      Nat.lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_mul_of_pos_left _ hN0)⟩
  refine ⟨part1, fun hsm => ?_, fun H _ _ f₁ f₂ h => eq_of_torsion G H part1 f₁ f₂ h⟩
  refine isIso_of_isMultiplicativeType G hG (fun n => (n : k) ≠ 0) ?_
  intro K _ _ Λ _ _ e N hN0 hNp M
  obtain ⟨p, hp⟩ : ∃ p : ℕ, ExpChar k p := ⟨_, ringExpChar.expChar k⟩
  have hp1 : 0 < p := by
    have := hp
    exact expChar_pos k p
  refine ⟨N * (M * p + 1), ?_, dvd_mul_right _ _,
    Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_mul_of_pos_right M hp1))
      (Nat.le_mul_of_pos_left _ hN0)⟩
  cases hp with
  | zero => exact Nat.cast_ne_zero.mpr (by positivity)
  | prime hprime =>
    rw [Ne, CharP.cast_eq_zero_iff k p, hprime.dvd_mul]
    rintro (hpN | hp1)
    · obtain ⟨x, hx0, hx⟩ := hNp p hprime hpN
      have : ExpChar k p := ExpChar.prime hprime
      exact hx0 (eq_zero_of_smooth G hsm e p x hx)
    · exact hprime.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_left p M)).mp hp1))

end Langlands.GroupScheme
