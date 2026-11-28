import Langlands.GroupScheme.Rational.CentralNormOneLocalCorrection
import Langlands.GroupScheme.CentralIsogeny.FiniteGaloisCoefficientLift
import Langlands.GroupScheme.GaloisCocycleConstruction
import Langlands.GroupScheme.GaloisPointTower

/-! # Lifting quadratic cocycles through a central isogeny whose kernel is killed by `3`

Let `p : X ⟶ D` be a central isogeny over a field `F` of characteristic zero such that every
point of `X` over a field that is killed by `p` has cube one. This module proves two facts
that give a cochain proof of the lifting step and of the archimedean step of
Platonov–Rapinchuk, §6.8, Lemma 6.33.

* `IsCentralIsogeny.exists_cohomologous_map_of_cube_kernel`: on the cover `Spec E → Spec F` of
  a quadratic Galois extension, every cocycle of `D` is cohomologous to the image of a
  cocycle of `X` on the same cover.
* `IsCentralIsogeny.isTrivial_baseChange_of_cube_kernel`: over a field `K` whose algebraic
  closure has degree `2`, a cocycle of `X` is trivial on the full pullback cover as soon as
  its image in `D` is.

The source instead lifts the class to the absolute cohomology set `H¹(F, H × B)` after killing
its obstruction in `H²(F, H ∩ B)` by restriction–corestriction, and uses
`H¹(F_v, H ∩ B) = 1` at the archimedean places; it does not construct a lift on the same
quadratic cover.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open GaloisPoint

set_option backward.isDefEq.respectTransparency false

section Naturality

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)

/-- A homomorphism of group schemes commutes with the Galois action on coefficient points. -/
theorem affinePointsTarget_conjugate (L : Type u) [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k L)) :
    G.affinePointsTarget f (CommAlgCat.of k L) (conjugate k L G σ x) =
      conjugate k L H σ (G.affinePointsTarget f (CommAlgCat.of k L) x) :=
  (DFunLike.congr_fun
    (affinePointsTarget_naturality G f (CommAlgCat.ofHom σ.toAlgHom)) x).symm

/-- A homomorphism of group schemes commutes with extension of coefficient fields. -/
theorem affinePointsTarget_relativeExtend (L M : Type u) [Field L] [Field M] [Algebra k L]
    [Algebra k M] [Algebra L M] [IsScalarTower k L M] (x : G.affinePoints (CommAlgCat.of k L)) :
    G.affinePointsTarget f (CommAlgCat.of k M) (relativeExtend k L M G x) =
      relativeExtend k L M H (G.affinePointsTarget f (CommAlgCat.of k L) x) :=
  (DFunLike.congr_fun
    (affinePointsTarget_naturality G f (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M))) x).symm

/-- A homomorphism of group schemes commutes with the relative Galois action. -/
theorem affinePointsTarget_relativeConjugate (L M : Type u) [Field L] [Field M] [Algebra k L]
    [Algebra k M] [Algebra L M] [IsScalarTower k L M] (σ : M ≃ₐ[L] M)
    (x : G.affinePoints (CommAlgCat.of k M)) :
    G.affinePointsTarget f (CommAlgCat.of k M) (relativeConjugate k L M G σ x) =
      relativeConjugate k L M H σ (G.affinePointsTarget f (CommAlgCat.of k M) x) :=
  affinePointsTarget_conjugate f M (σ.restrictScalars k) x

end Naturality

namespace GaloisCocycle

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The Galois values of an image cocycle are the images of the Galois values. -/
theorem value_map (ξ : Cocycle G (cover k L)) (φ : G ⟶ H) (σ : L ≃ₐ[k] L) :
    value (ξ.map φ) σ = G.affinePointsTarget φ (CommAlgCat.of k L) (value ξ σ) :=
  rfl

end GaloisCocycle

/-- A finite group with exactly two elements consists of the identity and one involution. -/
theorem exists_eq_one_or_eq_of_card_eq_two {Γ : Type*} [Group Γ] [Fintype Γ]
    (h : Fintype.card Γ = 2) :
    ∃ s : Γ, s ≠ 1 ∧ s * s = 1 ∧ ∀ τ : Γ, τ = 1 ∨ τ = s := by
  classical
  obtain ⟨s, hs⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (1 : Γ)
  have hall : ∀ τ : Γ, τ = 1 ∨ τ = s := by
    intro τ
    by_contra hτ
    push Not at hτ
    have h3 : 2 < Fintype.card Γ :=
      Fintype.two_lt_card_iff.mpr ⟨1, s, τ, hs.symm, hτ.1.symm, hτ.2.symm⟩
    omega
  refine ⟨s, hs, ?_, hall⟩
  rcases hall (s * s) with h1 | h1
  · exact h1
  · exact absurd (mul_left_cancel (h1.trans (mul_one s).symm)) hs

namespace IsCentralIsogeny

variable {F : Type u} [Field F] {X D : GroupScheme (Spec (CommRingCat.of F))} {p : X ⟶ D}
  (hp : IsCentralIsogeny p)

include hp

/-- A point killed by a central isogeny commutes with every point over the same test scheme. -/
theorem commute_of_affinePointsTarget_eq_one {A : CommAlgCat.{u} (CommRingCat.of F)}
    {z : X.affinePoints A} (hz : X.affinePointsTarget p A z = 1) (x : X.affinePoints A) :
    Commute z x :=
  commute_of_mem_center ((isCentral_kernelι_iff p).mp hp.isCentral_kernelι _ z hz) x

section QuadraticLift

variable {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- A cochain proof of the lifting step in Platonov–Rapinchuk, §6.8, Lemma 6.33, on the same
quadratic cover (the source lifts by restriction–corestriction in `H²` instead). Let
`p : X ⟶ D` be a central isogeny over a field of characteristic zero whose kernel points over
fields have cube one, and
let `E/F` be a quadratic Galois extension. Then every cocycle of `D` on the cover
`Spec E → Spec F` is cohomologous to the image of a cocycle of `X` on the same cover.

If `a` is the value at the nontrivial automorphism `σ`, then `σ(a) = a⁻¹`, and twisting by
`a⁻¹` replaces `a` by `a³`. The cube of a lift of `a` over a larger Galois field descends to
a lift `x` of `a³` over `E`, `z = x σ(x)` is a central kernel point fixed by `σ`, and `y = x z`
satisfies `y σ(y) = z³ = 1`. -/
theorem exists_cohomologous_map_of_cube_kernel [CharZero F] [IsAffine X.X.left]
    [IsAffine D.X.left] (hE : Module.finrank F E = 2)
    (h3 : ∀ (K : Type u) [Field K] [Algebra F K] (x : X.affinePoints (CommAlgCat.of F K)),
      X.affinePointsTarget p (CommAlgCat.of F K) x = 1 → x ^ 3 = 1)
    (ξ : Cocycle D (GaloisCocycle.cover F E)) :
    ∃ ζ : Cocycle X (GaloisCocycle.cover F E), ξ.Cohomologous (ζ.map p) := by
  classical
  obtain ⟨σ, hσ, hσσ, hall⟩ := exists_eq_one_or_eq_of_card_eq_two (Γ := E ≃ₐ[F] E)
    (by rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hE])
  let pE := X.affinePointsTarget p (CommAlgCat.of F E)
  let a := GaloisCocycle.value ξ σ
  have ha : a * conjugate F E D σ a = 1 := by
    have h := GaloisCocycle.value_mul ξ σ σ
    rw [hσσ, GaloisCocycle.value_one] at h
    exact h.symm
  have haσ : conjugate F E D σ a = a⁻¹ := eq_inv_of_mul_eq_one_right ha
  obtain ⟨M, _, _, _, _, _, _, hlift⟩ :=
    hp.exists_finiteGalois_coefficient_lifts (k := F) (L := E) (fun _ : Unit => a)
  obtain ⟨b, hb⟩ := hlift ()
  let : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  let : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  let pM := X.affinePointsTarget p (CommAlgCat.of F M)
  have hfix : b ^ 3 ∈ relativeFixedSubgroup F E M X := by
    intro τ
    let c := b⁻¹ * relativeConjugate F E M X τ b
    have hc : pM c = 1 := by
      change pM (b⁻¹ * relativeConjugate F E M X τ b) = 1
      rw [map_mul, map_inv, affinePointsTarget_relativeConjugate, hb, relativeConjugate_extend,
        inv_mul_cancel]
    have hc3 : c ^ 3 = 1 := h3 M c hc
    have hbc : relativeConjugate F E M X τ b = b * c := by
      change _ = b * (b⁻¹ * _)
      group
    rw [map_pow, hbc, (hp.commute_of_affinePointsTarget_eq_one hc b).symm.mul_pow, hc3, mul_one]
  let x := relativeDescend F E M X ⟨b ^ 3, hfix⟩
  have hx : relativeExtend F E M X x = b ^ 3 := relativeExtend_descend F E M X _
  have hpx : pE x = a ^ 3 := by
    apply relativeExtend_injective F E M D
    rw [← affinePointsTarget_relativeExtend, hx, map_pow, hb, map_pow]
  let z := x * conjugate F E X σ x
  have hz : pE z = 1 := by
    change pE (x * conjugate F E X σ x) = 1
    rw [map_mul, affinePointsTarget_conjugate, hpx, map_pow, haσ, inv_pow, mul_inv_cancel]
  have hz3 : z ^ 3 = 1 := h3 E z hz
  have hzc (w : X.affinePoints (CommAlgCat.of F E)) : Commute z w :=
    hp.commute_of_affinePointsTarget_eq_one hz w
  have hσσx : conjugate F E X σ (conjugate F E X σ x) = x := by
    rw [← conjugate_mul, hσσ, conjugate_one]
  have hσz : conjugate F E X σ z = z := by
    calc
      conjugate F E X σ z = conjugate F E X σ x * x := by
        change conjugate F E X σ (x * conjugate F E X σ x) = _
        rw [map_mul, hσσx]
      _ = x⁻¹ * (z * x) := by
        change _ = x⁻¹ * (x * conjugate F E X σ x * x)
        group
      _ = z := by
        rw [(hzc x).eq]
        group
  let y := x * z
  have hy : y * conjugate F E X σ y = 1 := by
    change x * z * conjugate F E X σ (x * z) = 1
    rw [map_mul, hσz]
    calc
      x * z * (conjugate F E X σ x * z) = x * conjugate F E X σ x * z * z := by
        rw [mul_assoc x z, (hzc _).eq]
        group
      _ = z ^ 3 := (pow_three' z).symm
      _ = 1 := hz3
  have hpy : pE y = a ^ 3 := by
    change pE (x * z) = _
    rw [map_mul, hpx, hz, mul_one]
  let c : (E ≃ₐ[F] E) → X.affinePoints (CommAlgCat.of F E) := fun τ => if τ = 1 then 1 else y
  have hc : ∀ τ₁ τ₂, c (τ₁ * τ₂) = c τ₁ * conjugate F E X τ₁ (c τ₂) := by
    intro τ₁ τ₂
    rcases hall τ₁ with rfl | rfl <;> rcases hall τ₂ with rfl | rfl <;>
      simp only [c, hσσ, hσ, mul_one, one_mul, ↓reduceIte, map_one, conjugate_one, hy]
  let ζ := GaloisCocycle.ofValues c hc
  refine ⟨ζ, a⁻¹, fun a' b' => GaloisCocycle.toFun_eq_of_value_eq (ζ.map p) (ξ.twist a⁻¹)
    (fun τ => ?_) a' b'⟩
  rw [GaloisCocycle.value_map, GaloisCocycle.value_ofValues, GaloisCocycle.value_twist]
  rcases hall τ with rfl | rfl
  · simp only [c, ↓reduceIte, map_one, GaloisCocycle.value_one, conjugate_one, inv_inv, mul_one,
      mul_inv_cancel]
  · simp only [c, hσ, ↓reduceIte]
    rw [hpy, map_inv, haσ, inv_inv]
    exact pow_three' a

end QuadraticLift

section LocalCorrection

variable {K L M : Type u} [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M] [Normal F L]

/-- Over a field `K` with an algebraically closed Galois extension `M` of degree `2`, a
cocycle of `X` whose image in `D` is trivial on the full pullback cover is itself trivial
there, provided the kernel points of `p` over `M` have cube one.

The local central correction gives a crossed homomorphism `c` from `Gal(M/K)` to the kernel
points over `M`; with `s` the nontrivial automorphism, `k = c(s)` satisfies `k s(k) = 1` and
`k³ = 1`, so `c(τ) = m τ(m)⁻¹` for `m = k⁻¹`. -/
theorem isTrivial_baseChange_of_cube_kernel [IsAlgClosed M] [FiniteDimensional K M]
    [IsGalois K M] (hM : Module.finrank K M = 2)
    (h3 : ∀ x : X.affinePoints (CommAlgCat.of F M),
      X.affinePointsTarget p (CommAlgCat.of F M) x = 1 → x ^ 3 = 1)
    (ζ : Cocycle X (GaloisCocycle.cover F L))
    (h : ((ζ.map p).baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    (ζ.baseChangePullback (Spec.algebraMap F K)).IsTrivial := by
  classical
  obtain ⟨d⟩ := hp.nonempty_localCentralCorrection (K := K) (M := M) ζ h
  obtain ⟨s, hs, hss, hall⟩ := exists_eq_one_or_eq_of_card_eq_two (Γ := M ≃ₐ[K] M)
    (by rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hM])
  let N := GroupScheme.affinePoints hp.commutativeKernel.toGrp (CommAlgCat.of F M)
  let j := hp.kernelPointInclusion M
  have hj : Function.Injective j := fun _ _ h => (cancel_mono (kernelι p).hom.hom).mp h
  let g (σ : M ≃ₐ[K] M) := relativeConjugate F K M X σ
  let gN (σ : M ≃ₐ[K] M) := relativeConjugate F K M hp.commutativeKernel.toGrp σ
  have hjg (σ : M ≃ₐ[K] M) (n : N) : j (gN σ n) = g σ (j n) :=
    Category.assoc (GaloisCocycle.arrow F M (σ.restrictScalars F)) n (kernelι p).hom.hom
  have hone (σ : M ≃ₐ[K] M) (hσ : σ = 1) (n : N) : gN σ n = n := by
    subst hσ
    exact conjugate_one F M _ n
  have hc1 : d.correction 1 = 1 := by
    have h := d.correction_mul 1 1
    rw [mul_one, hone 1 rfl] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  let k := d.correction s
  have hk : k * gN s k = 1 := by
    have h := d.correction_mul s s
    rw [hss, hc1] at h
    exact h.symm
  have hks : gN s k = k⁻¹ := eq_inv_of_mul_eq_one_right hk
  have hk3 : k ^ 3 = 1 := by
    apply hj
    rw [map_pow, map_one]
    exact h3 (j k) ((mem_range_kernelι_iff p (j k)).mp ⟨k, rfl⟩)
  let m : N := k⁻¹
  have hcm (σ : M ≃ₐ[K] M) : d.correction σ = m * (gN σ m)⁻¹ := by
    rcases hall σ with h | h <;> rw [h]
    · rw [hc1, hone 1 rfl, mul_inv_cancel]
    · change k = k⁻¹ * (gN s k⁻¹)⁻¹
      rw [map_inv, hks, inv_inv]
      calc k = k * k ^ 3 := by rw [hk3, mul_one]
        _ = k⁻¹ * k⁻¹ * (k ^ 3) ^ 2 := by group
        _ = k⁻¹ * k⁻¹ := by rw [hk3, one_pow, mul_one]
  let A (σ : M ≃ₐ[K] M) := relativeExtend F L M X
    (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L))
  let w := d.cochain * j m
  have hCob (σ : M ≃ₐ[K] M) : A σ = w * (g σ w)⁻¹ := by
    have hspec : j (d.correction σ) = d.cochain⁻¹ * A σ * g σ d.cochain := d.correction_spec σ
    have hA : A σ = d.cochain * j (d.correction σ) * (g σ d.cochain)⁻¹ := by
      rw [hspec]
      group
    rw [hA, hcm]
    simp only [w, map_mul, map_inv, hjg]
    group
  apply GaloisCocycle.isTrivial_baseChange_of_scalarExtension (M := M)
  let P := GaloisCocycle.scalarExtensionPointsEquiv (K := K) (M := M) X
  let y := P.symm w
  refine ⟨y, ?_⟩
  apply GaloisCocycle.toFun_eq_of_value_eq _ (Cocycle.coboundary y)
  intro σ
  apply P.injective
  rw [GaloisCocycle.value_coboundary, map_mul, map_inv,
    GaloisCocycle.scalarExtensionPointsEquiv_conjugate y σ,
    show P y = w from P.apply_symm_apply w, GaloisCocycle.value_scalarExtension]
  exact hCob σ

end LocalCorrection

end IsCentralIsogeny

end Langlands.GroupScheme
