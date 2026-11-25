/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtension
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf

/-!
# Counting in the extension of `μ_m` attached to a connected `ℤ/m`-torsor

Let `X` be a smooth proper connected curve over an algebraically closed field `k`, `m` an
integer prime to the characteristic, and `t` a `ℤ/m`-torsor over `X` with connected total space
`π : P ⟶ X`. With `V = π_* μ_m`, `D = τ - 1`, `K₁ = ker D ≅ μ_m` and `K₂ = ker D²`, we count:

* `#H²(X, V) = #H²(P, μ_m) = m`, since `π` is finite and `P` is again a smooth proper connected
  curve over `k` (`AlgebraicGeometry.Scheme.EtaleTorsor.card_sheafH_two_pushforwardMu`);
* `H²(X, V) ⟶ H²(X, K₂)` is surjective, since `ρ : V ⟶ K₂` is an epimorphism with torsion kernel
  and `H³` of torsion sheaves vanishes on a curve; so `#H²(X, K₂) ≤ m`;
* in the long exact sequence of `0 ⟶ K₁ ⟶ K₂ ⟶ K₁ ⟶ 0`, `H²(K₂) ⟶ H²(K₁)` is surjective and
  `#H²(K₁) = m`, so `H²(K₁) ⟶ H²(K₂)` vanishes and the connecting homomorphism
  `H¹(K₁) ⟶ H²(K₁)` is surjective.

Hence the cup product `H¹(X, μ_m) ⟶ H²(X, μ_m) ≅ ℤ/m` with the class of `t` is surjective
(`AlgebraicGeometry.Scheme.EtaleTorsor.surjective_cupMu`), and an integer `c` with `c • cupMu = 0`
is divisible by `m` (`AlgebraicGeometry.Scheme.EtaleTorsor.dvd_of_forall_nsmul_cupMu_eq_zero`).

## Main statements

- `CategoryTheory.Sheaf.H.surjective_δSucc_of_card_le`: a counting criterion for the
  surjectivity of a connecting homomorphism.
- `AlgebraicGeometry.Scheme.EtaleTorsor.surjective_cupMu`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.dvd_of_forall_nsmul_cupMu_eq_zero`.
-/

@[expose] public section

universe u v w w' u'

open CategoryTheory Limits

/-! ### Cohomology of sheaves: general facts -/

namespace CategoryTheory.Sheaf

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- An epimorphism of sheaves whose kernel has vanishing `Hⁿ⁺¹` induces a surjection on `Hⁿ`. -/
lemma H.surjective_map_of_epi {F G : Sheaf J AddCommGrpCat.{w}} (p : F ⟶ G) [Epi p] (n : ℕ)
    [Subsingleton (H (kernel p) (n + 1))] : Function.Surjective (H.map p n) := by
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p)) inferInstance
    (inferInstanceAs (Epi p))
  exact fun x ↦ (H.exact_map_δSucc hS n x).1 (Subsingleton.elim _ _)

/-- **A counting criterion for the connecting homomorphism.** Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0`
be short exact with `Hⁿ⁺¹(S.X₂)` finite and `Hⁿ⁺¹(S.X₂) ⟶ Hⁿ⁺¹(S.X₃)` surjective. If
`#Hⁿ⁺¹(S.X₂) ≤ #Hⁿ⁺¹(S.X₃)`, then `Hⁿ⁺¹(S.X₁) ⟶ Hⁿ⁺¹(S.X₂)` vanishes, so the connecting
homomorphism `Hⁿ(S.X₃) ⟶ Hⁿ⁺¹(S.X₁)` is surjective. -/
lemma H.surjective_δSucc_of_card_le {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n : ℕ) [Finite (H S.X₂ (n + 1))]
    (hg : Function.Surjective (H.map S.g (n + 1)))
    (hcard : Nat.card (H S.X₂ (n + 1)) ≤ Nat.card (H S.X₃ (n + 1))) :
    Function.Surjective (H.δSucc hS n) := by
  have : Finite (H S.X₃ (n + 1)) := Finite.of_surjective _ hg
  set g := H.map S.g (n + 1)
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv] at h1
  have hpos : 0 < Nat.card (H S.X₃ (n + 1)) := Nat.card_pos
  have hker : Nat.card g.ker ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by rw [mul_one, ← h1]; exact hcard) hpos
  have : Subsingleton g.ker := Finite.card_le_one_iff_subsingleton.1 hker
  intro y
  refine (H.exact_δSucc_map hS n y).1 ?_
  have hmem : H.map S.f (n + 1) y ∈ g.ker := (H.exact_map_map hS (n + 1) _).2 ⟨y, rfl⟩
  exact congrArg Subtype.val (Subsingleton.elim (⟨_, hmem⟩ : g.ker) 0)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

/-- A subsheaf of a sheaf killed by `N` is killed by `N`. -/
lemma nsmul_id_eq_zero_of_mono {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (i : F ⟶ G) [Mono i] {N : ℕ}
    (h : N • 𝟙 G = 0) : N • 𝟙 F = 0 := by
  rw [← cancel_mono i, zero_comp, Preadditive.nsmul_comp, Category.id_comp,
    ← Category.comp_id i, ← Preadditive.comp_nsmul, h, comp_zero]

namespace EtaleTorsor

variable {Y : Scheme.{u}} {m : ℕ} [NeZero m] (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) Y)

lemma nsmul_id_pushforwardMu : m • 𝟙 t.pushforwardMu = 0 := by
  rw [← cancel_mono (kernel.ι (m • 𝟙 t.pushforwardGm)), Preadditive.nsmul_comp,
    Category.id_comp, zero_comp]
  exact t.nsmul_kernel_ι_pushforwardMu

/-- `π_* μ_m` is the kernel of `m` on `π_* 𝔾ₘ`, as `π_*` preserves kernels. -/
noncomputable def lowerStarRootsOfUnityIso :
    (Etale.lowerStar AddCommGrpCat.{u + 1} t.π).obj (t.P.rootsOfUnitySheaf m) ≅
      t.pushforwardMu :=
  haveI : PreservesLimitsOfSize.{0, 0} (Etale.lowerStar AddCommGrpCat.{u + 1} t.π) :=
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t.π).rightAdjoint_preservesLimits
  PreservesKernel.iso (Etale.lowerStar AddCommGrpCat.{u + 1} t.π) (m • 𝟙 t.P.gmSheaf) ≪≫
    kernelIsoOfEq (by rw [Functor.map_nsmul, CategoryTheory.Functor.map_id])

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- For a connected `ℤ/m`-torsor `P` over a smooth proper connected curve `X` over an
algebraically closed field, `H²(X, π_* μ_m) = H²(P, μ_m)` has `m` elements: `π` is finite, and
`P` is again a smooth proper connected curve. -/
lemma card_sheafH_two_pushforwardMu {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X) [ConnectedSpace t.P] :
    Nat.card (Sheaf.H t.pushforwardMu 2) = m := by
  let : t.P.Over (Spec (.of k)) := ⟨t.π ≫ X ↘ Spec (.of k)⟩
  have := t.isFinite
  have := t.etale
  have : SmoothOfRelativeDimension 1 (t.P ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (t.π ≫ X ↘ Spec (.of k)))
  have : IsProper (t.P ↘ Spec (.of k)) := inferInstanceAs (IsProper (t.π ≫ X ↘ Spec (.of k)))
  have : Smooth (t.P ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : GeometricallyConnected (t.P ↘ Spec (.of k)) :=
    GeometricallyConnected.of_isSepClosed t.P
  have : GeometricallyIrreducible (t.P ↘ Spec (.of k)) :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected _
  have : GeometricallyReduced (t.P ↘ Spec (.of k)) := Smooth.geometricallyReduced _
  have : GeometricallyIntegral (t.P ↘ Spec (.of k)) :=
    .of_geometricallyReduced_of_geometricallyIrreducible _
  obtain ⟨e⟩ := card_sheafH_two_rootsOfUnitySheaf (k := k) (X := t.P) m hm
  rw [← Nat.card_eq_of_bijective _
      (Sheaf.H.bijective_map_of_isIso t.lowerStarRootsOfUnityIso.hom 2),
    Nat.card_eq_of_bijective _ (Etale.bijective_edgeMap_of_isFinite t.π _ 2)]
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod m)

/-- For a connected `ℤ/m`-torsor over a smooth proper connected curve over an algebraically
closed field, the cup product `H¹(X, μ_m) ⟶ H²(X, μ_m)` with its class is surjective. -/
theorem surjective_cupMu [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X]
    {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0) (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X)
    [ConnectedSpace t.P] : Function.Surjective t.cupMu := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve (X ↘ Spec (.of k)) :=
    { krullDim_le_one :=
        topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1 }
  have h3 (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : F ⟶ t.pushforwardMu)
      [Mono i] : Subsingleton (Sheaf.H F 3) :=
    IsCurve.subsingleton_sheafH_of_three_le (X ↘ Spec (.of k)) F
      (isTorsion_of_nsmul_id_eq_zero hm0 (nsmul_id_eq_zero_of_mono i t.nsmul_id_pushforwardMu))
      3 le_rfl
  -- `#H²(X, K₂) ≤ m`
  have : Subsingleton (Sheaf.H (kernel t.rhoK) (2 + 1)) := h3 _ (kernel.ι _)
  have := t.epi_rhoK
  have hρ := Sheaf.H.surjective_map_of_epi t.rhoK 2
  have hV := card_sheafH_two_pushforwardMu hm t
  have : Finite (Sheaf.H t.pushforwardMu 2) := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (Sheaf.H (kernel (t.muDiff ≫ t.muDiff)) 2) := Finite.of_surjective _ hρ
  have hK₂ : Nat.card (Sheaf.H (kernel (t.muDiff ≫ t.muDiff)) 2) ≤ m :=
    (Nat.card_le_card_of_surjective _ hρ).trans hV.le
  -- `#H²(X, K₁) = m`
  have := t.isIso_muUnit
  obtain ⟨e⟩ := card_sheafH_two_rootsOfUnitySheaf (X := X) m hm
  have hK₁ : Nat.card (Sheaf.H (kernel t.muDiff) 2) = m := by
    rw [← Nat.card_eq_of_bijective _ (Sheaf.H.bijective_map_of_isIso t.muUnit 2),
      Nat.card_congr e.toEquiv, Nat.card_zmod]
  -- the long exact sequence
  have : Subsingleton (Sheaf.H t.extSeq.X₁ (2 + 1)) := h3 _ (kernel.ι t.muDiff)
  have hg : Function.Surjective (Sheaf.H.map t.extSeq.g 2) := fun x ↦
    (Sheaf.H.exact_map_δSucc t.extSeq_shortExact 2 x).1 (Subsingleton.elim _ _)
  have : Finite (Sheaf.H t.extSeq.X₂ (1 + 1)) :=
    ‹Finite (Sheaf.H (kernel (t.muDiff ≫ t.muDiff)) 2)›
  have hδ := Sheaf.H.surjective_δSucc_of_card_le t.extSeq_shortExact 1 hg
    (by change _ ≤ Nat.card (Sheaf.H (kernel t.muDiff) 2); rw [hK₁]; exact hK₂)
  intro y
  obtain ⟨z, rfl⟩ := (Sheaf.H.bijective_map_of_isIso (inv t.muUnit) 2).2 y
  obtain ⟨w, rfl⟩ := hδ z
  obtain ⟨v, rfl⟩ := (Sheaf.H.bijective_map_of_isIso t.muUnit 1).2 w
  exact ⟨v, rfl⟩

/-- For a connected `ℤ/m`-torsor over a smooth proper connected curve over an algebraically
closed field, with `m` prime to the characteristic, an integer `c` such that `c` times the cup
product with the class of the torsor vanishes is divisible by `m`: the cup product
`H¹(X, μ_m) ⟶ H²(X, μ_m) ≅ ℤ/m` is surjective. -/
theorem dvd_of_forall_nsmul_cupMu_eq_zero [GeometricallyIntegral (X ↘ Spec (.of k))]
    [Nonempty X] {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X) [ConnectedSpace t.P] (c : ℕ)
    (hc : ∀ x, c • t.cupMu x = 0) : m ∣ c := by
  obtain ⟨e⟩ := card_sheafH_two_rootsOfUnitySheaf (X := X) m hm
  obtain ⟨x, hx⟩ := surjective_cupMu hm t (e.symm 1)
  have := congrArg e (hc x)
  rw [hx, map_nsmul, AddEquiv.apply_symm_apply, map_zero, nsmul_eq_mul, mul_one] at this
  exact (ZMod.natCast_eq_zero_iff c m).1 this

end EtaleTorsor

end AlgebraicGeometry.Scheme
