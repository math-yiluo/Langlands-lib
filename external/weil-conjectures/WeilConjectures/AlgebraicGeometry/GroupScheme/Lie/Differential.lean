/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket

/-!
# The differential of a homomorphism of group schemes over a field

The differential `df : Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H` over a
field `k` sends a tangent vector `v : Spec k[ε] ⟶ G` to `v ≫ f`. It is a homomorphism of Lie
algebras, functorial, injective for monomorphisms and bijective for open immersions. If the
commutators of `H` factor through a subgroup scheme `G ⟶ H`, then the brackets of `Lie(H)` lie in
`Lie(G)`; the tangent vectors of a central subgroup scheme are central.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt IsLocalRing
open scoped MonObj commutatorElement

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]

/-! ### Composing points with a homomorphism -/

section KerPost

variable {A : Type u} [CommRing A] [Algebra k A]

theorem comp_mem_pointsKer {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] {p : points G A}
    (hp : p ∈ pointsKer G π) : p ≫ f ∈ pointsKer H π := by
  rw [mem_pointsKer] at hp ⊢
  change points.map G π p ≫ f = 1
  rw [hp, MonObj.one_comp]

/-- Composition with a homomorphism of group schemes `f : G ⟶ H`, on points reducing to the
identity. -/
noncomputable def kerPost {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] :
    pointsKer G π →* pointsKer H π where
  toFun p := ⟨p.1 ≫ f, comp_mem_pointsKer f p.2⟩
  map_one' := Subtype.ext (MonObj.one_comp f)
  map_mul' p q := Subtype.ext ((IsMonHom.monoidHom f _).map_mul p.1 q.1)

@[simp]
theorem coe_kerPost {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] (p : pointsKer G π) :
    (kerPost f p : points H A) = p.1 ≫ f :=
  rfl

theorem kerMap_kerPost {B : Type u} [CommRing B] [Algebra k B] {πA : A →ₐ[k] k}
    {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = πA) (f : G ⟶ H) [IsMonHom f]
    (p : pointsKer G πA) : kerMap ψ hψ (kerPost f p) = kerPost f (kerMap ψ hψ p) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem kerPost_tangentMap [IsLocalRing A] {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] (m : A)
    (hm : m * m = 0) (hπ : π m = 0) (v : pointsKer G aug₁) :
    kerPost f (tangentMap m hm hπ v) = tangentMap m hm hπ (kerPost f v) :=
  (kerMap_kerPost _ _ f v).symm

theorem kerPost_injective {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (kerPost (π := π) f) := fun _ _ h ↦
  Subtype.ext ((cancel_mono f).1 (congrArg Subtype.val h))

/-- A homomorphism of group schemes preserves the bracket of tangent vectors. -/
theorem tangentBracket_kerPost (f : G ⟶ H) [IsMonHom f] (v w : pointsKer G aug₁) :
    tangentBracket (kerPost f v) (kerPost f w) = kerPost f (tangentBracket v w) := by
  apply tangentMul_injective
  rw [tangentMul_tangentBracket, tangentMul, ← kerPost_tangentMap, ← tangentMul,
    tangentMul_tangentBracket, map_commutatorElement, kerPost_tangentMap, kerPost_tangentMap]

end KerPost

/-! ### The differential -/

theorem lieEquivTangent_infPointsMap (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    lieEquivTangent H (lieEquiv H (infPointsMap f ((lieEquiv G).symm x))) =
      kerPost f (lieEquivTangent G x) := by
  apply Subtype.ext
  change inv dualNumbersToSpecOver ≫ _ = (inv dualNumbersToSpecOver ≫ _) ≫ f
  rw [Equiv.symm_apply_apply, coe_infPointsMap_apply, Category.assoc]

/-- The differential `df : Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H` over
`k`: on tangent vectors, `v ↦ v ≫ f`. It is a homomorphism of Lie algebras.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def differential (f : G ⟶ H) [IsMonHom f] : Lie G →ₗ⁅k⁆ Lie H where
  toFun x := lieEquiv H (infPointsMap f ((lieEquiv G).symm x))
  map_add' x y := by
    simp only [lieEquiv_symm_add, map_mul, lieEquiv_mul]
  map_smul' c x := by
    change _ = c • lieEquiv H _
    rw [show c • x = (Scheme.ΓSpecIso (.of k)).inv.hom c • x from rfl, lieEquiv_symm_smul,
      show infPointsMap f (infPointsScale G _ ((lieEquiv G).symm x)) =
        infPointsScale H _ (infPointsMap f ((lieEquiv G).symm x)) from
          Subtype.ext ((coe_infPointsMap_apply _ _).trans (Category.assoc _ _ _))]
    exact toLie_infPointsScale H _ _
  map_lie' {x y} := by
    apply (lieEquivTangent H).injective
    change lieEquivTangent H (lieEquiv H (infPointsMap f ((lieEquiv G).symm ⁅x, y⁆))) =
      lieEquivTangent H ⁅lieEquiv H (infPointsMap f ((lieEquiv G).symm x)),
        lieEquiv H (infPointsMap f ((lieEquiv G).symm y))⁆
    rw [lieEquivTangent_infPointsMap, lieEquivTangent_lie, lieEquivTangent_lie,
      lieEquivTangent_infPointsMap, lieEquivTangent_infPointsMap, tangentBracket_kerPost]

theorem differential_apply (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    differential f x = lieEquiv H (infPointsMap f ((lieEquiv G).symm x)) :=
  rfl

theorem lieEquivTangent_differential (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    lieEquivTangent H (differential f x) = kerPost f (lieEquivTangent G x) :=
  lieEquivTangent_infPointsMap f x

/-- The tangent point of the image of a tangent vector under a homomorphism is the image of its
tangent point. -/
theorem tangentPoint_differential (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    tangentPoint (differential f x) = tangentPoint x ≫ f := by
  simp only [tangentPoint, differential_apply, Equiv.symm_apply_apply,
    coe_infPointsEquivTangentGroup_apply, coe_infPointsMap_apply, Category.assoc]

theorem differential_congr {f g : G ⟶ H} [IsMonHom f] [IsMonHom g] (e : f = g) :
    differential f = differential g := by
  subst e; rfl

theorem differential_id : differential (𝟙 G) = LieHom.id := by
  ext x
  rw [differential_apply, LieHom.id_apply]
  conv_rhs => rw [← (lieEquiv G).apply_symm_apply x]
  congr 1

theorem differential_comp {K : Over (Spec (.of k))} [GrpObj K] (f : G ⟶ H) (g : H ⟶ K)
    [IsMonHom f] [IsMonHom g] : differential (f ≫ g) = (differential g).comp (differential f) := by
  ext x
  rw [LieHom.comp_apply, differential_apply, differential_apply, differential_apply,
    Equiv.symm_apply_apply]
  congr 1

/-- The differential of a monomorphism of group schemes, for instance of a closed immersion, is
injective. -/
theorem differential_injective (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (differential f) := fun x y h ↦ by
  apply (lieEquivTangent G).injective
  apply kerPost_injective f
  rw [← lieEquivTangent_differential, ← lieEquivTangent_differential, h]

/-- If the commutators of the points of `H` with values in `k[ε, δ]/(ε², δ²)` factor through the
subgroup scheme `f : G ⟶ H`, then the brackets of tangent vectors of `H` are tangent to `G`: the
bracket is the mixed term of the commutator of the points `1 + εx` and `1 + δy`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem lie_mem_range_differential_of_commutator_mem (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : points H (DualNumber (DualNumber k)),
      ⁅a, b⁆ ∈ (IsMonHom.monoidHom f _).range)
    (x y : Lie H) : ⁅x, y⁆ ∈ (differential f).range := by
  set c := ⁅tangentEps (lieEquivTangent H x), tangentDel (lieEquivTangent H y)⁆
  obtain ⟨d, hd⟩ := hf (tangentEps (lieEquivTangent H x)).1 (tangentDel (lieEquivTangent H y)).1
  have hd' : d ≫ f = c.1 := by
    rw [← IsMonHom.monoidHom_apply, hd]
    simp [c, commutatorElement_def]
  have hd₀ : d ∈ pointsKer G (aug₂ (k := k)) := by
    rw [mem_pointsKer]
    apply (cancel_mono f).1
    rw [MonObj.one_comp]
    change (_ ≫ d) ≫ f = 1
    rw [Category.assoc, hd']
    exact mem_pointsKer.1 c.2
  have hc : kerPost f ⟨d, hd₀⟩ = c := Subtype.ext hd'
  have h₁ : kerMap fst₂ aug₁_comp_fst₂ (⟨d, hd₀⟩ : pointsKer G (aug₂ (k := k))) = 1 := by
    apply kerPost_injective f
    rw [← kerMap_kerPost, hc, kerMap_fst₂_commutator, map_one]
  have h₂ : kerMap rho₂ aug₁_comp_rho₂ (⟨d, hd₀⟩ : pointsKer G (aug₂ (k := k))) = 1 := by
    apply kerPost_injective f
    rw [← kerMap_kerPost, hc, kerMap_rho₂_commutator, map_one]
  obtain ⟨u, hu⟩ := exists_tangentMul_eq _ h₁ h₂
  refine (LieHom.mem_range _ _).2 ⟨(lieEquivTangent G).symm u, ?_⟩
  apply (lieEquivTangent H).injective
  rw [lieEquivTangent_differential, Equiv.apply_symm_apply, lieEquivTangent_lie]
  apply tangentMul_injective
  rw [tangentMul, ← kerPost_tangentMap, ← tangentMul, hu, hc, tangentMul_tangentBracket]

/-- If the subgroup scheme `f : G ⟶ H` contains the commutators of `H`, then the brackets of
tangent vectors of `H` are tangent to `G`. (blueprint: `lemma-restriction-normal-subgroup`) -/
theorem lie_mem_range_differential_of_containsCommutators (f : G ⟶ H) [IsMonHom f] [Mono f]
    [IsMonHom.ContainsCommutators f] (x y : Lie H) : ⁅x, y⁆ ∈ (differential f).range :=
  lie_mem_range_differential_of_commutator_mem f (fun a b ↦ MonoidHom.mem_range.2
    (IsMonHom.ContainsCommutators.exists_comp_eq_commutator f a b)) x y

/-- The tangent vectors of a central subgroup scheme `f : G ⟶ H` are central in `Lie(H)`: for
`x ∈ Lie(G)` and `y ∈ Lie(H)` the points `1 + εx` and `1 + δy` commute over `k[ε, δ]/(ε², δ²)`,
so the mixed term `⁅df(x), y⁆` of their commutator vanishes. (blueprint:
`lemma-stable-subspaces-center`) -/
theorem range_differential_le_center (f : G ⟶ H) [IsMonHom f]
    (hf : ∀ (X : Over (Spec (.of k))) (a : X ⟶ G) (b : X ⟶ H), (a ≫ f) * b = b * (a ≫ f)) :
    (differential f).range ≤ (LieAlgebra.center k (Lie H) : LieSubalgebra k (Lie H)) := by
  rintro _ ⟨x, rfl⟩
  change differential f x ∈ LieModule.maxTrivSubmodule k (Lie H) (Lie H)
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  rw [← lie_skew, neg_eq_zero]
  apply (lieEquivTangent H).injective
  rw [lieEquivTangent_lie, lieEquivTangent_differential,
    show lieEquivTangent H 0 = 1 by
      rw [← lieEquivTangent_symm_one (G := H), Equiv.apply_symm_apply]]
  apply tangentMul_injective
  rw [tangentMul_tangentBracket, show tangentMul (1 : pointsKer H aug₁) = 1 from map_one _,
    tangentEps, ← kerPost_tangentMap,
    commutatorElement_eq_one_iff_mul_comm]
  exact Subtype.ext (hf _ _ _)

/-- The differential of an open immersion of group schemes `f : G ⟶ H` is bijective: every
tangent vector of `H` has the same underlying map as the identity section, hence factors
through the open subscheme `G`. -/
theorem differential_bijective_of_isOpenImmersion (f : G ⟶ H) [IsMonHom f]
    [IsOpenImmersion f.left] : Function.Bijective (differential f) := by
  have : Mono f := by
    have : Mono f.left := inferInstance
    exact (Over.forget _).mono_of_mono_map this
  refine ⟨differential_injective f, fun y ↦ ?_⟩
  set q := lieEquivTangent H y
  have hone : f.left (onePoint G) = onePoint H := by
    have := congrArg (fun g ↦ g.left (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩))
      (IsMonHom.one_hom f)
    exact this
  have hrange : Set.range q.1.left.base ⊆ Set.range f.left.base := by
    rintro _ ⟨z, rfl⟩
    have hU : q.1.left (closedPoint (DualNumber k)) ∈ f.left.opensRange := by
      rw [closedPoint_eq_onePoint q.2]
      exact ⟨onePoint G, hone⟩
    have h := Scheme.preimage_eq_top_of_closedPoint_mem
      (q.1.left : Spec (.of (DualNumber k)) ⟶ H.left) hU
    have hz : z ∈ (q.1.left : Spec (.of (DualNumber k)) ⟶ H.left) ⁻¹ᵁ f.left.opensRange := by
      rw [h]; trivial
    exact hz
  have hfac := IsOpenImmersion.lift_fac f.left q.1.left hrange
  let p : points G (DualNumber k) :=
    Over.homMk (IsOpenImmersion.lift f.left q.1.left hrange) (by
      rw [← Over.w f, reassoc_of% hfac]
      exact Over.w q.1)
  have hpq : p ≫ f = q.1 := Over.OverMorphism.ext hfac
  have hp : p ∈ pointsKer G (aug₁ (k := k)) := by
    rw [mem_pointsKer]
    apply (cancel_mono f).1
    rw [MonObj.one_comp]
    change (_ ≫ p) ≫ f = 1
    rw [Category.assoc, hpq]
    exact mem_pointsKer.1 q.2
  refine ⟨(lieEquivTangent G).symm ⟨p, hp⟩, (lieEquivTangent H).injective ?_⟩
  rw [lieEquivTangent_differential, Equiv.apply_symm_apply]
  exact Subtype.ext hpq

/-- An open immersion of group schemes `G ⟶ H` identifies `Lie(G)` with `Lie(H)`. -/
noncomputable def lieEquivOfIsOpenImmersion (f : G ⟶ H) [IsMonHom f] [IsOpenImmersion f.left] :
    Lie G ≃ₗ⁅k⁆ Lie H :=
  LieEquiv.ofBijective _ (differential_bijective_of_isOpenImmersion f)

end AlgebraicGeometry.GrpObj
