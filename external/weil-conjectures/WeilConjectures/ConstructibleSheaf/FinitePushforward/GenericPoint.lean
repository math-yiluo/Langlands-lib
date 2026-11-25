/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import Mathlib.RingTheory.Etale.Field

/-!
# Constant sheaves on a normal integral scheme and the generic point

Let `Z` be an integral scheme with integrally closed local rings, `K` its function field and
`g : Spec K ⟶ Z` the generic point. For a `Λ`-module `M` the unit `M_Z ⟶ g_* g^* M_Z` is an
isomorphism [Stacks 09Z5]. We check it on the étale `Z`-schemes `W` that are integral: there the
constant sections are `M` (connectedness), and `W ×_Z Spec K` is a single point, the generic
point of `W`. Every étale `Z`-scheme is covered by integral ones, because étale algebras over a
normal domain are finite products of domains (Stacks 092W).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The forgetful functor from `Λ`-modules to sets preserves sheaves on the small étale site. -/
instance (X : Scheme.{u}) :
    X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  inferInstance

/-- A morphism of étale sheaves of `Λ`-modules which is bijective on the sections over the
members of a family of étale schemes covering every étale scheme is an isomorphism. -/
theorem Scheme.isIso_of_bijective_app_of_forall_exists {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) (P : X.Etale → Prop)
    (hP : ∀ (V : X.Etale) (x : V.left), ∃ (W : X.Etale) (g : W ⟶ V), P W ∧ x ∈ Set.range g.left)
    (hφ : ∀ W, P W → Function.Bijective (φ.hom.app (op W))) : IsIso φ := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (A := ModuleCat.{u + 1} Λ)]
  refine ⟨⟨fun {V} a b h ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩,
    ⟨fun {V} s ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩⟩
  · obtain ⟨W, g, hW, hx⟩ := hP V.unop x
    refine ⟨W, g, (hφ W hW).1 ?_, hx⟩
    rw [NatTrans.naturality_apply φ.hom g.op a, NatTrans.naturality_apply φ.hom g.op b]
    exact congrArg _ h
  · obtain ⟨W, g, hW, hx⟩ := hP V x
    exact ⟨W, g, (hφ W hW).2 _, hx⟩

/-- An étale morphism from an integral scheme to an integral scheme sends the generic point to
the generic point, and is the only point over it. -/
lemma Scheme.Hom.preimage_genericPoint_eq_of_etale {W Z : Scheme.{u}} [IsIntegral W]
    [IsIntegral Z] (f : W ⟶ Z) [AlgebraicGeometry.Etale f] :
    f ⁻¹' {genericPoint Z} = {genericPoint W} := by
  have hη : f (genericPoint W) = genericPoint Z := by
    obtain ⟨w₀, hw₀⟩ : genericPoint Z ∈ Set.range f.base := by
      have := (genericPoint_spec Z).mem_open_set_iff (U := Set.range f.base)
        f.isOpenMap.isOpen_range
      rw [this, Set.univ_inter]
      exact Set.range_nonempty _
    have h₁ : f (genericPoint W) ⤳ genericPoint Z :=
      hw₀ ▸ ((genericPoint_spec W).specializes (Set.mem_univ w₀)).map f.continuous
    exact (h₁.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq
  ext w
  refine ⟨fun hw ↦ ?_, fun hw ↦ by rw [Set.mem_singleton_iff.1 hw]; exact hη⟩
  have hdisc := f.isDiscrete_preimage_singleton (genericPoint Z)
  have : DiscreteTopology (f ⁻¹' {genericPoint Z}) := hdisc.to_subtype
  have hsp : (⟨genericPoint W, hη⟩ : f ⁻¹' {genericPoint Z}) ⤳ ⟨w, hw⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.1
      ((genericPoint_spec W).specializes (Set.mem_univ w))
  exact congrArg Subtype.val hsp.eq.symm

/-- **The generic fibre of an integral étale scheme is a point.** For an étale morphism
`f : W ⟶ Z` of integral schemes, `W ×_Z Spec 𝒪_{Z,η}` has exactly one point. -/
lemma Scheme.Hom.subsingleton_pullback_fromSpecStalk_genericPoint {W Z : Scheme.{u}}
    [IsIntegral W] [IsIntegral Z] (f : W ⟶ Z) [AlgebraicGeometry.Etale f] :
    Subsingleton ↥(pullback f (Z.fromSpecStalk (genericPoint Z))) ∧
      Nonempty ↥(pullback f (Z.fromSpecStalk (genericPoint Z))) := by
  have hr : Set.range (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).base =
      {genericPoint W} := by
    rw [Scheme.Pullback.range_fst, range_fromSpecStalk, ← f.preimage_genericPoint_eq_of_etale]
    congr 1
    ext y
    exact ⟨fun h ↦ (h.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ y))).eq,
      fun h ↦ by rw [Set.mem_singleton_iff.1 h]; exact specializes_rfl⟩
  have hinj := (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).isEmbedding.injective
  refine ⟨⟨fun a b ↦ hinj ?_⟩, ?_⟩
  · have ha : _ ∈ Set.range (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).base := ⟨a, rfl⟩
    have hb : _ ∈ Set.range (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).base := ⟨b, rfl⟩
    rw [hr] at ha hb
    exact ha.trans hb.symm
  · obtain ⟨a, -⟩ := (Set.ext_iff.1 hr (genericPoint W)).2 rfl
    exact ⟨a⟩

/-- **Étale algebras over a normal domain are locally domains.** Let `B` be an étale algebra over an
integrally closed domain `R` and `q` a prime of `B`. Then some `b ∉ q` has `B[1/b]` a domain:
`B` is integrally closed in `B ⊗_R K` (Stacks 092W), which is a finite product of fields `Aᵢ`, so
the idempotents of the product come from `B`, and `B[1/bᵢ]` embeds into `Aᵢ`. -/
theorem Algebra.Etale.exists_notMem_isDomain_localization {R B : Type u} [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (q : Ideal B) [q.IsPrime] : ∃ b : B, b ∉ q ∧ IsDomain (Localization.Away b) := by
  classical
  have : Nontrivial B := nontrivial_of_ne 0 1 fun h ↦
    ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).2 (h ▸ q.zero_mem))
  let K := FractionRing R
  have : IsIntegrallyClosedIn R K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).1 inferInstance
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have hic := Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct R B K
  obtain ⟨I, _, Ai, _, _, e, -⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K (K ⊗[R] B)).1 inferInstance
  have := Fintype.ofFinite I
  -- the ring map `B ⟶ ∏ Aᵢ`, injective since `B` is flat over `R`
  let ι : B →+* (∀ i, Ai i) := e.toRingHom.comp ((Algebra.TensorProduct.comm R B K).toRingHom.comp
    (algebraMap B (B ⊗[R] K)))
  have hι : Function.Injective ι :=
    e.injective.comp ((Algebra.TensorProduct.comm R B K).injective.comp
    (Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R K)))
  -- the idempotents of `∏ Aᵢ` come from `B`
  have hb (i : I) : ∃ b : B, ι b = Pi.single i 1 := by
    let f : B ⊗[R] K := (Algebra.TensorProduct.comm R B K).symm (e.symm (Pi.single i 1))
    have hid : f * f = f := by
      simp only [f, ← map_mul, ← Pi.single_mul, one_mul]
    have hf : _root_.IsIntegral B f :=
      ⟨Polynomial.X ^ 2 - Polynomial.X,
        Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), by simp [sq, hid]⟩
    obtain ⟨b, hb⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hf
    refine ⟨b, ?_⟩
    change e ((Algebra.TensorProduct.comm R B K) (algebraMap B _ b)) = _
    rw [hb]
    simp [f]
  choose b hb using hb
  have hsum : ∑ i, b i = 1 := hι (by
    rw [map_sum, map_one]
    simp only [hb]
    exact Finset.univ_sum_single (fun _ ↦ 1))
  obtain ⟨i, hi⟩ : ∃ i, b i ∉ q := by
    by_contra! h
    exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).2 (hsum ▸ q.sum_mem fun i _ ↦ h i))
  refine ⟨b i, hi, ?_⟩
  let π : B →+* Ai i := (Pi.evalRingHom Ai i).comp ι
  have hπb : π (b i) = 1 := by simp [π, hb]
  let φ : Localization.Away (b i) →+* Ai i :=
    IsLocalization.Away.lift (b i) (by rw [hπb]; exact isUnit_one)
  refine Function.Injective.isDomain φ ((injective_iff_map_eq_zero φ).2 fun z hz ↦ ?_)
  obtain ⟨⟨x, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (b i)) z
  have hx : π x = 0 := by
    simp only [φ, IsLocalization.Away.lift, IsLocalization.lift_mk'] at hz
    simpa using hz
  have hxb : x * b i = 0 := hι (by
    rw [map_mul, hb, map_zero]
    ext j
    by_cases h : j = i
    · subst h
      simpa [π] using hx
    · simp [h])
  exact (IsLocalization.mk'_eq_zero_iff _ _).2 ⟨⟨b i, Submonoid.mem_powers _⟩, by
    rw [mul_comm]; exact hxb⟩

/-- **Étale schemes over a normal integral scheme are locally integral.** -/
lemma Scheme.exists_isIntegral_of_isIntegrallyClosed {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) (V : Z.Etale) (x : V.left) :
    ∃ U : V.left.Opens, x ∈ U ∧ IsIntegral U.toScheme := by
  have : AlgebraicGeometry.Etale V.hom := V.prop
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show V.hom x ∈ (⊤ : Z.Opens) from trivial)
  obtain ⟨A, hA, hxA, hAU⟩ := exists_isAffineOpen_mem_and_subset (X := V.left)
    (show x ∈ (V.hom ⁻¹ᵁ U : V.left.Opens) from hxU)
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  -- `Γ(Z, U)` is an integrally closed domain
  have : IsIntegrallyClosed Γ(Z, U) := IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦ by
    let y : PrimeSpectrum Γ(Z, U) := ⟨P, inferInstance⟩
    have hy : hU.fromSpec y ∈ U := by
      have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
      rwa [hU.range_fromSpec] at this
    let := TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨_, hy⟩
    have := hU.isLocalization_stalk' y hy
    have := hZ (hU.fromSpec y)
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv P.primeCompl (Z.presheaf.stalk (hU.fromSpec y))
        (Localization.AtPrime P)).toRingEquiv
  -- the étale algebra `Γ(Z, U) ⟶ Γ(V, A)`
  let φ : Γ(Z, U) ⟶ Γ(V.left, A) := V.hom.appLE U A hAU
  let := φ.hom.toAlgebra
  have : Algebra.Etale Γ(Z, U) Γ(V.left, A) := by
    rw [← RingHom.etale_algebraMap]
    exact HasRingHomProperty.appLE @AlgebraicGeometry.Etale V.hom inferInstance ⟨U, hU⟩ ⟨A, hA⟩ _
  obtain ⟨b, hbq, hdom⟩ :=
    Algebra.Etale.exists_notMem_isDomain_localization (R := Γ(Z, U))
      (hA.primeIdealOf ⟨x, hxA⟩).asIdeal
  have hxb : x ∈ V.left.basicOpen b := by
    rw [Scheme.mem_basicOpen _ _ _ hxA]
    by_contra h
    apply hbq
    rw [hA.primeIdealOf_eq_map_closedPoint]
    exact (IsLocalRing.mem_maximalIdeal _).2 h
  refine ⟨V.left.basicOpen b, hxb, ?_⟩
  · have hB := hA.isLocalization_basicOpen b
    have : IsAffine (V.left.basicOpen b).toScheme := hA.basicOpen b
    have : Nonempty (V.left.basicOpen b).toScheme := ⟨⟨x, hxb⟩⟩
    have : IsDomain Γ(V.left, V.left.basicOpen b) := Function.Injective.isDomain
      (IsLocalization.algEquiv (Submonoid.powers b) Γ(V.left, V.left.basicOpen b)
        (Localization.Away b)).toRingEquiv.toRingHom (RingEquiv.injective _)
    have : IsDomain Γ((V.left.basicOpen b).toScheme, ⊤) := Function.Injective.isDomain
      (Scheme.Opens.topIso _).commRingCatIsoToRingEquiv.toRingHom (RingEquiv.injective _)
    exact isIntegral_of_isAffine_of_isDomain _

/-- **Constant sheaves on a normal integral scheme, at the generic point** (the generic-point
half of Stacks 09Z5). Let `Z` be an integral scheme whose local rings are integrally closed and
`g : Spec 𝒪_{Z,η} ⟶ Z` its generic point. Then the unit `M_Z ⟶ g_* g^* M_Z` is an isomorphism.
-/
theorem Etale.isIso_unit_constantSheaf_fromSpecStalk_genericPoint (Z : Scheme.{u})
    [IsIntegral Z] (hZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Z.fromSpecStalk (genericPoint Z))).unit.app
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  let g := Z.fromSpecStalk (genericPoint Z)
  suffices h : IsIso (Etale.constantSheafUnit g M) by
    have : IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)) := h
    exact IsIso.of_isIso_comp_right _ ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M))
  refine Scheme.isIso_of_bijective_app_of_forall_exists _ (fun W ↦ IsIntegral W.left)
    (fun V x ↦ ?_) (fun W hW ↦ ?_)
  · obtain ⟨U, hxU, hU⟩ := Scheme.exists_isIntegral_of_isIntegrallyClosed hZ V x
    exact ⟨Etale.ofOpens V U, Etale.ofOpensι V U, hU, ⟨x, hxU⟩, rfl⟩
  · have : AlgebraicGeometry.Etale W.hom := W.prop
    have : IsIntegral ((𝟭 Scheme).obj W.left) := hW
    have : IsIntegral ((Functor.fromPUnit Z).obj W.right) := ‹IsIntegral Z›
    obtain ⟨hsub, hne⟩ := W.hom.subsingleton_pullback_fromSpecStalk_genericPoint
    let FW := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj W
    have : ConnectedSpace FW.left := by
      have : Subsingleton FW.left := hsub
      exact { isPreconnected_univ :=
                _root_.Set.Subsingleton.isPreconnected Set.subsingleton_of_subsingleton
              toNonempty := hne }
    obtain ⟨p⟩ : Nonempty FW.left := hne
    refine ⟨fun a b h ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨m, rfl⟩ := Scheme.surjective_toSheafify_app_of_connectedSpace Z M W a
      obtain ⟨m', rfl⟩ := Scheme.surjective_toSheafify_app_of_connectedSpace Z M W b
      rw [Etale.constantSheafUnit_app_toSheafify, Etale.constantSheafUnit_app_toSheafify] at h
      let ψ := ((Spec (Z.presheaf.stalk (genericPoint Z))).moduleConstantSheafToPointFunctionSheaf
        M).hom.app (op FW)
      have e₁ := Scheme.moduleConstantSheafToPointFunctionSheaf_app_toSheafify _ M FW m
      have e₂ := Scheme.moduleConstantSheafToPointFunctionSheaf_app_toSheafify _ M FW m'
      have : (fun _ : FW.left ↦ m) = fun _ ↦ m' := e₁.symm.trans ((congrArg ψ h).trans e₂)
      rw [congrFun this p]
    · obtain ⟨m, rfl⟩ := Scheme.surjective_toSheafify_app_of_connectedSpace _ M FW y
      exact ⟨_, Etale.constantSheafUnit_app_toSheafify g M W m⟩

/-- **Maps into pushforwards of constant sheaves from a normal integral scheme** (Step 5 of the
proof of Stacks 09Z6). Let `f : Y ⟶ X` with `Y` integral with integrally closed local rings, and
`g : Spec K ⟶ Y` its generic point. Maps `C ⟶ f_* M_Y` correspond to maps `(g ≫ f)^* C ⟶ M_K`:
by 09Z5 the constant sheaf `M_Y` is `g_* M_K`. -/
noncomputable def Etale.homLowerStarConstantSheafEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (C : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (M : ModuleCat.{u + 1} Λ) :
    (C ⟶ (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≃
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (Y.fromSpecStalk (genericPoint Y) ≫ f)).obj C ⟶
        (constantSheaf (Spec (Y.presheaf.stalk (genericPoint Y))).smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).obj M) :=
  let g := Y.fromSpecStalk (genericPoint Y)
  let MY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have := Etale.isIso_unit_constantSheaf_fromSpecStalk_genericPoint Y hY M
  ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv C MY).symm.trans <|
    (Iso.homCongr (Iso.refl _)
      (asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app MY))).trans <|
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv _ _).symm.trans <|
    Iso.homCongr ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g f).app C).symm
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M)

end AlgebraicGeometry
