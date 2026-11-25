/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.TensorProduct.Free
public import WeilConjectures.AlgebraicGeometry.AffineSpaceEmbedding
public import WeilConjectures.AlgebraicGeometry.PolynomialAffineHyperplane
public import WeilConjectures.AlgebraicGeometry.ZeroLocusSubschemeRegular

/-!
# Smooth uniformizers at codimension one regular points

Let `X` be locally of finite type over a perfect field `k` and `x : X` a point whose local ring
`𝒪_{X,x}` is a discrete valuation ring. Then there are an open neighbourhood `W₀ ∋ x` and a
smooth morphism `W₀ ⟶ 𝔸¹_k` such that the pullback of the coordinate is a uniformizer of
`𝒪_{X,x}` (`AlgebraicGeometry.exists_smooth_polyAffine_irreducible_germ`).

The proof is local algebra at `x`. The ring `B = 𝒪_{X,x}` is formally smooth over `k` (regular
points are smooth over a perfect field) and so is its residue field. For `π ∈ 𝔪 \ 𝔪²` the map
`𝔪/𝔪² → κ ⊗ Ω[B⁄k]` is injective, so `dπ ∉ 𝔪 Ω[B⁄k]` and some linear form on the projective
module `Ω[B⁄k]` sends `dπ` to `1`. This splits `B ⊗ Ω[k[T]⁄k] → Ω[B⁄k]`, and the Jacobi–Zariski
sequence shows that `B` is formally smooth over `k[T]` via `T ↦ π`
(`Algebra.FormallySmooth.mvPolynomial_fin_one_of_notMem_sq`). Hence any section with germ `π`
defines a morphism to `𝔸¹_k` smooth at `x`, and one restricts to its (open) smooth locus.

## Main results

- `Algebra.FormallySmooth.of_comp_of_mapBaseChange_retraction`: for `R → S → T` with `T` formally
  smooth over `R`, a retraction of `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` makes `T` formally smooth over `S`.
- `AlgebraicGeometry.overRestrictToPolyAffine`: the morphism `V ⟶ 𝔸ᴺ_k` given by sections over
  an open `V`, and the criterion `AlgebraicGeometry.mem_smoothLocus_overRestrictToPolyAffine_iff`
  for its smoothness at a point.
- `AlgebraicGeometry.exists_smooth_polyAffine_irreducible_germ`: the smooth uniformizer.
-/

@[expose] public section

open IsLocalRing KaehlerDifferential TensorProduct

/-- Let `M` be a projective module over a local ring `R` and `v ∈ M` with `v ∉ 𝔪 M`. Then some
linear form `ℓ : M → R` takes the value `1` at `v`. -/
theorem Module.Projective.exists_linearMap_apply_eq_one {R M : Type*} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] {v : M}
    (hv : v ∉ maximalIdeal R • (⊤ : Submodule R M)) : ∃ ℓ : M →ₗ[R] R, ℓ v = 1 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹_›
  by_cases h : ∃ i, IsUnit (s v i)
  · obtain ⟨i, hi⟩ := h
    refine ⟨(↑hi.unit⁻¹ : R) • (Finsupp.lapply i ∘ₗ s), ?_⟩
    simp
  · push Not at h
    refine (hv ?_).elim
    have hsv : Finsupp.linearCombination R id (s v) = v := LinearMap.congr_fun hs v
    rw [← hsv, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem_smul ((mem_maximalIdeal _).mpr (h i)) trivial

/-- Let `R → S → T` be ring maps with `T` formally smooth over `R`. If the map
`T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` has a retraction, then `T` is formally smooth over `S`: the
Jacobi–Zariski sequence `H¹(L_{T/R}) → H¹(L_{T/S}) → T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0`
shows that `H¹(L_{T/S}) = 0` and that `Ω[T⁄S]` is a direct summand of `Ω[T⁄R]`. -/
theorem Algebra.FormallySmooth.of_comp_of_mapBaseChange_retraction {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T] (l : Ω[T⁄R] →ₗ[T] T ⊗[S] Ω[S⁄R])
    (hl : l ∘ₗ mapBaseChange R S T = LinearMap.id) : Algebra.FormallySmooth S T := by
  obtain ⟨-, s, hs⟩ := ((exact_mapBaseChange_map R S T).split_tfae'.out 2 1 rfl rfl).mp
    ⟨map_surjective R S T, l, hl⟩
  refine ⟨Module.Projective.of_split s (map R S T T) hs, subsingleton_of_forall_eq 0 fun z ↦ ?_⟩
  have hδ : H1Cotangent.δ R S T z = 0 := by
    rw [← LinearMap.id_apply (R := T) (H1Cotangent.δ R S T z), ← hl, LinearMap.comp_apply,
      (H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero, map_zero]
  obtain ⟨w, rfl⟩ := (H1Cotangent.exact_map_δ R S T z).mp hδ
  rw [Subsingleton.elim w 0, map_zero]

/-- Let `B` be a local `k`-algebra, formally smooth over `k`, whose residue field is formally
smooth over `k`. If `π ∈ 𝔪 \ 𝔪²`, then `dπ ∉ 𝔪 Ω[B⁄k]`: the map `𝔪/𝔪² → κ ⊗ Ω[B⁄k]` is
injective. -/
theorem KaehlerDifferential.D_notMem_maximalIdeal_smul_top {k B : Type*} [CommRing k]
    [CommRing B] [IsLocalRing B] [Algebra k B] [Algebra.FormallySmooth k B]
    [Algebra.FormallySmooth k (ResidueField B)] {π : B} (hπ : π ∈ maximalIdeal B)
    (hπ2 : π ∉ maximalIdeal B ^ 2) :
    D k B π ∉ maximalIdeal B • (⊤ : Submodule B Ω[B⁄k]) := by
  have hinj : Function.Injective (kerCotangentToTensor k B (ResidueField B)) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff residue_surjective).2
      inferInstance
  have hker : RingHom.ker (algebraMap B (ResidueField B)) = maximalIdeal B := ker_residue
  have hπ' : π ∈ RingHom.ker (algebraMap B (ResidueField B)) := hker ▸ hπ
  intro hD
  have h0 : kerCotangentToTensor k B (ResidueField B)
      ((RingHom.ker (algebraMap B (ResidueField B))).toCotangent ⟨π, hπ'⟩) = 0 := by
    rw [kerCotangentToTensor_toCotangent]
    refine Submodule.smul_induction_on (p := fun w ↦ (1 : ResidueField B) ⊗ₜ[B] w = 0) hD
      (fun r hr w _ ↦ ?_) (fun a b ha hb ↦ ?_)
    · have hr' : algebraMap B (ResidueField B) r = 0 := RingHom.mem_ker.mp (by rwa [hker])
      rw [← smul_tmul, Algebra.smul_def, mul_one, hr', zero_tmul]
    · rw [tmul_add, ha, hb, add_zero]
  have h1 : π ∈ RingHom.ker (algebraMap B (ResidueField B)) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker] at h1
  exact hπ2 h1

/-- Let `B` be a local `k`-algebra, formally smooth over `k`, whose residue field is formally
smooth over `k`, and let `k[X₀] → B` be a `k`-algebra map with `X₀ ↦ π ∈ 𝔪 \ 𝔪²`. Then `B` is
formally smooth over `k[X₀]`. -/
theorem Algebra.FormallySmooth.mvPolynomial_fin_one_of_notMem_sq {k B : Type*} [CommRing k]
    [CommRing B] [IsLocalRing B] [Algebra k B] [Algebra (MvPolynomial (Fin 1) k) B]
    [IsScalarTower k (MvPolynomial (Fin 1) k) B] [Algebra.FormallySmooth k B]
    [Algebra.FormallySmooth k (ResidueField B)]
    (hπ : algebraMap (MvPolynomial (Fin 1) k) B (.X 0) ∈ maximalIdeal B)
    (hπ2 : algebraMap (MvPolynomial (Fin 1) k) B (.X 0) ∉ maximalIdeal B ^ 2) :
    Algebra.FormallySmooth (MvPolynomial (Fin 1) k) B := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_linearMap_apply_eq_one
    (KaehlerDifferential.D_notMem_maximalIdeal_smul_top (k := k) hπ hπ2)
  refine of_comp_of_mapBaseChange_retraction (R := k) (LinearMap.toSpanSingleton B _
    ((1 : B) ⊗ₜ[MvPolynomial (Fin 1) k] D k (MvPolynomial (Fin 1) k) (.X 0)) ∘ₗ ℓ) ?_
  refine (Algebra.TensorProduct.basis B (mvPolynomialBasis k (Fin 1))).ext fun i ↦ ?_
  obtain rfl := Subsingleton.elim i 0
  have hb : mvPolynomialBasis k (Fin 1) 0 = D k (MvPolynomial (Fin 1) k) (.X 0) :=
    Module.Basis.apply_eq_iff.mpr (mvPolynomialBasis_repr_D_X k (Fin 1) 0)
  rw [Algebra.TensorProduct.basis_apply, hb, LinearMap.comp_apply, mapBaseChange_tmul, one_smul,
    map_D, LinearMap.comp_apply, hℓ]
  simp

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a morphism `g : Y ⟶ Spec R`, the ring map `R → 𝒪_{Y,y}` induced by `g` factors as the
localization `R → 𝒪_{Spec R, g y}` followed by the stalk map of `g` at `y`. -/
theorem Scheme.Hom.ΓSpecIso_inv_appTop_germ {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (g : Y ⟶ Spec R) (y : Y) :
    (Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial =
      StructureSheaf.toStalk R (g y) ≫ g.stalkMap y := by
  have h : StructureSheaf.toStalk R (g y) =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (g y) trivial := rfl
  rw [h, Category.assoc, Scheme.Hom.germ_stalkMap]
  rfl

/-- A morphism `g : Y ⟶ Spec R`, locally of finite presentation, is smooth at `y` if and only if
the induced ring map `R → 𝒪_{Y,y}` is formally smooth. -/
theorem Scheme.Hom.mem_smoothLocus_iff_formallySmooth {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (g : Y ⟶ Spec R) [LocallyOfFinitePresentation g] (y : Y) :
    y ∈ g.smoothLocus ↔
      ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.FormallySmooth := by
  rw [g.ΓSpecIso_inv_appTop_germ, Scheme.Hom.mem_smoothLocus]
  let := (g.stalkMap y).hom.toAlgebra
  let : Algebra R ((Spec R).presheaf.stalk (g y)) := StructureSheaf.stalkAlgebra R (g y)
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk (g y)) (g y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R (g y)
  let : Algebra R (Y.presheaf.stalk y) :=
    (StructureSheaf.toStalk R (g y) ≫ g.stalkMap y).hom.toAlgebra
  have : IsScalarTower R ((Spec R).presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
    .of_algebraMap_eq' rfl
  have : Algebra.FormallyEtale R ((Spec R).presheaf.stalk (g y)) :=
    .of_isLocalization (g y).asIdeal.primeCompl
  exact Algebra.FormallySmooth.iff_restrictScalars.symm

/-- A morphism `g : Y ⟶ Spec R` locally of finite type: the induced ring map `R → 𝒪_{Y,y}` is
essentially of finite type. -/
theorem Scheme.Hom.essFiniteType_ΓSpecIso_inv_appTop_germ {Y : Scheme.{u}}
    {R : CommRingCat.{u}} (g : Y ⟶ Spec R) [LocallyOfFiniteType g] (y : Y) :
    ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.EssFiniteType := by
  rw [g.ΓSpecIso_inv_appTop_germ, CommRingCat.hom_comp]
  exact .comp (Algebra.EssFiniteType.of_isLocalization _ (g y).asIdeal.primeCompl)
    (LocallyOfFiniteType.stalkMap g y)

/-- A morphism `f : Y ⟶ Spec R` is the composite of `Y ⟶ Spec Γ(Y, ⊤)` and the spectrum of the
ring map `R → Γ(Y, ⊤)` induced by `f`. -/
theorem Scheme.toSpecΓ_SpecMap_ΓSpecIso_inv_appTop {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (f : Y ⟶ Spec R) : Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The global ring map of `Y ⟶ Spec Γ(Y, ⊤) ⟶ Spec A` is the given ring map `A → Γ(Y, ⊤)`. -/
theorem Scheme.ΓSpecIso_inv_appTop_toSpecΓ_SpecMap {Y : Scheme.{u}} {A : Type u} [CommRing A]
    (ψ : A →+* Γ(Y, ⊤)) :
    (Scheme.ΓSpecIso (.of A)).inv ≫ (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop =
      CommRingCat.ofHom ψ := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Scheme.toSpecΓ_appTop]
  erw [Iso.inv_hom_id]
  exact Category.comp_id _

variable {k : Type u} [Field k]

/-- For an open `V` of a scheme `X` over a field `k` and sections `s₀, …, s_{N-1}` of `𝒪_X` over
`V`, the morphism `V ⟶ 𝔸ᴺ_k` over `k` given by `Xᵢ ↦ sᵢ`. -/
noncomputable def overRestrictToPolyAffine (X : Over (Spec (.of k))) (V : X.left.Opens) {N : ℕ}
    (s : Fin N → Γ(X.left, V)) : overRestrict X V ⟶ polyAffine k N :=
  Over.homMk (V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (V.ι ≫ X.hom).appTop).hom fun i ↦ V.topIso.inv (s i)))) (by
    simp only [polyAffine, Over.mk_hom]
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval₂Hom_comp_C]
    exact Scheme.toSpecΓ_SpecMap_ΓSpecIso_inv_appTop (V.ι ≫ X.hom))

/-- The underlying morphism of `overRestrictToPolyAffine X V s` is `V ⟶ Spec Γ(V, ⊤) ⟶ 𝔸ᴺ_k`. -/
lemma overRestrictToPolyAffine_left (X : Over (Spec (.of k))) (V : X.left.Opens) {N : ℕ}
    (s : Fin N → Γ(X.left, V)) :
    (overRestrictToPolyAffine X V s).left = V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ (V.ι ≫ X.hom).appTop).hom
        fun i ↦ V.topIso.inv (s i))) :=
  rfl

/-- The ring map `k[X₀, …, X_{N-1}] → 𝒪_{X,x}` induced by `overRestrictToPolyAffine X V s` at a
point `x ∈ V` is `Xᵢ ↦ (sᵢ)ₓ`. -/
theorem overRestrictToPolyAffine_germ (X : Over (Spec (.of k))) (V : X.left.Opens) {N : ℕ}
    (s : Fin N → Γ(X.left, V)) (x : X.left) (hx : x ∈ V) :
    (Scheme.ΓSpecIso _).inv ≫ (overRestrictToPolyAffine X V s).left.appTop ≫
        X.left.presheaf.germ (V.ι ''ᵁ ⊤) x ⟨⟨x, hx⟩, trivial, rfl⟩ =
      CommRingCat.ofHom (MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
        X.left.presheaf.germ ⊤ x trivial).hom fun i ↦ X.left.presheaf.germ V x hx (s i)) := by
  rw [overRestrictToPolyAffine_left, ← Category.assoc,
    Scheme.ΓSpecIso_inv_appTop_toSpecΓ_SpecMap]
  ext : 1
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp only [Over.mk_left, Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top,
      Scheme.Opens.ι_app, homOfLE_leOfHom, CommRingCat.hom_comp, ConcreteCategory.hom_ofHom,
      MvPolynomial.comp_eval₂Hom, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
    exact TopCat.Presheaf.germ_res_apply' X.left.presheaf _ x _ _
  · simp only [CommRingCat.hom_comp, Scheme.Opens.topIso_inv, ConcreteCategory.hom_ofHom,
      MvPolynomial.comp_eval₂Hom, MvPolynomial.eval₂Hom_X']
    exact TopCat.Presheaf.germ_res_apply' X.left.presheaf _ x _ (s i)

/-- The pullback of the coordinate `Xᵢ` along `overRestrictToPolyAffine X V s` has germ `(sᵢ)ₓ`
at every `x ∈ V`. -/
theorem germ_appTop_overRestrictToPolyAffine (X : Over (Spec (.of k))) (V : X.left.Opens)
    {N : ℕ} (s : Fin N → Γ(X.left, V)) (x : X.left) (hx : x ∈ V) (i : Fin N) :
    X.left.presheaf.germ (V.ι ''ᵁ ⊤) x ⟨⟨x, hx⟩, trivial, rfl⟩
        ((overRestrictToPolyAffine X V s).left.appTop (polyAffineCoord k i)) =
      X.left.presheaf.germ V x hx (s i) := by
  rw [polyAffineCoord]
  refine (ConcreteCategory.congr_hom (overRestrictToPolyAffine_germ X V s x hx)
    (MvPolynomial.X i)).trans ?_
  simp

/-- The morphism `overRestrictToPolyAffine X V s` is locally of finite presentation when `X` is
locally of finite type over `k`. -/
instance (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] (V : X.left.Opens) {N : ℕ}
    (s : Fin N → Γ(X.left, V)) :
    LocallyOfFinitePresentation (overRestrictToPolyAffine X V s).left := by
  have : LocallyOfFiniteType ((overRestrictToPolyAffine X V s).left ≫ (polyAffine k N).hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (overRestrictToPolyAffine X V s).left :=
    locallyOfFiniteType_of_comp _ (polyAffine k N).hom
  have : IsLocallyNoetherian (polyAffine k N).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of (MvPolynomial (Fin N) k))))
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›

/-- The morphism `overRestrictToPolyAffine X V s : V ⟶ 𝔸ᴺ_k` is smooth at `x ∈ V` if and only if
the ring map `k[X₀, …, X_{N-1}] → 𝒪_{X,x}`, `Xᵢ ↦ (sᵢ)ₓ`, is formally smooth. -/
theorem mem_smoothLocus_overRestrictToPolyAffine_iff (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] (V : X.left.Opens) {N : ℕ} (s : Fin N → Γ(X.left, V))
    (x : X.left) (hx : x ∈ V) :
    (⟨x, hx⟩ : V.toScheme) ∈ (overRestrictToPolyAffine X V s).left.smoothLocus ↔
      (MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
        X.left.presheaf.germ ⊤ x trivial).hom
          fun i ↦ X.left.presheaf.germ V x hx (s i)).FormallySmooth := by
  refine (Scheme.Hom.mem_smoothLocus_iff_formallySmooth (R := .of (MvPolynomial (Fin N) k))
    _ _).trans ?_
  rw [← RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (V.stalkIso ⟨x, hx⟩).hom,
    ← CommRingCat.hom_comp]
  have h : ((Scheme.ΓSpecIso _).inv ≫ (overRestrictToPolyAffine X V s).left.appTop ≫
      V.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ trivial) ≫ (V.stalkIso ⟨x, hx⟩).hom =
        CommRingCat.ofHom (MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
          X.left.presheaf.germ ⊤ x trivial).hom fun i ↦ X.left.presheaf.germ V x hx (s i)) := by
    rw [Category.assoc, Category.assoc, Scheme.Opens.germ_stalkIso_hom]
    exact overRestrictToPolyAffine_germ X V s x hx
  exact iff_of_eq (congrArg (fun φ ↦ (CommRingCat.Hom.hom φ).FormallySmooth) h)

/-- Let `X` be locally of finite type over a perfect field `k` and `x : X` a point whose local ring
is a discrete valuation ring with uniformizer `ϖ`. Then the ring map `k[X₀] → 𝒪_{X,x}`,
`X₀ ↦ ϖ`, is formally smooth. -/
theorem formallySmooth_eval₂Hom_stalk_of_irreducible [PerfectField k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] (x : X.left) [IsDomain (X.left.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.left.presheaf.stalk x)]
    {ϖ : X.left.presheaf.stalk x} (hϖ : Irreducible ϖ) :
    (MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.germ ⊤ x trivial).hom fun _ : Fin 1 ↦ ϖ).FormallySmooth := by
  set φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫ X.left.presheaf.germ ⊤ x trivial).hom
  have : LocallyOfFinitePresentation X.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have hsm : φ.FormallySmooth := (X.hom.mem_smoothLocus_iff_formallySmooth x).mp
    X.hom.mem_smoothLocus_of_isRegularLocalRing_of_perfectField
  have hft : φ.EssFiniteType := X.hom.essFiniteType_ΓSpecIso_inv_appTop_germ x
  algebraize [φ, MvPolynomial.eval₂Hom φ fun _ : Fin 1 ↦ ϖ]
  have : IsScalarTower k (MvPolynomial (Fin 1) k) (X.left.presheaf.stalk x) :=
    .of_algebraMap_eq' (MvPolynomial.eval₂Hom_comp_C φ _).symm
  have : Algebra.FormallySmooth k (X.left.presheaf.stalk x) := hsm
  have : Algebra.EssFiniteType k (X.left.presheaf.stalk x) := hft
  have : Algebra.EssFiniteType k (ResidueField (X.left.presheaf.stalk x)) :=
    inferInstanceAs (Algebra.EssFiniteType k
      (X.left.presheaf.stalk x ⧸ maximalIdeal (X.left.presheaf.stalk x)))
  have hX : algebraMap (MvPolynomial (Fin 1) k) (X.left.presheaf.stalk x) (.X 0) = ϖ :=
    MvPolynomial.eval₂Hom_X' φ _ 0
  have hm2 : ϖ ∉ maximalIdeal (X.left.presheaf.stalk x) ^ 2 := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h : ϖ * (ϖ * c) = ϖ * 1 := by rw [mul_one, ← mul_assoc, ← sq, ← hc]
    exact hϖ.not_isUnit (.of_mul_eq_one _ (mul_left_cancel₀ hϖ.ne_zero h))
  exact Algebra.FormallySmooth.mvPolynomial_fin_one_of_notMem_sq (k := k)
    (by rw [hX]; exact hϖ.not_isUnit) (by rw [hX]; exact hm2)

/-- **Smooth uniformizers.** Let `X` be locally of finite type over a perfect field `k` and
`x : X` a point whose local ring is a discrete valuation ring. Then there are an open
neighbourhood `W₀` of `x` and a smooth morphism `f₀ : W₀ ⟶ 𝔸¹_k` over `k` such that the pullback
of the coordinate is a uniformizer of `𝒪_{X,x}`.

Any `s` with irreducible germ `sₓ` works: `k[X₀] → 𝒪_{X,x}`, `X₀ ↦ sₓ`, is formally smooth
(`formallySmooth_eval₂Hom_stalk_of_irreducible`), so `s : V ⟶ 𝔸¹_k` is smooth at `x`, and one
restricts to its smooth locus. -/
theorem exists_smooth_polyAffine_irreducible_germ [PerfectField k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] (x : X.left) [IsDomain (X.left.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.left.presheaf.stalk x)] :
    ∃ (W₀ : X.left.Opens) (hx : x ∈ W₀) (f₀ : overRestrict X W₀ ⟶ polyAffine k 1),
      Smooth f₀.left ∧
      Irreducible (X.left.presheaf.germ (W₀.ι ''ᵁ ⊤) x ⟨⟨x, hx⟩, trivial, rfl⟩
        (f₀.left.appTop (polyAffineCoord k (Fin.last 0)))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.left.presheaf.stalk x)
  obtain ⟨V, hxV, s, rfl⟩ : ∃ (V : X.left.Opens) (hxV : x ∈ V) (s : Γ(X.left, V)),
      X.left.presheaf.germ V x hxV s = ϖ := X.left.presheaf.exists_germ_eq ϖ
  have hgx : (⟨x, hxV⟩ : V.toScheme) ∈
      (overRestrictToPolyAffine X V fun _ : Fin 1 ↦ s).left.smoothLocus :=
    (mem_smoothLocus_overRestrictToPolyAffine_iff X V _ x hxV).mpr
      (formallySmooth_eval₂Hom_stalk_of_irreducible X x hϖ)
  set W₀ := V.ι ''ᵁ (overRestrictToPolyAffine X V fun _ : Fin 1 ↦ s).left.smoothLocus
  have hW₀V : W₀ ≤ V := V.ι_image_le _
  have hxW₀ : x ∈ W₀ := ⟨_, hgx, rfl⟩
  refine ⟨W₀, hxW₀,
    overRestrictToPolyAffine X W₀ fun _ ↦ X.left.presheaf.map (homOfLE hW₀V).op s, ?_, ?_⟩
  · rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
    rintro ⟨w, hw⟩ -
    have hw' := (mem_smoothLocus_overRestrictToPolyAffine_iff X V _ w (hW₀V hw)).mp
      ((V.mem_ι_image_iff (x := ⟨w, hW₀V hw⟩)).mp hw)
    rw [mem_smoothLocus_overRestrictToPolyAffine_iff]
    simpa only [TopCat.Presheaf.germ_res_apply] using hw'
  · rw [germ_appTop_overRestrictToPolyAffine X W₀ _ x hxW₀, TopCat.Presheaf.germ_res_apply]
    exact hϖ

end AlgebraicGeometry
