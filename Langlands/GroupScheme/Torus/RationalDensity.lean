import Langlands.GroupScheme.Torus.GaloisDensityAlgebra
import Langlands.GroupScheme.Torus.SplitPointTopology
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Density of rational points of tori split by a finite Galois extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.TorusDensity

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The base change morphism `Spec K ⟶ Spec k`. -/
abbrev specBase : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

variable {k K}

/-- The scheme automorphism `Spec σ` of `Spec K`. -/
abbrev specGal (σ : K ≃ₐ[k] K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (σ : K →+* K))

theorem specGal_comp_specBase (σ : K ≃ₐ[k] K) : specGal σ ≫ specBase k K = specBase k K := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

theorem specGal_comp_specGal (σ τ : K ≃ₐ[k] K) : specGal τ ≫ specGal σ = specGal (τ * σ) := by
  rw [← Spec.map_comp]
  rfl

theorem specGal_one : specGal (1 : K ≃ₐ[k] K) = 𝟙 _ := by
  rw [Spec.map_eq_id]
  rfl

/-! ### Galois descent of points -/

/-- A `K`-point of a `k`-scheme fixed by all of `Gal(K/k)` comes from a rational point. -/
theorem exists_rationalPoint_of_fixed [FiniteDimensional k K] [IsGalois k K]
    (X : Over (Spec (CommRingCat.of k))) (z : Spec (CommRingCat.of K) ⟶ X.left)
    (hz : z ≫ X.hom = specBase k K) (hfix : ∀ σ : K ≃ₐ[k] K, specGal σ ≫ z = z) :
    ∃ p : RationalPoint k X, specBase k K ≫ p.left = z := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨R, f, hf, y0, hy0⟩ := Scheme.exists_Spec_apply_eq (z pt)
  have hsub : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hrange : Set.range z ⊆ Set.range f := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q pt]
    exact ⟨y0, hy0⟩
  set l := IsOpenImmersion.lift f z hrange with hl_def
  have hl : l ≫ f = z := IsOpenImmersion.lift_fac _ _ _
  set ψ := Spec.preimage l with hψ_def
  have hψl : Spec.map ψ = l := Spec.map_preimage l
  have hfixψ : ∀ a, ψ.hom a ∈ Set.range (algebraMap k K) := by
    intro a
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    have h1 : specGal σ ≫ l = l := by
      rw [← cancel_mono f, Category.assoc, hl, hfix]
    have h2 : ψ ≫ CommRingCat.ofHom (σ : K →+* K) = ψ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hψl]
      exact h1
    exact congrArg (fun g => g.hom a) h2
  have hleft : Function.LeftInverse (Function.invFun (algebraMap k K)) (algebraMap k K) :=
    Function.leftInverse_invFun (algebraMap k K).injective
  let ψ₀ : R →+* k := (RingEquiv.ofLeftInverse hleft).symm.toRingHom.comp
    (ψ.hom.codRestrict (algebraMap k K).range fun a => hfixψ a)
  have hψ₀ : CommRingCat.ofHom ψ₀ ≫ CommRingCat.ofHom (algebraMap k K) = ψ := by
    ext a
    change algebraMap k K ((RingEquiv.ofLeftInverse hleft).symm
      (ψ.hom.codRestrict (algebraMap k K).range (fun a => hfixψ a) a)) = ψ.hom a
    rw [← RingEquiv.ofLeftInverse_apply hleft, RingEquiv.apply_symm_apply]
    rfl
  let p₀ : Spec (CommRingCat.of k) ⟶ X.left := Spec.map (CommRingCat.ofHom ψ₀) ≫ f
  have hp₀ : specBase k K ≫ p₀ = z := by
    rw [← Category.assoc, ← Spec.map_comp, hψ₀, hψl, hl]
  have hover : p₀ ≫ X.hom = 𝟙 _ := by
    set g := p₀ ≫ X.hom
    have hg : specBase k K ≫ g = specBase k K := by
      rw [← Category.assoc, hp₀, hz]
    rw [← Spec.map_preimage g] at hg ⊢
    rw [← Spec.map_comp] at hg
    have hg' := Spec.map_injective hg
    rw [Spec.map_eq_id]
    ext x
    apply (algebraMap k K).injective
    exact congrArg (fun φ => φ.hom x) hg'
  exact ⟨Over.homMk p₀ (by simpa using hover), hp₀⟩

/-! ### The test scheme `Spec K` and Laurent points -/

variable (K) in
/-- `K` as an algebra over itself. -/
abbrev testAlg : CommAlgCat (CommRingCat.of K) := CommAlgCat.of (CommRingCat.of K) K

variable (K) in
/-- `Spec K` as a scheme over itself. -/
abbrev testObj : Over (Spec (CommRingCat.of K)) :=
  (algSpec (CommRingCat.of K)).obj (op (testAlg K))

theorem testObj_hom : (testObj K).hom = 𝟙 (Spec (CommRingCat.of K)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K))
  rw [Spec.map_eq_id]
  rfl

/-- A `K`-point of the Laurent model is the spectrum of the evaluation at its coordinates. -/
theorem laurent_point_left (I : Type u) [Fintype I]
    (y : testObj K ⟶ (splitTorus.laurentGroupScheme I (CommRingCat.of K)).X) :
    y.left = Spec.map (CommRingCat.ofHom (lev K
      (splitTorus.laurentAffinePointsEquiv I (CommRingCat.of K) (testAlg K) y) :
        AddMonoidAlgebra K (I →₀ ℤ) →+* K)) := by
  set t := splitTorus.laurentAffinePointsEquiv I (CommRingCat.of K) (testAlg K) y with ht
  have hy : y = (splitTorus.laurentAffinePointsEquiv I (CommRingCat.of K) (testAlg K)).symm t :=
    (MulEquiv.symm_apply_apply _ _).symm
  have hlev : ((splitTorus.algHomEquiv I (CommRingCat.of K) K).symm t :
      AddMonoidAlgebra K (I →₀ ℤ) →ₐ[K] K) = lev K t := by
    apply algHom_ext_coord K
    intro i
    rw [lev_coord, coe_coord]
    exact (splitTorus.algHomEquiv_apply_val I (CommRingCat.of K) K _ i).symm.trans
      (congrArg (fun s => (s i : K)) ((splitTorus.algHomEquiv I (CommRingCat.of K) K).apply_symm_apply t))
  have hy' : y.left = Spec.map (CommRingCat.ofHom
      ((splitTorus.algHomEquiv I (CommRingCat.of K) K).symm t :
        AddMonoidAlgebra K (I →₀ ℤ) →+* K)) := by
    conv_lhs => rw [hy, splitTorus.laurentAffinePointsEquiv_symm_apply]
    rfl
  rw [hy', hlev]

/-! ### The Galois action on `K`-points -/

variable (k K) in
/-- `Spec K` as a scheme over `Spec k`. -/
abbrev testObjBase : Over (Spec (CommRingCat.of k)) :=
  (Over.map (specBase k K)).obj (testObj K)

theorem testObjBase_hom : (testObjBase k K).hom = specBase k K := by
  change (testObj K).hom ≫ specBase k K = specBase k K
  rw [testObj_hom]
  exact Category.id_comp _

/-- The Galois automorphism `Spec σ` of `Spec K` over `Spec k`. -/
def galHom (σ : K ≃ₐ[k] K) : testObjBase k K ⟶ testObjBase k K :=
  Over.homMk (specGal σ) (by rw [testObjBase_hom]; exact specGal_comp_specBase σ)

@[simp] theorem galHom_left (σ : K ≃ₐ[k] K) : (galHom σ).left = specGal σ := rfl

theorem galHom_comp (σ τ : K ≃ₐ[k] K) : galHom τ ≫ galHom σ = galHom (τ * σ) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, galHom_left, galHom_left, galHom_left, specGal_comp_specGal]

variable (T : GroupScheme (Spec (CommRingCat.of k)))

/-- Precomposition with a Galois automorphism, on `K`-points of `T`. -/
def galAct (σ : K ≃ₐ[k] K) : (testObjBase k K ⟶ T.X) →* (testObjBase k K ⟶ T.X) where
  toFun y := galHom σ ≫ y
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem galAct_apply (σ : K ≃ₐ[k] K) (y : testObjBase k K ⟶ T.X) :
    galAct T σ y = galHom σ ≫ y := rfl

theorem galAct_galAct (σ τ : K ≃ₐ[k] K) (y : testObjBase k K ⟶ T.X) :
    galAct T τ (galAct T σ y) = galAct T (τ * σ) y := by
  rw [galAct_apply, galAct_apply, galAct_apply, ← Category.assoc, galHom_comp]

/-- The semilinear automorphism `id ×_k Spec σ⁻¹` of the base change `T_K`. -/
def twistMap (σ : K ≃ₐ[k] K) :
    pullback T.X.hom (specBase k K) ⟶ pullback T.X.hom (specBase k K) :=
  pullback.map T.X.hom (specBase k K) T.X.hom (specBase k K) (𝟙 _) (specGal σ⁻¹) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, specGal_comp_specBase])

theorem twistMap_one : twistMap T (1 : K ≃ₐ[k] K) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [twistMap, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [twistMap, pullback.lift_snd, inv_one, specGal_one, Category.comp_id, Category.id_comp]

/-- The adjunction between `K`-points of `T_K` and `K`-points of `T`. -/
abbrev baseChangePoints :
    (testObj K ⟶ ((GroupScheme.baseChange (specBase k K)).obj T).X) ≃*
      (testObjBase k K ⟶ T.X) :=
  GroupScheme.baseChangePointsEquiv (specBase k K) T (testObj K)

theorem baseChangePoints_symm_left_fst (y : testObjBase k K ⟶ T.X) :
    ((baseChangePoints T).symm y).left ≫ pullback.fst T.X.hom (specBase k K) = y.left := by
  have h := GroupScheme.baseChangePointsEquiv_left (specBase k K) T (testObj K)
    ((baseChangePoints T).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem baseChangePoints_symm_left_snd (y : testObjBase k K ⟶ T.X) :
    ((baseChangePoints T).symm y).left ≫ pullback.snd T.X.hom (specBase k K) = 𝟙 _ := by
  have h := Over.w ((baseChangePoints T).symm y)
  rw [testObj_hom] at h
  exact h

/-- The Galois action on `K`-points of `T`, seen on `K`-points of `T_K`. -/
theorem baseChangePoints_symm_galAct_left (σ : K ≃ₐ[k] K) (y : testObjBase k K ⟶ T.X) :
    ((baseChangePoints T).symm (galAct T σ y)).left =
      specGal σ ≫ ((baseChangePoints T).symm y).left ≫ twistMap T σ := by
  apply pullback.hom_ext
  · rw [baseChangePoints_symm_left_fst, Category.assoc, Category.assoc, twistMap,
      pullback.lift_fst, Category.comp_id, baseChangePoints_symm_left_fst]
    rfl
  · rw [baseChangePoints_symm_left_snd, Category.assoc, Category.assoc, twistMap,
      pullback.lift_snd, ← Category.assoc _ (pullback.snd _ _), baseChangePoints_symm_left_snd]
    change 𝟙 (Spec (CommRingCat.of K)) = specGal σ ≫ 𝟙 (Spec (CommRingCat.of K)) ≫ specGal σ⁻¹
    rw [Category.id_comp, specGal_comp_specGal, mul_inv_cancel, specGal_one]

/-! ### Laurent coordinates on `K`-points -/

variable {T} {I : Type u} [Fintype I]
  (Λ : (GroupScheme.baseChange (specBase k K)).obj T ≅
    splitTorus.laurentGroupScheme I (CommRingCat.of K))

/-- `K`-points of `T` in the Laurent coordinates given by `Λ`. -/
def coordEquiv : (testObjBase k K ⟶ T.X) ≃* (I → Kˣ) :=
  (baseChangePoints T).symm.trans ((isoPointsEquiv Λ (testObj K)).trans
    (splitTorus.laurentAffinePointsEquiv I (CommRingCat.of K) (testAlg K)))

/-- The scheme isomorphism underlying `Λ`. -/
abbrev chart : pullback T.X.hom (specBase k K) ≅
    Spec (CommRingCat.of (AddMonoidAlgebra K (I →₀ ℤ))) :=
  (Over.forget _).mapIso ((Grp.forget _).mapIso Λ)

theorem coordEquiv_left (y : testObjBase k K ⟶ T.X) :
    ((baseChangePoints T).symm y).left ≫ (chart Λ).hom =
      Spec.map (CommRingCat.ofHom
        (lev K (coordEquiv Λ y) : AddMonoidAlgebra K (I →₀ ℤ) →+* K)) :=
  laurent_point_left I ((baseChangePoints T).symm y ≫ Λ.hom.hom.hom)

/-- The twist `id ×_k Spec σ⁻¹` in the Laurent chart. -/
def galScheme (σ : K ≃ₐ[k] K) :
    Spec (CommRingCat.of (AddMonoidAlgebra K (I →₀ ℤ))) ⟶
      Spec (CommRingCat.of (AddMonoidAlgebra K (I →₀ ℤ))) :=
  (chart Λ).inv ≫ twistMap T σ ≫ (chart Λ).hom

/-- The ring endomorphism of the Laurent algebra underlying `galScheme Λ σ`. -/
def galRingHom (σ : K ≃ₐ[k] K) :
    CommRingCat.of (AddMonoidAlgebra K (I →₀ ℤ)) ⟶
      CommRingCat.of (AddMonoidAlgebra K (I →₀ ℤ)) :=
  Spec.preimage (galScheme Λ σ)

/-- The images of the coordinate units under `galRingHom Λ σ`. -/
def galUnit (σ : K ≃ₐ[k] K) (i : I) : (AddMonoidAlgebra K (I →₀ ℤ))ˣ :=
  Units.map (galRingHom Λ σ).hom.toMonoidHom (coord K i)

omit [Fintype I] in
theorem galUnit_one (i : I) : galUnit Λ (1 : K ≃ₐ[k] K) i = coord K i := by
  have h : galRingHom Λ (1 : K ≃ₐ[k] K) = 𝟙 _ := by
    rw [galRingHom, galScheme, twistMap_one, Category.id_comp, Iso.inv_hom_id, Spec.preimage_id]
  apply Units.ext
  rw [galUnit, h]
  rfl

/-- The Galois action on `K`-points in Laurent coordinates. -/
theorem coordEquiv_galAct (σ : K ≃ₐ[k] K) (y : testObjBase k K ⟶ T.X) (i : I) :
    coordEquiv Λ (galAct T σ y) i =
      gal σ (Units.map (lev K (coordEquiv Λ y) : AddMonoidAlgebra K (I →₀ ℤ) →* K)
        (galUnit Λ σ i)) := by
  set x := (baseChangePoints T).symm y
  have h1 := coordEquiv_left Λ (galAct T σ y)
  rw [baseChangePoints_symm_galAct_left] at h1
  have h2 : (specGal σ ≫ x.left ≫ twistMap T σ) ≫ (chart Λ).hom =
      specGal σ ≫ (x.left ≫ (chart Λ).hom) ≫ Spec.map (galRingHom Λ σ) := by
    rw [galRingHom, Spec.map_preimage, galScheme]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [h2, coordEquiv_left, ← Spec.map_comp, ← Spec.map_comp] at h1
  have h3 := congrArg (fun φ => φ.hom (coord K i : AddMonoidAlgebra K (I →₀ ℤ)))
    (Spec.map_injective h1)
  apply Units.ext
  change σ ((lev K (coordEquiv Λ y) : AddMonoidAlgebra K (I →₀ ℤ) →+* K)
      ((galRingHom Λ σ).hom (coord K i))) =
    (lev K (coordEquiv Λ (galAct T σ y)) : AddMonoidAlgebra K (I →₀ ℤ) →+* K)
      (coord K i) at h3
  rw [← lev_coord K (coordEquiv Λ (galAct T σ y)) i]
  exact h3.symm

/-! ### Norms of `K`-points -/

/-- The Galois action in Laurent coordinates, as a group endomorphism. -/
def coordAct (σ : K ≃ₐ[k] K) : (I → Kˣ) →* (I → Kˣ) :=
  (coordEquiv Λ).toMonoidHom.comp ((galAct T σ).comp (coordEquiv Λ).symm.toMonoidHom)

theorem coordAct_apply (σ : K ≃ₐ[k] K) (t : I → Kˣ) (i : I) :
    coordAct Λ σ t i =
      gal σ (Units.map (lev K t : AddMonoidAlgebra K (I →₀ ℤ) →* K) (galUnit Λ σ i)) := by
  have h := coordEquiv_galAct Λ σ ((coordEquiv Λ).symm t) i
  rw [MulEquiv.apply_symm_apply] at h
  exact h

omit [Fintype I] in
theorem coordAct_coordAct (σ τ : K ≃ₐ[k] K) (t : I → Kˣ) :
    coordAct Λ τ (coordAct Λ σ t) = coordAct Λ (τ * σ) t := by
  simp only [coordAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, galAct_galAct]

variable [FiniteDimensional k K]

/-- The norm `∏_σ σ(y)` of the `K`-point with Laurent coordinates `t`. -/
def normPoint (t : I → Kˣ) : testObjBase k K ⟶ T.X :=
  (coordEquiv Λ).symm (∏ σ, coordAct Λ σ t)

omit [Fintype I] in
theorem galAct_normPoint (τ : K ≃ₐ[k] K) (t : I → Kˣ) :
    galAct T τ (normPoint Λ t) = normPoint Λ t := by
  apply (coordEquiv Λ).injective
  have h : coordEquiv Λ (galAct T τ (normPoint Λ t)) = coordAct Λ τ (∏ σ, coordAct Λ σ t) := by
    simp only [coordAct, normPoint, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h, map_prod]
  simp_rw [coordAct_coordAct]
  rw [normPoint, MulEquiv.apply_symm_apply]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun _ => rfl

theorem coordEquiv_normPoint (t : I → Kˣ) :
    coordEquiv Λ (normPoint Λ t) = normFamily (galUnit Λ) t := by
  rw [normPoint, MulEquiv.apply_symm_apply]
  funext i
  rw [Finset.prod_apply]
  exact Finset.prod_congr rfl fun σ _ => coordAct_apply Λ σ t i

/-! ### Density -/

/-- **Rational points of a torus split by a finite Galois extension are dense.** Let `k` be an
infinite field, `K / k` a finite Galois extension and `T` a group scheme over `k` whose base
change to `K` is a split torus. Then the rational points of `T` are Zariski dense. -/
theorem dense_rationalPoints_of_isSplitTorus_baseChange [Infinite k] [IsGalois k K]
    (T : GroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus ((GroupScheme.baseChange (specBase k K)).obj T)) :
    Dense (⋃ p : RationalPoint k T.X, Set.range p.left) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have : Fintype I := Fintype.ofFinite I
  let Λ := e ≪≫ splitTorus.laurentIso I (CommRingCat.of K)
  have hinv : ∀ a, (chart Λ).inv ((chart Λ).hom a) = a := fun a => by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [dense_iff_inter_open]
  rintro U hU ⟨x0, hx0⟩
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K))
  have hsubk : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.X.hom)
    (g := specBase k K) x0 pt (Subsingleton.elim _ _)
  set W : Set (Spec (CommRingCat.of (AddMonoidAlgebra K (I →₀ ℤ)))) :=
    (chart Λ).inv ⁻¹' (pullback.fst T.X.hom (specBase k K) ⁻¹' U) with hW
  have hWo : IsOpen W :=
    (hU.preimage (pullback.fst T.X.hom (specBase k K)).continuous).preimage
      (chart Λ).inv.continuous
  have hwW : (chart Λ).hom w ∈ W := by
    rw [hW, Set.mem_preimage, Set.mem_preimage, hinv, hw]
    exact hx0
  obtain ⟨_, ⟨F, rfl⟩, hFw, hFW⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens
      (R := AddMonoidAlgebra K (I →₀ ℤ))).exists_subset_of_mem_open hwW hWo
  have hFw' : (chart Λ).hom w ∈ PrimeSpectrum.basicOpen F := hFw
  have hF : F ≠ 0 := fun h =>
    (PrimeSpectrum.mem_basicOpen _ _).1 hFw' (h ▸ Ideal.zero_mem _)
  obtain ⟨t, ht⟩ := exists_lev_normFamily_ne_zero (k := k) (galUnit Λ) (galUnit_one Λ) hF
  set z := normPoint Λ t with hz_def
  obtain ⟨p, hp⟩ := exists_rationalPoint_of_fixed T.X z.left
    ((Over.w z).trans (testObjBase_hom (k := k) (K := K)))
    (fun σ => congrArg CommaMorphism.left (galAct_normPoint Λ σ t))
  refine ⟨p.left (specBase k K pt), ?_, Set.mem_iUnion.2 ⟨p, ⟨_, rfl⟩⟩⟩
  have hpz : p.left (specBase k K pt) = z.left pt := by
    rw [← hp, Scheme.Hom.comp_apply]
    rfl
  rw [hpz]
  set x := (baseChangePoints T).symm z with hx_def
  have hx := coordEquiv_left Λ z
  rw [coordEquiv_normPoint] at hx
  have e1 := Scheme.Hom.comp_apply x.left (chart Λ).hom pt
  rw [hx] at e1
  have hmem : Spec.map (CommRingCat.ofHom (lev K (normFamily (galUnit Λ) t) :
      AddMonoidAlgebra K (I →₀ ℤ) →+* K)) pt ∈ W := by
    apply hFW
    show PrimeSpectrum.comap (lev K (normFamily (galUnit Λ) t) :
      AddMonoidAlgebra K (I →₀ ℤ) →+* K) pt ∈ PrimeSpectrum.basicOpen F
    rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      Ideal.eq_bot_of_prime pt.asIdeal, Ideal.mem_bot]
    exact ht
  have hmem' : (chart Λ).hom (x.left pt) ∈ W := by
    convert hmem using 1
    exact e1.symm
  rw [hW, Set.mem_preimage, Set.mem_preimage, hinv] at hmem'
  have e2 := Scheme.Hom.comp_apply x.left (pullback.fst T.X.hom (specBase k K)) pt
  rw [baseChangePoints_symm_left_fst] at e2
  convert hmem' using 1

end Langlands.GroupScheme.TorusDensity
