import Langlands.Cohomology.Profinite.Functoriality
import Mathlib.Order.CompletePartialOrder

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G]

abbrev underlyingRep (X : TopRep.{u} k G) : Rep.{u} k G :=
  Rep.of X.ρ.toRepresentation

@[simp]
theorem underlyingRep_ρ_apply (X : TopRep.{u} k G) (g : G) (x : X) :
    (underlyingRep X).ρ g x = X.ρ g x :=
  rfl

section Discrete

variable [DiscreteTopology k]

def discreteTopRep (A : Rep.{u} k G) : TopRep.{u} k G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  haveI : ContinuousSMul k A := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalAddGroup A := ⟨⟩
  TopRep.of (X := A) <| ContRepresentation.ofMonoidHom
    { toFun g := { toLinearMap := A.ρ g, cont := continuous_of_discreteTopology }
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }

instance (A : Rep.{u} k G) : DiscreteTopology (discreteTopRep A) :=
  ⟨rfl⟩

variable [TopologicalSpace G]

instance (A : Rep.{u} k G) [IsSmoothRep A] : IsSmoothRep (underlyingRep (discreteTopRep A)) :=
  ‹IsSmoothRep A›

end Discrete

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory TopRep ContRepresentation

universe u v w

section Cons

variable {G : Type v} [TopologicalSpace G]

def finConsHomeomorph (m : ℕ) : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by simp
  right_inv x := by simp
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (m + 1) => G) continuous_fst continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk (continuous_pi fun _ => continuous_apply _)

@[simp]
theorem finConsHomeomorph_symm_apply (m : ℕ) (x : Fin (m + 1) → G) :
    (finConsHomeomorph m).symm x = (x 0, Fin.tail x) :=
  rfl

end Cons

variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

def nestedHomeomorph (X : TopRep.{u} k G) : (m : ℕ) → resolutionX X m ≃ₜ C(Fin m → G, X)
  | 0 => Homeomorph.continuousMapOfUnique
  | m + 1 => ((Homeomorph.refl G).arrowCongr (nestedHomeomorph X m)).trans
      (Homeomorph.curry.symm.trans ((finConsHomeomorph m).arrowCongr (Homeomorph.refl X)))

variable (X : TopRep.{u} k G)

@[simp]
theorem nestedHomeomorph_zero_apply (v : resolutionX X 0) (x : Fin 0 → G) :
    nestedHomeomorph X 0 v x = v :=
  rfl

theorem nestedHomeomorph_succ_apply (m : ℕ) (f : resolutionX X (m + 1))
    (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) f x =
      nestedHomeomorph X m ((f : C(G, resolutionX X m)) (x 0)) (Fin.tail x) :=
  rfl

theorem nestedHomeomorph_add (m : ℕ) (a b : resolutionX X m) :
    nestedHomeomorph X m (a + b) = nestedHomeomorph X m a + nestedHomeomorph X m b := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((a + b : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x) +
          nestedHomeomorph X m ((b : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.add_apply, ih]
    rfl

theorem nestedHomeomorph_smul (m : ℕ) (r : k) (a : resolutionX X m) :
    nestedHomeomorph X m (r • a) = r • nestedHomeomorph X m a := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((r • a : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = r • nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.smul_apply, ih]
    rfl

def nestedLinearEquiv (m : ℕ) : resolutionX X m ≃ₗ[k] C(Fin m → G, X) where
  toFun := nestedHomeomorph X m
  invFun := (nestedHomeomorph X m).symm
  map_add' := nestedHomeomorph_add X m
  map_smul' := nestedHomeomorph_smul X m
  left_inv := (nestedHomeomorph X m).symm_apply_apply
  right_inv := (nestedHomeomorph X m).apply_symm_apply

@[simp]
theorem nestedLinearEquiv_apply (m : ℕ) (a : resolutionX X m) :
    nestedLinearEquiv X m a = nestedHomeomorph X m a :=
  rfl

theorem nestedHomeomorph_ρ_apply (m : ℕ) (g : G) (a : resolutionX X m) (x : Fin m → G) :
    nestedHomeomorph X m ((resolutionX X m).ρ g a) x =
      X.ρ g (nestedHomeomorph X m a fun i => g⁻¹ * x i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nestedHomeomorph_succ_apply, nestedHomeomorph_succ_apply]
    exact ih _ _

theorem nestedHomeomorph_d_apply (m : ℕ) (a : resolutionX X m) (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) ((d X m).hom a) x =
      ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) • nestedHomeomorph X m a (fun j => x (i.succAbove j)) := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul]
    rfl
  | succ m ih =>
    have h1 : ((d X (m + 1)).hom a : C(G, resolutionX X (m + 1))) (x 0) =
        a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0)) := by
      rw [hom_d_succ]
      rfl
    rw [nestedHomeomorph_succ_apply, h1,
      show nestedHomeomorph X (m + 1) (a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0))) =
        nestedHomeomorph X (m + 1) a -
          nestedHomeomorph X (m + 1) ((d X m).hom ((a : C(G, resolutionX X m)) (x 0))) from
        map_sub (nestedLinearEquiv X (m + 1)) _ _,
      ContinuousMap.sub_apply, ih, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [nestedHomeomorph_succ_apply X m a, Fin.succ_succAbove_zero]
    congr 1
    funext j
    simp only [Fin.tail, Fin.succ_succAbove_succ]

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory TopRep ContRepresentation

universe u

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_partialProd (n : ℕ) :
    Continuous fun g : Fin n → G => Fin.partialProd g := by
  refine continuous_pi fun i => ?_
  induction i using Fin.induction with
  | zero => simpa using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

variable {k : Type u} [CommRing k]

theorem isLocallyConstant_ρ_apply {Y : Type*} [TopologicalSpace Y] (A : Rep.{u} k G)
    [IsSmoothRep A] {p : Y → G} (hp : Continuous p) {ψ : Y → A} (hψ : IsLocallyConstant ψ) :
    IsLocallyConstant fun y => A.ρ (p y) (ψ y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have h1 : ∀ᶠ z in nhds y, ψ z = ψ y := hψ.eventually_eq y
  have h2 : ∀ᶠ z in nhds y, A.ρ (p z) (ψ y) = A.ρ (p y) (ψ y) :=
    hp.continuousAt.eventually ((isLocallyConstant_apply A (ψ y)).eventually_eq (p y))
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]

end General

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

section Invariant

variable (X : TopRep.{u} k G)

theorem nestedHomeomorph_mul_apply_of_mem_invariants {m : ℕ} {a : resolutionX X m}
    (ha : a ∈ (resolutionX X m).ρ.invariants) (g : G) (x : Fin m → G) :
    nestedHomeomorph X m a (fun i => g * x i) = X.ρ g (nestedHomeomorph X m a x) := by
  have h := nestedHomeomorph_ρ_apply X m g a (fun i => g * x i)
  rw [(mem_invariants a).1 ha g] at h
  simpa using h

end Invariant

variable (X : TopRep.{u} k G) [DiscreteTopology X] [IsSmoothRep (underlyingRep X)]

def toInhomogeneous (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) :
    locallyConstantCochains (underlyingRep X) n :=
  ⟨fun g => nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g),
    (IsLocallyConstant.iff_continuous _).2
      ((nestedHomeomorph X (n + 1) σ.1).continuous.comp (continuous_partialProd n))⟩

omit [IsSmoothRep (underlyingRep X)] in
theorem toInhomogeneous_apply (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) (g : Fin n → G) :
    (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g =
      nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g) :=
  rfl

def homogeneousFun (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (x : Fin (n + 1) → G) : X :=
  X.ρ (x 0) (φ fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)

omit [LocallyCompactSpace G] [DiscreteTopology X] in
theorem isLocallyConstant_homogeneousFun (n : ℕ) {φ : (Fin n → G) → underlyingRep X}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant (homogeneousFun X n φ) :=
  isLocallyConstant_ρ_apply (underlyingRep X) (continuous_apply 0)
    (hφ.comp_continuous (continuous_pi fun _ =>
      ((continuous_apply _).inv).mul (continuous_apply _)))

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [DiscreteTopology X]
  [IsSmoothRep (underlyingRep X)] in
theorem homogeneousFun_mul (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (g : G)
    (x : Fin (n + 1) → G) :
    homogeneousFun X n φ (fun i => g * x i) = X.ρ g (homogeneousFun X n φ x) := by
  simp only [homogeneousFun, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
  rfl

def ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n) :
    (resolutionX X (n + 1)).ρ.invariants :=
  ⟨(nestedHomeomorph X (n + 1)).symm
      ⟨homogeneousFun X n φ.1, (isLocallyConstant_homogeneousFun X n φ.2).continuous⟩, by
    rw [mem_invariants]
    intro g
    apply (nestedHomeomorph X (n + 1)).injective
    ext x
    rw [nestedHomeomorph_ρ_apply, Homeomorph.apply_symm_apply]
    change X.ρ g (homogeneousFun X n φ.1 fun i => g⁻¹ * x i) = homogeneousFun X n φ.1 x
    rw [homogeneousFun_mul]
    change (X.ρ g * X.ρ g⁻¹) _ = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl⟩

omit [DiscreteTopology X] in
theorem nestedHomeomorph_ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n)
    (x : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 1) (ofInhomogeneous X n φ).1 x = homogeneousFun X n φ.1 x := by
  simp [ofInhomogeneous]

def homogeneousEquiv (n : ℕ) :
    locallyConstantCochains (underlyingRep X) n ≃ₗ[k] (resolutionX X (n + 1)).ρ.invariants :=
  LinearEquiv.symm
  { toFun := toInhomogeneous X n
    invFun := ofInhomogeneous X n
    map_add' σ τ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_add, Pi.add_apply]
      rw [nestedHomeomorph_add]
      rfl
    map_smul' r σ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [nestedHomeomorph_smul]
      rfl
    left_inv σ := by
      apply Subtype.ext
      apply (nestedHomeomorph X (n + 1)).injective
      ext x
      rw [nestedHomeomorph_ofInhomogeneous]
      change X.ρ (x 0) (nestedHomeomorph X (n + 1) σ.1
        (Fin.partialProd fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)) = _
      rw [← nestedHomeomorph_mul_apply_of_mem_invariants X σ.2]
      congr 1
      exact Fin.partialProd_left_inv x
    right_inv φ := by
      ext g
      rw [toInhomogeneous_apply, nestedHomeomorph_ofInhomogeneous]
      simp only [homogeneousFun, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
      rfl }

omit [IsSmoothRep (underlyingRep X)] in

theorem nestedHomeomorph_d_partialProd (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants)
    (g : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 2) ((d X (n + 1)).hom σ.1) (Fin.partialProd g) =
      (inhomogeneousCochains.d (underlyingRep X) n).hom
        (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g := by
  rw [nestedHomeomorph_d_apply, Fin.sum_univ_succ, inhomogeneousCochains.d_hom_apply]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.partialProd_succ']
    exact nestedHomeomorph_mul_apply_of_mem_invariants X σ.2 _ _
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInhomogeneous_apply, Fin.partialProd_contractNth, Fin.val_succ]
    rfl

theorem homogeneousEquiv_symm_d (i : ℕ) (σ : (homogeneousCochains X).X i) :
    (homogeneousEquiv X (i + 1)).symm (((homogeneousCochains X).d i (i + 1)).hom σ) =
      (dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ) := by
  apply Subtype.ext
  funext g
  rw [dLocallyConstant_hom_apply]
  change nestedHomeomorph X (i + 2) (((homogeneousCochains X).d i (i + 1)).hom σ).1
    (Fin.partialProd g) = _
  rw [homogeneousCochains.d_apply]
  exact nestedHomeomorph_d_partialProd X i σ g

noncomputable def cochainsIsoHomogeneousCochains :
    cochains (underlyingRep X) ≅
      ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
        (homogeneousCochains X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (homogeneousEquiv X n).toModuleIso) (by
    rintro i j (rfl : i + 1 = j)
    rw [cochains_d]
    ext φ : 2
    obtain ⟨σ, rfl⟩ := (homogeneousEquiv X i).symm.surjective φ
    change ((homogeneousCochains X).d i (i + 1)).hom (homogeneousEquiv X i
      ((homogeneousEquiv X i).symm σ)) = homogeneousEquiv X (i + 1)
        ((dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ))
    rw [LinearEquiv.apply_symm_apply]
    exact (homogeneousEquiv X (i + 1)).symm_apply_eq.1 (homogeneousEquiv_symm_d X i σ))

noncomputable def isoContinuousCohomology (n : ℕ) :
    cohomology (underlyingRep X) n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology n X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cochainsIsoHomogeneousCochains X) ≪≫
    ((homogeneousCochains X).sc n).mapHomologyIso (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))

noncomputable def linearEquivContinuousCohomology (n : ℕ) :
    cohomology (underlyingRep X) n ≃ₗ[k]
      ((continuousCohomology n X : TopModuleCat.{u} k) : Type u) :=
  (isoContinuousCohomology X n).toLinearEquiv


section Naturality

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- The morphism of representations underlying a morphism `TopRep.res φ X ⟶ Y` of topological
representations. -/
abbrev underlyingHom {X : TopRep.{u} k G} {Y : TopRep.{u} k H} (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    Rep.res (φ : H →* G) (underlyingRep X) ⟶ underlyingRep Y :=
  Rep.ofHom f.hom.toIntertwiningMap

theorem nestedHomeomorph_resolutionMap {X : TopRep.{u} k G} {Y : TopRep.{u} k H} (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (m : ℕ) (a : resolutionX X m) (x : Fin m → H) :
    nestedHomeomorph Y m ((ContinuousCohomology.resolutionMap φ f m).hom a) x =
      f.hom (nestedHomeomorph X m a (⇑φ ∘ x)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nestedHomeomorph_succ_apply, nestedHomeomorph_succ_apply]
    exact ih _ _

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [IsTopologicalGroup H] [LocallyCompactSpace H] in
theorem comp_partialProd {n : ℕ} (φ : H →ₜ* G) (g : Fin n → H) :
    ⇑φ ∘ Fin.partialProd g = Fin.partialProd (⇑φ ∘ g) := by
  funext i
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    simp only [Function.comp_apply, Fin.partialProd_succ, map_mul] at ih ⊢
    rw [ih]

variable {X : TopRep.{u} k G} [DiscreteTopology X] [IsSmoothRep (underlyingRep X)]
  {Y : TopRep.{u} k H} [DiscreteTopology Y] [IsSmoothRep (underlyingRep Y)]
  (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y)

theorem toInhomogeneous_cochainsMap (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) :
    toInhomogeneous Y n (((ContinuousCohomology.cochainsMap φ f).f n).hom σ) =
      ((cochainsMap φ (underlyingHom φ f)).f n).hom (toInhomogeneous X n σ) := by
  apply Subtype.ext
  funext g
  change nestedHomeomorph Y (n + 1)
      ((ContinuousCohomology.resolutionMap φ f (n + 1)).hom σ.1) (Fin.partialProd g) =
    f.hom (nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd (⇑φ ∘ g)))
  rw [nestedHomeomorph_resolutionMap, comp_partialProd]

/-- The isomorphism of complexes `cochainsIsoHomogeneousCochains` is natural in the group and
the coefficients. -/
theorem cochainsMap_comp_cochainsIsoHomogeneousCochains_hom :
    cochainsMap φ (underlyingHom φ f) ≫ (cochainsIsoHomogeneousCochains Y).hom =
      (cochainsIsoHomogeneousCochains X).hom ≫
        ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex _).map
          (ContinuousCohomology.cochainsMap φ f) := by
  ext n x : 3
  change homogeneousEquiv Y n (((cochainsMap φ (underlyingHom φ f)).f n).hom x) =
    ((ContinuousCohomology.cochainsMap φ f).f n).hom (homogeneousEquiv X n x)
  have h := toInhomogeneous_cochainsMap φ f n (homogeneousEquiv X n x)
  have hx : toInhomogeneous X n (homogeneousEquiv X n x) = x :=
    (homogeneousEquiv X n).symm_apply_apply x
  rw [hx] at h
  rw [← h]
  exact (homogeneousEquiv Y n).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
-- The homology of the image of a complex under `forget₂` and the homology of the image of its
-- short complex in degree `n` are definitionally, not reducibly, equal.
/-- Naturality of the comparison with Mathlib's continuous cohomology: for a continuous
homomorphism `φ : H →ₜ* G` and a morphism `f : TopRep.res φ X ⟶ Y` of discrete topological
representations, `map φ f n` corresponds to `ContinuousCohomology.map φ f n`. -/
theorem isoContinuousCohomology_naturality (n : ℕ) :
    map φ (underlyingHom φ f) n ≫ (isoContinuousCohomology Y n).hom =
      (isoContinuousCohomology X n).hom ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (ContinuousCohomology.map φ f n) := by
  let F := forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)
  have h1 := congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
    (cochainsMap_comp_cochainsIsoHomogeneousCochains_hom φ f)
  simp only [HomologicalComplex.homologyMap_comp] at h1
  have h2 := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (ContinuousCohomology.cochainsMap φ f)) F
  change HomologicalComplex.homologyMap (cochainsMap φ (underlyingHom φ f)) n ≫
      (HomologicalComplex.homologyMap (cochainsIsoHomogeneousCochains Y).hom n ≫
        (((homogeneousCochains Y).sc n).mapHomologyIso F).hom) =
    (HomologicalComplex.homologyMap (cochainsIsoHomogeneousCochains X).hom n ≫
        (((homogeneousCochains X).sc n).mapHomologyIso F).hom) ≫
      F.map (HomologicalComplex.homologyMap (ContinuousCohomology.cochainsMap φ f) n)
  rw [reassoc_of% h1, Category.assoc]
  congr 1

end Naturality

section Discrete

variable [DiscreteTopology k]

/-- A smooth representation over a discrete ring, with the discrete topology on its carrier, as a
discrete module of `Langlands.Continuous` (its action is jointly continuous because the orbit maps
are locally constant). -/
noncomputable def _root_.Langlands.Continuous.DiscreteModule.ofSmoothRep (A : Rep.{u} k G)
    [IsSmoothRep A] : Continuous.DiscreteModule k G where
  toTopRep := discreteTopRep A
  continuous_action := by
    refine continuous_prod_of_discrete_right.2 fun a => ?_
    have h : IsLocallyConstant fun g : G => ((discreteTopRep A).ρ g a : discreteTopRep A) :=
      isLocallyConstant_apply A a
    exact h.continuous

omit [LocallyCompactSpace G] in
theorem _root_.Langlands.Continuous.DiscreteModule.ofSmoothRep_toRep (A : Rep.{u} k G)
    [IsSmoothRep A] : (Continuous.DiscreteModule.ofSmoothRep A).toRep = A :=
  rfl

/-- The comparison for a smooth representation over a discrete ring, given the discrete
topology. -/
noncomputable def isoContinuousCohomologyDiscrete (A : Rep.{u} k G) [IsSmoothRep A]
    (n : ℕ) :
    cohomology A n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology n (discreteTopRep A)) :=
  isoContinuousCohomology (discreteTopRep A) n

noncomputable def linearEquivContinuousCohomologyDiscrete (A : Rep.{u} k G)
    [IsSmoothRep A] (n : ℕ) :
    cohomology A n ≃ₗ[k]
      ((continuousCohomology n (discreteTopRep A) : TopModuleCat.{u} k) : Type u) :=
  linearEquivContinuousCohomology (discreteTopRep A) n

end Discrete

end Langlands.ProfiniteCohomology
