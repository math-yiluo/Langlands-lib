import Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology
import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Inverse limit topology on limits of discrete representations

Milne, *Étale Cohomology* (1980), Ch. V, §1, p.164: for a connected scheme `X` with geometric
point `x` and an `l`-adic sheaf `F`, "the action of `π₁(X, x)` on `F_x = lim (F_n)_x` need not
factor through a finite quotient. However, the action is continuous when `F_x` is given the
`l`-adic topology". Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
§3, p.308, allows "any continuous `K_ℓ`-module" as coefficients and then takes a free
`𝒪/ℓ^m𝒪`-module of finite order with a continuous action of `K_ℓ` factoring through a quotient
`K_ℓ/K_ℓ(n)`; §4, p.312, (4.10.4) uses the cohomology of the inverse system `{𝓛̃_m}`.

This module gives the point of a cone over a diagram `M : J ⥤ Action (ModuleCat R) G` the inverse
limit topology of the levels with the discrete topology. The topology is not compared with an
`l`-adic or `I`-adic topology on the limit, and smoothness of the levels is an explicit
hypothesis wherever it is used.

* `ContinuousLimit.ConeSpace c`: the point of a cone `c`, with the coarsest topology for which
  every projection `proj c j` to a discrete level is continuous (`continuous_iff`,
  `isLocallyConstant_proj`). It is a topological additive group, each `act c g` is continuous
  (`continuous_act`), and the point of a limit cone is Hausdorff (`t2Space_of_isLimit`).
* `continuous_of_isSmooth`: a smooth representation on a discrete module has a jointly continuous
  action map `G × V → V`. `continuous_action`: if every level is smooth, the action
  `G × ConeSpace c → ConeSpace c` is jointly continuous.
* `ContinuousSMul R (ConeSpace c)` for a discrete ring `R` (instance), when every element of every
  level is killed by an open ideal (`continuousSMul_of_ideal`), and for the `I`-adic topology
  when every level is killed by a power of `I` (`continuousSMul_of_isAdic`).
* `continuous_hom`: a map of cone points compatible with a morphism of diagrams is continuous.
* Mathlib packaging: `contRepresentation c`, `contIntertwiningMap`, `topRep c : TopRep R G`,
  `contAction c hM : ContAction (TopModuleCat R) G` for smooth levels, and, for a discrete ring,
  `limitTopRepFunctor R G J : (J ⥤ Action (ModuleCat R) G) ⥤ TopRep R G`.
* `EtaleAdicCohomology.AdicCohomologySpace R ρ q F`: the underlying module of the published
  `equivariantAdicCohomology R ρ q` of an inverse system `F` of equivariant étale sheaves,
  `lim_m H^q(X, F_m)`, with this topology. It is Hausdorff, maps induced by morphisms of
  systems are continuous (`continuous_map`), and the action is jointly continuous when every
  `H^q(X, F_m)` is smooth (`continuous_action`); `adicContRepresentation`, `adicContAction` and,
  for a discrete ring, the functor `equivariantAdicCohomologyTopRep R ρ q` package it.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite Filter Topology

universe u v w t

namespace ContinuousLimit

section Level

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {V : Type*} [AddCommGroup V] [Module R V]

/-- For a smooth representation `ρ`, the orbit map `g ↦ ρ g v` of each vector `v` is eventually
equal to `ρ g₀ v` near every `g₀`. -/
theorem eventually_eq_of_isSmooth {ρ : Representation R G V} (hρ : IsSmooth ρ) (g₀ : G)
    (v : V) : ∀ᶠ g in 𝓝 g₀, ρ g v = ρ g₀ v := by
  obtain ⟨K, hK⟩ := hρ v
  have hcont : Continuous fun g : G => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hK1 : (K : Set G) ∈ 𝓝 (g₀⁻¹ * g₀) := by
    rw [inv_mul_cancel]
    exact K.isOpen.mem_nhds K.one_mem
  filter_upwards [hcont.continuousAt.preimage_mem_nhds hK1] with g hg
  have hfix : ρ (g₀⁻¹ * g) v = v := (Representation.mem_invariants _ v).1 hK ⟨_, hg⟩
  calc ρ g v = ρ (g₀ * (g₀⁻¹ * g)) v := by rw [mul_inv_cancel_left]
    _ = ρ g₀ v := by rw [map_mul, Module.End.mul_apply, hfix]

/-- A smooth representation on a module with the discrete topology is jointly continuous. -/
theorem continuous_of_isSmooth [TopologicalSpace V] [DiscreteTopology V]
    {ρ : Representation R G V} (hρ : IsSmooth ρ) :
    Continuous fun p : G × V => ρ p.1 p.2 := by
  refine (IsLocallyConstant.iff_continuous _).1 ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g₀, v₀⟩
  have h₁ := (continuous_fst.tendsto (g₀, v₀)).eventually (eventually_eq_of_isSmooth hρ g₀ v₀)
  have h₂ := (continuous_snd.tendsto (g₀, v₀)).eventually
    ((IsLocallyConstant.of_discrete (id : V → V)).eventually_eq v₀)
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  rw [show p.2 = v₀ from hp₂, hp₁]

end Level

section Cone

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
variable {J : Type w} [Category.{t} J] {M : J ⥤ Action (ModuleCat.{u} R) G}

/-- The point of a cone `c` over a diagram of representations, to be given the inverse limit
topology of the discrete levels. -/
def ConeSpace (c : Cone M) : Type u := c.pt.V

variable (c : Cone M)

instance : AddCommGroup (ConeSpace c) := inferInstanceAs (AddCommGroup c.pt.V)

instance : Module R (ConeSpace c) := inferInstanceAs (Module R c.pt.V)

/-- The projection of the cone point to the level `j`. -/
def proj (j : J) : ConeSpace c →ₗ[R] (M.obj j).V := (c.π.app j).hom.hom

/-- The action of `g` on the cone point. -/
def act (g : G) : ConeSpace c →ₗ[R] ConeSpace c := (c.pt.ρ g).hom

lemma proj_act (j : J) (g : G) (x : ConeSpace c) :
    proj c j (act c g x) = ((M.obj j).ρ g).hom (proj c j x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((c.π.app j).comm g)) x

/-- The inverse limit topology: the coarsest topology for which every projection to a level
with the discrete topology is continuous. -/
instance : TopologicalSpace (ConeSpace c) :=
  ⨅ j, TopologicalSpace.induced (proj c j) ⊥

/-- A map into the cone point is continuous if and only if its composite with every projection
is locally constant. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → ConeSpace c) :
    Continuous f ↔ ∀ j, IsLocallyConstant fun x => proj c j (f x) := by
  refine continuous_iInf_rng.trans (forall_congr' fun j => continuous_induced_rng.trans ?_)
  let _ : TopologicalSpace (M.obj j).V := ⊥
  have : DiscreteTopology (M.obj j).V := ⟨rfl⟩
  exact (IsLocallyConstant.iff_continuous _).symm

/-- Every projection is locally constant. -/
theorem isLocallyConstant_proj (j : J) : IsLocallyConstant (proj c j) :=
  (continuous_iff c id).1 continuous_id j

instance : IsTopologicalAddGroup (ConeSpace c) where
  continuous_add := (continuous_iff c _).2 fun j => by
    have h := ((isLocallyConstant_proj c j).comp_continuous continuous_fst).comp₂
      ((isLocallyConstant_proj c j).comp_continuous continuous_snd) (· + ·)
    simpa only [Function.comp_apply, map_add] using h
  continuous_neg := (continuous_iff c _).2 fun j => by
    have h := (isLocallyConstant_proj c j).comp (fun y => -y)
    simpa only [Function.comp_def, map_neg] using h

/-- Each element of the group acts continuously. -/
theorem continuous_act (g : G) : Continuous (act c g) :=
  (continuous_iff c _).2 fun j => by
    have h := (isLocallyConstant_proj c j).comp ((M.obj j).ρ g).hom
    simpa only [Function.comp_def, proj_act] using h

/-- If the orbit maps `r ↦ r • y` of every level are locally constant, scalar multiplication on
the cone point is continuous. -/
theorem continuousSMul [TopologicalSpace R]
    (hR : ∀ j (y : (M.obj j).V), IsLocallyConstant fun r : R => r • y) :
    ContinuousSMul R (ConeSpace c) := by
  refine ⟨(continuous_iff c _).2 fun j => ?_⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨r₀, x₀⟩
  have h₁ := (continuous_fst.tendsto (r₀, x₀)).eventually
    ((hR j (proj c j x₀)).eventually_eq r₀)
  have h₂ := (continuous_snd.tendsto (r₀, x₀)).eventually
    ((isLocallyConstant_proj c j).eventually_eq x₀)
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  simp only [map_smul] at hp₂ ⊢
  rw [hp₂, hp₁]

instance [TopologicalSpace R] [DiscreteTopology R] : ContinuousSMul R (ConeSpace c) :=
  continuousSMul c fun _ _ => IsLocallyConstant.of_discrete _

/-- If `y` is killed by an open ideal `I` of a topological ring, `r ↦ r • y` is locally
constant. -/
theorem isLocallyConstant_smul_of_ideal {N : Type*} [AddCommGroup N] [Module R N]
    [TopologicalSpace R] [IsTopologicalAddGroup R] (I : Ideal R) (hI : IsOpen (I : Set R))
    (y : N) (hy : ∀ r ∈ I, r • y = 0) : IsLocallyConstant fun r : R => r • y := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro r₀
  have hcont : Continuous fun r : R => r - r₀ := continuous_id.sub continuous_const
  have hI0 : (I : Set R) ∈ 𝓝 (r₀ - r₀) := by
    rw [sub_self]
    exact hI.mem_nhds I.zero_mem
  filter_upwards [hcont.continuousAt.preimage_mem_nhds hI0] with r hr
  calc r • y = r₀ • y + (r - r₀) • y := by rw [← add_smul, add_sub_cancel]
    _ = r₀ • y := by rw [hy _ hr, add_zero]

/-- If every element of every level is killed by an open ideal, scalar multiplication on the
cone point is continuous. -/
theorem continuousSMul_of_ideal [TopologicalSpace R] [IsTopologicalAddGroup R]
    (hM : ∀ j (y : (M.obj j).V), ∃ I : Ideal R, IsOpen (I : Set R) ∧ ∀ r ∈ I, r • y = 0) :
    ContinuousSMul R (ConeSpace c) :=
  continuousSMul c fun j y => by
    obtain ⟨I, hI, hy⟩ := hM j y
    exact isLocallyConstant_smul_of_ideal I hI y hy

/-- For the `I`-adic topology on `R`, scalar multiplication on the cone point is continuous
when every level is killed by a power of `I`. -/
theorem continuousSMul_of_isAdic [TopologicalSpace R] [IsTopologicalRing R] {I : Ideal R}
    (hI : IsAdic I) (hM : ∀ j, ∃ n : ℕ, ∀ r ∈ I ^ n, ∀ y : (M.obj j).V, r • y = 0) :
    ContinuousSMul R (ConeSpace c) :=
  continuousSMul_of_ideal c fun j y => by
    obtain ⟨n, hn⟩ := hM j
    exact ⟨I ^ n, (isAdic_iff.1 hI).1 n, fun r hr => hn r hr y⟩

/-- The action is jointly continuous when every level is a smooth representation. -/
theorem continuous_action [TopologicalSpace G] [ContinuousMul G]
    (hM : ∀ j, IsSmooth ((Rep.ActionToRep R G).obj (M.obj j)).ρ) :
    Continuous fun p : G × ConeSpace c => act c p.1 p.2 := by
  refine (continuous_iff c _).2 fun j => ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g₀, x₀⟩
  have h₁ := (continuous_fst.tendsto (g₀, x₀)).eventually
    (eventually_eq_of_isSmooth (hM j) g₀ (proj c j x₀))
  have h₂ := (continuous_snd.tendsto (g₀, x₀)).eventually
    ((isLocallyConstant_proj c j).eventually_eq x₀)
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  rw [proj_act, proj_act, hp₂]
  exact hp₁

/-- The cone point of a limit cone is Hausdorff. -/
theorem t2Space_of_isLimit [PreservesLimit M (Action.forget (ModuleCat.{u} R) G)]
    [PreservesLimit (M ⋙ Action.forget (ModuleCat.{u} R) G) (forget (ModuleCat.{u} R))]
    {c : Cone M} (hc : IsLimit c) : T2Space (ConeSpace c) := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, proj c j x ≠ proj c j y := by
    by_contra! h
    exact hxy (Concrete.isLimit_ext (M ⋙ Action.forget (ModuleCat.{u} R) G)
      (isLimitOfPreserves (Action.forget (ModuleCat.{u} R) G) hc) x y h)
  refine ⟨proj c j ⁻¹' {proj c j x}, proj c j ⁻¹' {proj c j y},
    (isLocallyConstant_proj c j).isOpen_fiber _, (isLocallyConstant_proj c j).isOpen_fiber _,
    rfl, rfl, Set.disjoint_left.2 fun z hz hz' => hj ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz hz'
  exact hz.symm.trans hz'

/-- A morphism of cone points compatible with a morphism of diagrams is continuous. -/
theorem continuous_hom {M' : J ⥤ Action (ModuleCat.{u} R) G} {c' : Cone M'} (α : M ⟶ M')
    (f : c.pt ⟶ c'.pt) (hf : ∀ j, f ≫ c'.π.app j = c.π.app j ≫ α.app j) :
    Continuous (X := ConeSpace c) (Y := ConeSpace c') f.hom.hom := by
  refine (continuous_iff c' (X := ConeSpace c) f.hom.hom).2 fun j => ?_
  have e : (fun x : ConeSpace c => proj c' j (f.hom.hom x)) = (α.app j).hom.hom ∘ proj c j :=
    funext fun x => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (congrArg Action.Hom.hom (hf j))) x
  rw [e]
  exact (isLocallyConstant_proj c j).comp _

lemma act_one (x : ConeSpace c) : act c 1 x = x := by
  change (c.pt.ρ 1).hom x = x
  rw [map_one]
  rfl

lemma act_mul (g h : G) (x : ConeSpace c) : act c (g * h) x = act c g (act c h x) := by
  change (c.pt.ρ (g * h)).hom x = (c.pt.ρ g).hom ((c.pt.ρ h).hom x)
  rw [map_mul]
  rfl

/-- The action of `G` on the cone point, as a representation by continuous linear maps. -/
def contRepresentation : ContRepresentation R G (ConeSpace c) :=
  .ofMonoidHom
    { toFun g := ⟨act c g, continuous_act c g⟩
      map_one' := ContinuousLinearMap.ext (act_one c)
      map_mul' g h := ContinuousLinearMap.ext (act_mul c g h) }

@[simp]
lemma contRepresentation_apply (g : G) (x : ConeSpace c) :
    contRepresentation c g x = act c g x :=
  rfl

/-- A morphism of cone points compatible with a morphism of diagrams, as a continuous
intertwining map. -/
def contIntertwiningMap {M' : J ⥤ Action (ModuleCat.{u} R) G} (c' : Cone M') (α : M ⟶ M')
    (f : c.pt ⟶ c'.pt) (hf : ∀ j, f ≫ c'.π.app j = c.π.app j ≫ α.app j) :
    ContIntertwiningMap (contRepresentation c) (contRepresentation c') where
  toContinuousLinearMap := ⟨f.hom.hom, continuous_hom c α f hf⟩
  isIntertwining' g := ContinuousLinearMap.ext fun x =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.comm g)) x

@[simp]
lemma contIntertwiningMap_apply {M' : J ⥤ Action (ModuleCat.{u} R) G} (c' : Cone M')
    (α : M ⟶ M') (f : c.pt ⟶ c'.pt) (hf : ∀ j, f ≫ c'.π.app j = c.π.app j ≫ α.app j)
    (x : ConeSpace c) : contIntertwiningMap c c' α f hf x = f.hom.hom x :=
  rfl

/-- The cone point as a topological representation, for a topological ring `R` acting
continuously on it (for instance a discrete ring, or see `continuousSMul`). -/
abbrev topRep [TopologicalSpace R] [ContinuousSMul R (ConeSpace c)] : TopRep.{u} R G :=
  TopRep.of (contRepresentation c)

/-- When every level is smooth, the cone point is an object of `ContAction (TopModuleCat R) G`:
an action of `G` on a topological module that is jointly continuous. -/
def contAction [TopologicalSpace R] [ContinuousSMul R (ConeSpace c)] [TopologicalSpace G]
    [ContinuousMul G] (hM : ∀ j, IsSmooth ((Rep.ActionToRep R G).obj (M.obj j)).ρ) :
    ContAction (TopModuleCat.{u} R) G :=
  ⟨TopRep.toActionTopModFunc.obj (topRep c), (Action.isContinuous_def _).2 (continuous_action c hM)⟩

end Cone

section Functor

variable (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] (G : Type v) [Group G]
  (J : Type w) [Category.{t} J] [HasLimitsOfShape J (Action (ModuleCat.{u} R) G)]

/-- For a discrete ring `R`, the limit of a diagram of representations with the inverse limit
topology of the discrete levels, as a functor to topological representations. -/
def limitTopRepFunctor : (J ⥤ Action (ModuleCat.{u} R) G) ⥤ TopRep.{u} R G where
  obj M := topRep (limit.cone M)
  map {M M'} α := TopRep.ofHom
    (contIntertwiningMap (limit.cone M) (limit.cone M') α (lim.map α) (limMap_π α))
  map_id M := TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun x => by
    change (lim.map (𝟙 M)).hom.hom x = x
    rw [CategoryTheory.Functor.map_id]
    rfl))
  map_comp α β := TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun x => by
    change (lim.map (α ≫ β)).hom.hom x = (lim.map β).hom.hom ((lim.map α).hom.hom x)
    rw [CategoryTheory.Functor.map_comp]
    rfl))

variable {R G J}

lemma limitTopRepFunctor_obj_V (M : J ⥤ Action (ModuleCat.{u} R) G) :
    ((limitTopRepFunctor R G J).obj M).V = (limit M).V :=
  rfl

lemma limitTopRepFunctor_obj_ρ (M : J ⥤ Action (ModuleCat.{u} R) G) (g : G)
    (x : ((limitTopRepFunctor R G J).obj M).V) :
    ((limitTopRepFunctor R G J).obj M).ρ g x = ((limit M).ρ g).hom x :=
  rfl

lemma limitTopRepFunctor_map_apply {M M' : J ⥤ Action (ModuleCat.{u} R) G} (α : M ⟶ M')
    (x : ((limitTopRepFunctor R G J).obj M).V) :
    ((limitTopRepFunctor R G J).map α).hom x = (limMap α).hom.hom x :=
  rfl

end Functor

end ContinuousLimit

namespace EtaleAdicCohomology

open AlgebraicGeometry Langlands.Geometry ContinuousLimit

section Equivariant

variable {X : Scheme.{u}} (R : Type u) [CommRing R] {G : Type w} [Group G]
  (ρ : G →* (Aut X)ᵐᵒᵖ) (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ)

/-- The module `lim_m H^q(X, F_m)` underlying `equivariantAdicCohomology R ρ q F`, with the
inverse limit topology of the discrete modules `H^q(X, F_m)`. -/
abbrev AdicCohomologySpace : Type u :=
  ConeSpace (limit.cone (F ⋙ EtaleCohomologyAction.pullbackCohomologyFunctor R ρ q))

lemma adicCohomologySpace_eq :
    AdicCohomologySpace R ρ q F = ((equivariantAdicCohomology R ρ q).obj F).V :=
  rfl

instance : T2Space (AdicCohomologySpace R ρ q F) :=
  t2Space_of_isLimit (limit.isLimit _)

/-- The map `lim_m H^q(X, F_m) → lim_m H^q(X, E_m)` induced by a morphism of inverse systems is
continuous. -/
theorem continuous_map {E : ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ} (φ : F ⟶ E) :
    Continuous (X := AdicCohomologySpace R ρ q F) (Y := AdicCohomologySpace R ρ q E)
      ((equivariantAdicCohomology R ρ q).map φ).hom.hom :=
  continuous_hom _ (Functor.whiskerRight φ _) _ (limMap_π _)

/-- The action of `G` on `lim_m H^q(X, F_m)` is jointly continuous when every `H^q(X, F_m)` is a
smooth representation. -/
theorem continuous_action [TopologicalSpace G] [ContinuousMul G]
    (hF : ∀ n, IsSmooth ((Rep.ActionToRep R G).obj
      ((EtaleCohomologyAction.pullbackCohomologyFunctor R ρ q).obj (F.obj n))).ρ) :
    Continuous (Y := AdicCohomologySpace R ρ q F) fun p : G × AdicCohomologySpace R ρ q F =>
      (((equivariantAdicCohomology R ρ q).obj F).ρ p.1).hom p.2 :=
  ContinuousLimit.continuous_action
    (limit.cone (F ⋙ EtaleCohomologyAction.pullbackCohomologyFunctor R ρ q)) hF

/-- `lim_m H^q(X, F_m)` as a representation of `G` by continuous linear maps. -/
abbrev adicContRepresentation : ContRepresentation R G (AdicCohomologySpace R ρ q F) :=
  contRepresentation _

/-- When every `H^q(X, F_m)` is smooth, `lim_m H^q(X, F_m)` as an object of
`ContAction (TopModuleCat R) G`. -/
def adicContAction [TopologicalSpace R] [ContinuousSMul R (AdicCohomologySpace R ρ q F)]
    [TopologicalSpace G] [ContinuousMul G]
    (hF : ∀ n, IsSmooth ((Rep.ActionToRep R G).obj
      ((EtaleCohomologyAction.pullbackCohomologyFunctor R ρ q).obj (F.obj n))).ρ) :
    ContAction (TopModuleCat.{u} R) G :=
  contAction (limit.cone (F ⋙ EtaleCohomologyAction.pullbackCohomologyFunctor R ρ q)) hF

/-- For a discrete ring `R`, `equivariantAdicCohomology R ρ q` with the inverse limit topology, as
a functor to topological representations. -/
def equivariantAdicCohomologyTopRep [TopologicalSpace R] [DiscreteTopology R] :
    (ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ) ⥤ TopRep.{u} R G :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (EtaleCohomologyAction.pullbackCohomologyFunctor R ρ q) ⋙
    limitTopRepFunctor R G ℕᵒᵖ

lemma equivariantAdicCohomologyTopRep_obj_V [TopologicalSpace R] [DiscreteTopology R] :
    ((equivariantAdicCohomologyTopRep R ρ q).obj F).V =
      ((equivariantAdicCohomology R ρ q).obj F).V :=
  rfl

end Equivariant

end EtaleAdicCohomology

end Langlands.Cohomology
