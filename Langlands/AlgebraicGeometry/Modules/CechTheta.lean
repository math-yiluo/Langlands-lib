import Langlands.AlgebraicGeometry.Modules.CechShift

/-!
# Degree-one Čech cocycles and `H¹` as a relation

Let `f : P ⟶ Spec R`, let `M` be an `𝒪_P`-module whose Čech complexes for standard covers of
affine opens are exact, and let `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` be its embedding into the chosen
injective module. For a family `V` of opens covering `P`, a Čech `1`-cocycle `z` of `M` on `V`
represents the class `x ∈ H¹(P, M)` (`Rep f M V z x`) if `ι z = d t` for a `0`-cochain `t` of
`I` such that the sections `π t` of `Q` are the restrictions of a global section `q`, and `x` is
the image of `q` under the connecting morphism `Γ(P, Q) ⟶ H¹(P, M)`.

For a finite family covering `P`, every cocycle represents exactly one class, the relation is
additive and `R`-linear, and coboundaries represent `0`. If the members of `V` are affine,
every class is represented by a cocycle.
-/

universe w w₁ w₂ u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechTheta

open Langlands.Cohomology CechDegreeOne CechShift

variable {P : Scheme.{u}} {R : CommRingCat.{u}} (f : P ⟶ Spec R)

section Conn

variable [HasDerivedCategory.{w₁} P.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]
  (M : P.Modules)

/-- The connecting morphism `Γ(P, Q) ⟶ H¹(P, M)` of the embedding `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` of `M`
into its injective hull, precomposed with the inverse of the degree-zero comparison
`R⁰Γ ≅ Γ`. -/
noncomputable def conn :
    (DerivedSections.relativeGlobalSections f).obj (cokernel (Injective.ι M)) ⟶
      (DerivedSections.relativeCohomology f 1).obj M :=
  (DerivedSections.relativeGlobalSections f).rightDerivedZeroIsoSelf.inv.app _ ≫
    DerivedPlus.rightDerivedδ (DerivedSections.relativeGlobalSections f)
      (PushforwardInjectiveAcyclic.injectiveSc_shortExact M) 0 1 rfl

/-- Global sections of `Q` coming from `I` are killed by the connecting morphism. -/
lemma conn_π (T : Γ(Injective.under M, ⊤)) :
    (conn f M).hom ((cokernel.π (Injective.ι M)).app ⊤ T) = 0 := by
  let F := DerivedSections.relativeGlobalSections f
  have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact M
  have e₁ := congrArg (fun k => k.hom T)
    (F.rightDerivedZeroIsoSelf.inv.naturality (cokernel.π (Injective.ι M)))
  have e₃ := congrArg (fun k => k.hom ((F.rightDerivedZeroIsoSelf.inv.app _).hom T))
    (DerivedPlus.rightDerived_map_comp_δ F hS 0 1 rfl)
  exact (congrArg (DerivedPlus.rightDerivedδ F hS 0 1 rfl).hom e₁).trans e₃

lemma conn_add (q q' : Γ(cokernel (Injective.ι M), ⊤)) :
    (conn f M).hom (q + q') = (conn f M).hom q + (conn f M).hom q' :=
  map_add (conn f M).hom q q'

lemma conn_sub (q q' : Γ(cokernel (Injective.ι M), ⊤)) :
    (conn f M).hom (q - q') = (conn f M).hom q - (conn f M).hom q' :=
  map_sub (conn f M).hom q q'

lemma conn_zero : (conn f M).hom (0 : Γ(cokernel (Injective.ι M), ⊤)) = 0 :=
  map_zero (conn f M).hom

/-- The `R`-module structure of `Γ(P, Q)` is given by `structureRingHom f`. -/
lemma conn_smul (a : R) (q : Γ(cokernel (Injective.ι M), ⊤)) :
    (conn f M).hom ((DerivedSections.structureRingHom f).hom a • q) =
      a • (conn f M).hom q := by
  let q' : (DerivedSections.relativeGlobalSections f).obj (cokernel (Injective.ι M)) := q
  exact map_smul (conn f M).hom a q'

/-- A global section of `Q` killed by the connecting morphism comes from `I`. -/
lemma exists_π_eq_of_conn_eq_zero (q : Γ(cokernel (Injective.ι M), ⊤))
    (hq : (conn f M).hom q = 0) :
    ∃ T : Γ(Injective.under M, ⊤), (cokernel.π (Injective.ι M)).app ⊤ T = q := by
  let F := DerivedSections.relativeGlobalSections f
  have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact M
  obtain ⟨s₀, hs₀⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (DerivedPlus.rightDerived_exact₃ F hS 0 1 rfl) ((F.rightDerivedZeroIsoSelf.inv.app _).hom q)
    hq
  refine ⟨(F.rightDerivedZeroIsoSelf.hom.app _).hom s₀, ?_⟩
  have e₁ := congrArg (fun k => k.hom s₀)
    (F.rightDerivedZeroIsoSelf.hom.naturality (cokernel.π (Injective.ι M)))
  have e₂ := congrArg (fun k => k.hom q) (F.rightDerivedZeroIsoSelf.inv_hom_id_app
    (cokernel (Injective.ι M)))
  exact e₁.symm.trans ((congrArg (F.rightDerivedZeroIsoSelf.hom.app _).hom hs₀).trans e₂)

/-- The connecting morphism is surjective, since `H¹(P, I) = 0`. -/
lemma conn_surjective (x : (DerivedSections.relativeCohomology f 1).obj M) :
    ∃ q : Γ(cokernel (Injective.ι M), ⊤), (conn f M).hom q = x := by
  let F := DerivedSections.relativeGlobalSections f
  have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact M
  have hδ : Epi (DerivedPlus.rightDerivedδ F hS 0 1 rfl) :=
    DerivedPlus.epi_rightDerivedδ_of_isZero F hS 0 1 rfl
      (F.isZero_rightDerived_obj_injective_succ 0 (Injective.under M))
  have : Epi (conn f M) := epi_comp' inferInstance hδ
  exact (ModuleCat.epi_iff_surjective _).1 this x

end Conn

section Scalar

/-- The image of `a : R` in the sections of `𝒪_P` over `W`. -/
noncomputable def sc (a : R) (W : P.Opens) : Γ(P, W) :=
  (P.presheaf.map (homOfLE le_top).op).hom ((DerivedSections.structureRingHom f).hom a)

lemma map_sc (a : R) {W W' : P.Opens} (h : W' ≤ W) :
    (P.presheaf.map (homOfLE h).op).hom (sc f a W) = sc f a W' := by
  rw [sc, sc, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma res_smul {N : P.Modules} {W W' : P.Opens} (h : W' ≤ W) (r : Γ(P, W)) (x : Γ(N, W)) :
    Cech.res (P := N.presheaf) h (r • x) =
      (P.presheaf.map (homOfLE h).op).hom r • Cech.res (P := N.presheaf) h x :=
  Scheme.Modules.map_smul N (homOfLE h) r x

lemma res_sc_smul (a : R) {N : P.Modules} {W W' : P.Opens} (h : W' ≤ W) (x : Γ(N, W)) :
    Cech.res (P := N.presheaf) h (sc f a W • x) = sc f a W' • Cech.res (P := N.presheaf) h x := by
  rw [res_smul, map_sc]

variable {ι : Type w} (V : ι → P.Opens)

/-- Multiplication of a Čech cochain of a module by the image of `a : R`. -/
noncomputable def smulC (a : R) {N : P.Modules} {p : ℕ} (c : Cech.C N.presheaf V p) :
    Cech.C N.presheaf V p :=
  fun σ => sc f a (Cech.inter V σ) • c σ

variable {V}

lemma d_smulC (a : R) {N : P.Modules} (p : ℕ) (c : Cech.C N.presheaf V p) :
    Cech.d _ V p (smulC f V a c) = smulC f V a (Cech.d _ V p c) := by
  funext τ
  rw [Cech.d_apply, smulC, Cech.d_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smulC, res_sc_smul, smul_comm]

lemma smulC_zero (a : R) {N : P.Modules} {p : ℕ} :
    smulC f V a (0 : Cech.C N.presheaf V p) = 0 := by
  funext σ
  exact smul_zero _

lemma map_smulC (a : R) {N N' : P.Modules} (φ : N ⟶ N') (p : ℕ) (c : Cech.C N.presheaf V p) :
    Cech.map V φ.mapPresheaf p (smulC f V a c) = smulC f V a (Cech.map V φ.mapPresheaf p c) := by
  funext σ
  exact Scheme.Modules.Hom.app_smul φ _ (c σ)

end Scalar

section Rep

variable [HasDerivedCategory.{w₁} P.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]
  (M : P.Modules) {ι : Type w} (V : ι → P.Opens)

/-- The Čech `1`-cochain `z` of `M` on `V` represents the class `x ∈ H¹(P, M)`. -/
def Rep (z : Cech.C M.presheaf V 1) (x : (DerivedSections.relativeCohomology f 1).obj M) :
    Prop :=
  ∃ (t : Cech.C (Injective.under M).presheaf V 0) (q : Γ(cokernel (Injective.ι M), ⊤)),
    Cech.d _ V 0 t = mapι M V 1 z ∧ (∀ σ, Cech.res le_top q = mapπ M V 0 t σ) ∧
      (conn f M).hom q = x

variable {f M V}

lemma rep_add {z z' : Cech.C M.presheaf V 1} {x x'} (h : Rep f M V z x) (h' : Rep f M V z' x') :
    Rep f M V (z + z') (x + x') := by
  obtain ⟨t, q, ht, hq, rfl⟩ := h
  obtain ⟨t', q', ht', hq', rfl⟩ := h'
  refine ⟨t + t', q + q', ?_, fun σ => ?_, conn_add f M q q'⟩
  · rw [map_add, map_add, ht, ht']
  · rw [map_add, hq, hq', map_add]
    rfl

lemma rep_smul (a : R) {z : Cech.C M.presheaf V 1} {x} (h : Rep f M V z x) :
    Rep f M V (smulC f V a z) (a • x) := by
  obtain ⟨t, q, ht, hq, rfl⟩ := h
  refine ⟨smulC f V a t, (DerivedSections.structureRingHom f).hom a • q, ?_, fun σ => ?_,
    conn_smul f M a q⟩
  · rw [d_smulC, ht, map_smulC]
  · rw [map_smulC, res_smul, smulC, ← hq σ]
    rfl

/-- Coboundaries represent `0`. -/
lemma rep_d (y : Cech.C M.presheaf V 0) : Rep f M V (Cech.d _ V 0 y) 0 := by
  refine ⟨mapι M V 0 y, 0, by rw [Cech.d_map], fun σ => ?_, conn_zero f M⟩
  rw [map_zero, mapπ_mapι]
  rfl

/-- A cocycle represents at most one class. -/
lemma rep_unique (hcov : ⊤ ≤ iSup V) {z : Cech.C M.presheaf V 1} {x x'}
    (h : Rep f M V z x) (h' : Rep f M V z x') : x = x' := by
  obtain ⟨t, q, ht, hq, rfl⟩ := h
  obtain ⟨t', q', ht', hq', rfl⟩ := h'
  have hd : Cech.d _ V 0 (t - t') = 0 := by rw [map_sub, ht, ht', sub_self]
  obtain ⟨T, hT⟩ : ∃ T : Γ(Injective.under M, ⊤), ∀ σ, Cech.res le_top T = (t - t') σ :=
    exists_top_of_d_zero ((PushforwardInjectiveAcyclic.toAbSheaf P).obj (Injective.under M))
      hcov hd
  have hcov' : (⊤ : P.Opens) ≤ ⨆ σ : Fin 1 → ι, Cech.inter V σ := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov hx)
    exact Opens.mem_iSup.2 ⟨fun _ => i, (Cech.inter_const_one i).ge hi⟩
  have hπ : (cokernel.π (Injective.ι M)).app ⊤ T = q - q' := by
    refine Cech.eq_of_locally ((PushforwardInjectiveAcyclic.toAbSheaf P).obj
      (cokernel (Injective.ι M))) (fun σ : Fin 1 → ι => Cech.inter V σ) (fun _ => le_top) hcov'
      fun σ => ?_
    have e : Cech.res (le_top : Cech.inter V σ ≤ ⊤) ((cokernel.π (Injective.ι M)).app ⊤ T) =
        Cech.res (P := (cokernel (Injective.ι M)).presheaf) (le_top : Cech.inter V σ ≤ ⊤)
          (q - q') := by
      rw [← app_res, hT σ, Pi.sub_apply, map_sub, map_sub, hq σ, hq' σ]
      rfl
    exact e
  have h0 := conn_π f M T
  rw [hπ, conn_sub] at h0
  exact sub_eq_zero.1 h0

lemma rep_eq_zero_of_d (hcov : ⊤ ≤ iSup V) {y : Cech.C M.presheaf V 0} {x}
    (h : Rep f M V (Cech.d _ V 0 y) x) : x = 0 :=
  rep_unique hcov h (rep_d y)

/-- Every cocycle on a finite family covering `P` represents a class. -/
lemma exists_rep [Finite ι] (hcov : ⊤ ≤ iSup V) {z : Cech.C M.presheaf V 1}
    (hz : Cech.d _ V 1 z = 0) : ∃ x, Rep f M V z x := by
  obtain ⟨t, ht⟩ := exactAt_injective M V 0 (mapι M V 1 z) (by rw [Cech.d_map, hz, map_zero])
  have hdt : Cech.d _ V 0 (mapπ M V 0 t) = 0 := by rw [Cech.d_map, ht, mapπ_mapι]
  obtain ⟨q, hq⟩ : ∃ q : Γ(cokernel (Injective.ι M), ⊤),
      ∀ σ, Cech.res le_top q = mapπ M V 0 t σ :=
    exists_top_of_d_zero ((PushforwardInjectiveAcyclic.toAbSheaf P).obj
      (cokernel (Injective.ι M))) hcov hdt
  exact ⟨(conn f M).hom q, t, q, ht, hq, rfl⟩

/-- If the members of `V` are affine, every class is represented by a cocycle. -/
lemma exists_cocycle_rep (hM : AffineVanishing.IsCechAcyclic M)
    (hV : ∀ σ : Fin 1 → ι, IsAffineOpen (Cech.inter V σ))
    (x : (DerivedSections.relativeCohomology f 1).obj M) :
    ∃ z : Cech.C M.presheaf V 1, Cech.d _ V 1 z = 0 ∧ Rep f M V z x := by
  obtain ⟨q, rfl⟩ := conn_surjective f M x
  obtain ⟨t, ht⟩ := exists_mapπ_eq hM hV (fun σ => Cech.res le_top q)
  obtain ⟨z, hz⟩ := exists_mapι_eq (Cech.d _ V 0 t) (by
    rw [← Cech.d_map, ht]
    exact d_zero_res_top (cokernel (Injective.ι M)).presheaf q)
  have hz' : mapι M V 1 z = Cech.d _ V 0 t := hz
  refine ⟨z, mapι_injective 2 ?_, t, q, hz'.symm, fun σ => (congrFun ht σ).symm, rfl⟩
  rw [← Cech.d_map, hz', Cech.d_d, map_zero]

end Rep

end Langlands.AlgebraicGeometry.Modules.CechTheta
