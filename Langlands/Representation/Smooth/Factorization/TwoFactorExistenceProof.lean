import Langlands.Representation.Smooth.Factorization.TwoFactorStatement
import Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Existence of two-factor decompositions

This module proves `Langlands.AdmissibleProductFactorizationStatement`.

The first factor is the span `U` of the `G₁`-orbit of a well-chosen fixed vector,
and the second factor is the space of `G₁`-intertwiners from `U` to the given
representation, with `G₂` acting by post-composition. Evaluation identifies the
external tensor of these factors with the given representation; injectivity uses
Jacobson density and Schur's lemma for the admissible irreducible factor `U`.
-/

namespace Langlands.TwoFactorExistence

open Representation
open scoped TensorProduct

universe uG uG₁ uG₂ uV uW uX

section Density

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Intertwiners commute with the action of the group algebra. -/
theorem intertwining_asAlgebraHom {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (r : MonoidAlgebra ℂ G) (v : V) :
    f (ρ.asAlgebraHom r v) = σ.asAlgebraHom r (f v) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, LinearMap.add_apply, hx, hy]
  | single g a => simp [asAlgebraHom_single, f.isIntertwining]

/-- Jacobson density for an irreducible representation whose endomorphisms are
scalars: every linear endomorphism agrees on a finite set with an element of the
group algebra. -/
theorem exists_algebra_eq (σ : Representation ℂ G W) [σ.IsIrreducible]
    (hS : ∀ f : σ.IntertwiningMap σ, ∃ c : ℂ, f = c • IntertwiningMap.id σ)
    (g : W →ₗ[ℂ] W) (s : Finset W) :
    ∃ r : MonoidAlgebra ℂ G, ∀ m ∈ s, g m = σ.asAlgebraHom r m := by
  classical
  let F : Module.End (Module.End (MonoidAlgebra ℂ G) σ.asModule) σ.asModule :=
    { toFun := fun m => σ.asModuleEquiv.symm (g (σ.asModuleEquiv m))
      map_add' := fun a b => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hS ((IntertwiningMap.equivLinearMapAsModule σ σ).symm φ)
        have hφ : ∀ x : σ.asModule, φ x = σ.asModuleEquiv.symm (c • σ.asModuleEquiv x) := by
          intro x
          exact congrArg (fun f : σ.IntertwiningMap σ => f (σ.asModuleEquiv x)) hc
        change σ.asModuleEquiv.symm (g (σ.asModuleEquiv (φ m))) =
          φ (σ.asModuleEquiv.symm (g (σ.asModuleEquiv m)))
        rw [hφ, hφ]
        simp }
  obtain ⟨r, hr⟩ := jacobson_density F (s.image σ.asModuleEquiv.symm)
  refine ⟨r, fun m hm => ?_⟩
  have h := hr (σ.asModuleEquiv.symm m) (Finset.mem_image_of_mem _ hm)
  have h2 := congrArg σ.asModuleEquiv h
  rw [asModuleEquiv_map_smul] at h2
  simpa [F] using h2

end Density

section Lattice

variable {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {σ : Representation ℂ H W}

theorem mem_bot_iff {v : W} : v ∈ (⊥ : Subrepresentation σ) ↔ v = 0 :=
  Submodule.mem_bot ℂ

theorem mem_top (v : W) : v ∈ (⊤ : Subrepresentation σ) :=
  Submodule.mem_top

theorem eq_bot_of_forall (P : Subrepresentation σ) (h : ∀ v ∈ P, v = 0) : P = ⊥ :=
  eq_bot_iff.mpr fun v hv => mem_bot_iff.mpr (h v hv)

theorem exists_ne_zero_of_ne_bot {P : Subrepresentation σ} (hP : P ≠ ⊥) : ∃ v ∈ P, v ≠ 0 := by
  by_contra h
  exact hP (eq_bot_of_forall P fun v hv => by_contra fun hv0 => h ⟨v, hv, hv0⟩)

theorem eq_top_of_forall (P : Subrepresentation σ) (h : ∀ v, v ∈ P) : P = ⊤ :=
  eq_top_iff.mpr fun v _ => h v

theorem mem_fixedVectors_iff {K : Subgroup H} {v : W} :
    v ∈ fixedVectors σ K ↔ ∀ k ∈ K, σ k v = v := by
  rw [fixedVectors, Representation.mem_invariants]
  exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.prop⟩

/-- The inclusion of a subrepresentation, as an intertwining map. -/
def subtypeHom (P : Subrepresentation σ) : P.toRepresentation.IntertwiningMap σ where
  toLinearMap := P.toSubmodule.subtype
  isIntertwining' _ := LinearMap.ext fun _ => rfl

@[simp]
theorem subtypeHom_apply (P : Subrepresentation σ) (v : P.toSubmodule) :
    subtypeHom P v = v := rfl

theorem isSmooth_toRepresentation [TopologicalSpace H] (h : IsSmooth σ)
    (P : Subrepresentation σ) : IsSmooth P.toRepresentation := by
  intro v
  obtain ⟨L, hL⟩ := h v
  exact ⟨L, mem_fixedVectors_iff.mpr fun k hk => Subtype.ext ((mem_fixedVectors_iff.mp hL) k hk)⟩

end Lattice

section Factors

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (G₁ × G₂) V)

/-- The subrepresentation of the first-factor restriction spanned by the orbit
of a vector. -/
def spanOrbit (y : V) : Subrepresentation (first ρ) where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G₁ => first ρ g y)
  apply_mem_toSubmodule h v hv := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      refine Submodule.subset_span ⟨h * g, ?_⟩
      change first ρ (h * g) y = first ρ h (first ρ g y)
      rw [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x z _ _ hx hz => simpa using Submodule.add_mem _ hx hz
    | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

theorem mem_spanOrbit_self (y : V) : y ∈ spanOrbit ρ y := by
  refine Submodule.subset_span ⟨1, ?_⟩
  change first ρ 1 y = y
  simp

theorem spanOrbit_le {y : V} {P : Subrepresentation (first ρ)} (hy : y ∈ P) :
    spanOrbit ρ y ≤ P := by
  intro x hx
  refine (Submodule.span_le.mpr ?_ : Submodule.span ℂ _ ≤ P.toSubmodule) hx
  rintro _ ⟨g, rfl⟩
  exact P.apply_mem_toSubmodule g hy

/-- Vectors fixed by a subgroup of the second factor form a subrepresentation of
the first-factor restriction. -/
noncomputable def secondFixed (K : Subgroup G₂) : Subrepresentation (first ρ) where
  toSubmodule := fixedVectors (second ρ) K
  apply_mem_toSubmodule g v hv := mem_fixedVectors_iff.mpr fun k hk => by
    rw [← first_second_comm, (mem_fixedVectors_iff.mp hv) k hk]

variable {ρ} (U : Subrepresentation (first ρ))

/-- The multiplicity space of `U`: first-factor intertwiners from `U` to the
given representation. -/
abbrev Mult := U.toRepresentation.IntertwiningMap (first ρ)

/-- The second factor acts on the multiplicity space by post-composition. -/
noncomputable def multRep : Representation ℂ G₂ (Mult U) where
  toFun g := IntertwiningMap.llcomp U.toRepresentation (first ρ) (first ρ) (secondOp ρ g)
  map_one' := by
    refine LinearMap.ext fun f => IntertwiningMap.ext (LinearMap.ext fun u => ?_)
    change second ρ 1 (f u) = f u
    simp
  map_mul' g h := by
    refine LinearMap.ext fun f => IntertwiningMap.ext (LinearMap.ext fun u => ?_)
    change second ρ (g * h) (f u) = second ρ g (second ρ h (f u))
    rw [map_mul, Module.End.mul_apply]

theorem multRep_apply (g : G₂) (f : Mult U) (u : U.toSubmodule) :
    multRep U g f u = second ρ g (f u) := rfl

/-- Evaluation of multiplicity intertwiners at a fixed vector of `U`. -/
def evalAt (u : U.toSubmodule) : Mult U →ₗ[ℂ] V where
  toFun f := f u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalAt_injective [U.toRepresentation.IsIrreducible] {u : U.toSubmodule} (hu : u ≠ 0) :
    Function.Injective (evalAt U u) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hf' : f u = 0 := hf
  rcases IsIrreducible.injective_or_eq_zero f with hinj | hz
  · exact absurd (hinj (hf'.trans (map_zero f).symm)) hu
  · exact hz

/-- Evaluation of multiplicity intertwiners on `U`. -/
noncomputable def eval : U.toSubmodule ⊗[ℂ] Mult U →ₗ[ℂ] V :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun u (f : Mult U) => f u)
    (fun u u' f => map_add f u u') (fun c u f => map_smul f c u)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl))

theorem eval_tmul (u : U.toSubmodule) (f : Mult U) : eval U (u ⊗ₜ f) = f u := by
  simp [eval]

/-- The external tensor representation of `U` and its multiplicity space. -/
noncomputable abbrev tensorRep : Representation ℂ (G₁ × G₂) (U.toSubmodule ⊗[ℂ] Mult U) :=
  Representation.tprod (U.toRepresentation.comp (MonoidHom.fst G₁ G₂))
    ((multRep U).comp (MonoidHom.snd G₁ G₂))

theorem eval_comm (g : G₁ × G₂) : eval U ∘ₗ tensorRep U g = ρ g ∘ₗ eval U := by
  refine TensorProduct.ext' fun u f => ?_
  simp only [LinearMap.comp_apply, Representation.tprod_apply, MonoidHom.coe_comp,
    Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, TensorProduct.map_tmul,
    eval_tmul, multRep_apply, IntertwiningMap.isIntertwining]
  exact first_second_apply ρ g (f u)

/-- Evaluation as an intertwining map. -/
noncomputable def evalHom : (tensorRep U).IntertwiningMap ρ where
  toLinearMap := eval U
  isIntertwining' := eval_comm U

theorem eval_surjective [ρ.IsIrreducible] (u : U.toSubmodule) (f : Mult U) (h : f u ≠ 0) :
    Function.Surjective (eval U) := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero (evalHom U) with hs | hz
  · exact hs
  · exfalso
    apply h
    have h0 := congrArg (fun F : (tensorRep U).IntertwiningMap ρ => F (u ⊗ₜ f)) hz
    change eval U (u ⊗ₜ f) = 0 at h0
    rwa [eval_tmul] at h0

theorem eval_injective [U.toRepresentation.IsIrreducible]
    (hS : ∀ f : U.toRepresentation.IntertwiningMap U.toRepresentation,
      ∃ c : ℂ, f = c • IntertwiningMap.id U.toRepresentation) :
    Function.Injective (eval U) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ U.toSubmodule
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hc : ∀ j u, c j u = 0 := by
    intro j u
    obtain ⟨r, hr⟩ := exists_algebra_eq U.toRepresentation hS
      ((b.coord j).smulRight u) (c.support.image b)
    have hterm : ∀ i ∈ c.support, (first ρ).asAlgebraHom r (eval U (b i ⊗ₜ c i)) =
        (b.coord j (b i)) • c i u := by
      intro i hi
      rw [eval_tmul, ← intertwining_asAlgebraHom, ← hr (b i) (Finset.mem_image_of_mem b hi),
        LinearMap.smulRight_apply, map_smul]
    have h1 := congrArg ((first ρ).asAlgebraHom r) ht
    simp only [map_finsuppSum, map_zero] at h1
    rw [Finsupp.sum, Finset.sum_congr rfl hterm, Finset.sum_eq_single j] at h1
    · simpa using h1
    · intro i _ hij
      simp [hij]
    · intro hj
      simp [Finsupp.notMem_support_iff.mp hj]
  have hc0 : c = 0 := Finsupp.ext fun j =>
    IntertwiningMap.ext (LinearMap.ext fun u => hc j u)
  simp [hc0]

end Factors

section Topology

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
variable [TopologicalSpace G₁] [TopologicalSpace G₂]
variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ (G₁ × G₂) V}

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
theorem continuous_inl' : Continuous (MonoidHom.inl G₁ G₂) :=
  continuous_id.prodMk continuous_const

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
theorem continuous_inr' : Continuous (MonoidHom.inr G₁ G₂) :=
  continuous_const.prodMk continuous_id

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
theorem isSmooth_first (h : IsSmooth ρ) : IsSmooth (first ρ) := by
  intro v
  obtain ⟨W, hW⟩ := h v
  refine ⟨W.comap (MonoidHom.inl G₁ G₂) continuous_inl', mem_fixedVectors_iff.mpr fun k hk => ?_⟩
  exact (mem_fixedVectors_iff.mp hW) (MonoidHom.inl G₁ G₂ k) hk

omit [IsTopologicalGroup G₂] in
/-- In an irreducible smooth representation of `G₁ × G₂` with a nonzero vector fixed
by a compact open subgroup `K` of `G₁`, every nonzero subrepresentation of the
first-factor restriction contains a nonzero `K`-fixed vector. -/
theorem exists_fixed_of_ne_bot [ρ.IsIrreducible] (hs : IsSmooth ρ) (K : OpenSubgroup G₁)
    (hK : IsCompact (K : Set G₁)) {x : V} (hx0 : x ≠ 0)
    (hx : x ∈ fixedVectors (first ρ) K.toSubgroup)
    {N : Subrepresentation (first ρ)} (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ n ∈ fixedVectors (first ρ) K.toSubgroup := by
  by_contra hcon
  have hs₁ := isSmooth_first hs
  let e := Compact.averageMap (first ρ) hs₁ K hK
  have hcomm : ∀ (g : G₂) (v : V), e (second ρ g v) = second ρ g (e v) := fun g v =>
    (LinearMap.congr_fun
      (Compact.averageMap_commute (first ρ) (first ρ) hs₁ hs₁ K hK (secondOp ρ g)) v).symm
  have hN0 : ∀ n ∈ N, e n = 0 := by
    intro n hn
    have hsN := isSmooth_toRepresentation hs₁ N
    have h : ((Compact.averageMap N.toRepresentation hsN K hK ⟨n, hn⟩ : N.toSubmodule) : V) =
        e n :=
      LinearMap.congr_fun
        (Compact.averageMap_commute N.toRepresentation (first ρ) hsN hs₁ K hK (subtypeHom N))
        ⟨n, hn⟩
    have hmem : e n ∈ N := by
      rw [← h]
      exact Subtype.prop _
    by_contra hne
    exact hcon ⟨_, hmem, hne, Compact.averageMap_mem_fixedVectors _ _ _ _ n⟩
  let Z : Subrepresentation ρ :=
    { toSubmodule := ⨅ g : G₁, LinearMap.ker (e ∘ₗ first ρ g)
      apply_mem_toSubmodule := by
        intro h v hv
        simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hv ⊢
        intro g
        rw [← first_second_apply ρ h, first_mul_apply, first_second_comm, hcomm, hv, map_zero] }
  have hNZ : ∀ n ∈ N, n ∈ Z := by
    intro n hn
    change n ∈ ⨅ g : G₁, LinearMap.ker (e ∘ₗ first ρ g)
    rw [Submodule.mem_iInf]
    intro g
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact hN0 _ (N.apply_mem_toSubmodule g hn)
  have hxZ : x ∉ Z := by
    intro h
    have h1 : x ∈ ⨅ g : G₁, LinearMap.ker (e ∘ₗ first ρ g) := h
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 1
    have hex : e x = x := Compact.averageMap_id _ _ _ _ x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, map_one, Module.End.one_apply, hex] at h2
    exact hx0 h2
  rcases IsSimpleOrder.eq_bot_or_eq_top Z with hZ | hZ
  · refine hN (eq_bot_of_forall N fun n hn => ?_)
    have h := hNZ n hn
    rw [hZ] at h
    exact mem_bot_iff.mp h
  · apply hxZ
    rw [hZ]
    exact mem_top x

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
/-- A first-factor subrepresentation fixed by an open subgroup of the second
factor is admissible. -/
theorem isAdmissible_of_le_secondFixed (ha : IsAdmissible ρ) (K₂ : OpenSubgroup G₂)
    (P : Subrepresentation (first ρ)) (hP : P ≤ secondFixed ρ K₂.toSubgroup) :
    IsAdmissible P.toRepresentation := by
  refine ⟨isSmooth_toRepresentation (isSmooth_first ha.1) P, fun L => ?_⟩
  have hmap : ∀ w : fixedVectors P.toRepresentation L.toSubgroup,
      ((w : P.toSubmodule) : V) ∈ fixedVectors ρ (L.prod K₂).toSubgroup := by
    intro w
    have hw₂ : ((w : P.toSubmodule) : V) ∈ fixedVectors (second ρ) K₂.toSubgroup :=
      hP (w : P.toSubmodule).2
    refine mem_fixedVectors_iff.mpr fun g hg => ?_
    rw [OpenSubgroup.toSubgroup_prod, Subgroup.mem_prod] at hg
    rw [← first_second_apply ρ g, (mem_fixedVectors_iff.mp hw₂) g.2 hg.2]
    exact congrArg Subtype.val ((mem_fixedVectors_iff.mp w.2) g.1 hg.1)
  have := ha.2 (L.prod K₂)
  let f : fixedVectors P.toRepresentation L.toSubgroup →ₗ[ℂ]
      fixedVectors ρ (L.prod K₂).toSubgroup :=
    LinearMap.codRestrict _
      (P.toSubmodule.subtype ∘ₗ (fixedVectors P.toRepresentation L.toSubgroup).subtype) hmap
  refine Module.Finite.of_injective f fun a b hab => ?_
  have h := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h)

variable (U : Subrepresentation (first ρ))

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
/-- The multiplicity space of an irreducible first-factor subrepresentation
containing a nonzero `K₁`-fixed vector is admissible. -/
theorem isAdmissible_multRep [U.toRepresentation.IsIrreducible] (ha : IsAdmissible ρ)
    {u : U.toSubmodule} (hu : u ≠ 0) (K₁ : OpenSubgroup G₁)
    (hu₁ : (u : V) ∈ fixedVectors (first ρ) K₁.toSubgroup) : IsAdmissible (multRep U) := by
  have hinj := evalAt_injective U hu
  refine ⟨fun f => ?_, fun L => ?_⟩
  · obtain ⟨W, hW⟩ := ha.1 (f u)
    refine ⟨W.comap (MonoidHom.inr G₁ G₂) continuous_inr',
      mem_fixedVectors_iff.mpr fun k hk => hinj ?_⟩
    change multRep U k f u = f u
    rw [multRep_apply]
    exact (mem_fixedVectors_iff.mp hW) (MonoidHom.inr G₁ G₂ k) hk
  · have hmap : ∀ f : fixedVectors (multRep U) L.toSubgroup,
        evalAt U u (f : Mult U) ∈ fixedVectors ρ (K₁.prod L).toSubgroup := by
      intro f
      refine mem_fixedVectors_iff.mpr fun g hg => ?_
      rw [OpenSubgroup.toSubgroup_prod, Subgroup.mem_prod] at hg
      change ρ g ((f : Mult U) u) = (f : Mult U) u
      rw [← second_first_apply ρ g]
      have h1 : first ρ g.1 ((f : Mult U) u) = (f : Mult U) u := by
        rw [← IntertwiningMap.isIntertwining]
        congr 1
        exact Subtype.ext ((mem_fixedVectors_iff.mp hu₁) g.1 hg.1)
      rw [h1, ← multRep_apply U]
      exact congrArg (fun F : Mult U => F u) ((mem_fixedVectors_iff.mp f.2) g.2 hg.2)
    have := ha.2 (K₁.prod L)
    let F : fixedVectors (multRep U) L.toSubgroup →ₗ[ℂ] fixedVectors ρ (K₁.prod L).toSubgroup :=
      LinearMap.codRestrict _ (evalAt U u ∘ₗ (fixedVectors (multRep U) L.toSubgroup).subtype) hmap
    refine Module.Finite.of_injective F fun a b hab => ?_
    have h := congrArg Subtype.val hab
    exact Subtype.ext (hinj h)

omit [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
/-- The multiplicity space of an irreducible first-factor subrepresentation with
scalar endomorphisms is irreducible. -/
theorem isIrreducible_multRep [ρ.IsIrreducible] [U.toRepresentation.IsIrreducible]
    (hS : ∀ f : U.toRepresentation.IntertwiningMap U.toRepresentation,
      ∃ c : ℂ, f = c • IntertwiningMap.id U.toRepresentation)
    {u : U.toSubmodule} (hu : u ≠ 0) : (multRep U).IsIrreducible := by
  have hinj := evalAt_injective U hu
  have hι : subtypeHom U ≠ 0 := by
    intro h
    apply hu
    apply Subtype.ext
    have h1 := congrArg (fun F : Mult U => F u) h
    simpa using h1
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hι ?_⟩, eq_bot_or_eq_top := fun N => ?_ }
  · have h1 := mem_top (σ := multRep U) (subtypeHom U)
    rw [← h] at h1
    exact mem_bot_iff.mp h1
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨n, hn, hn0⟩ := exists_ne_zero_of_ne_bot hN
  let T : U.toSubmodule ⊗[ℂ] N.toSubmodule →ₗ[ℂ] U.toSubmodule ⊗[ℂ] Mult U :=
    TensorProduct.map LinearMap.id N.toSubmodule.subtype
  have hstab : ∀ (g : G₁ × G₂) (t : U.toSubmodule ⊗[ℂ] N.toSubmodule),
      ρ g (eval U (T t)) ∈ LinearMap.range (eval U ∘ₗ T) := by
    intro g t
    induction t with
    | tmul v m =>
      refine ⟨U.toRepresentation g.1 v ⊗ₜ
        ⟨multRep U g.2 (m : Mult U), N.apply_mem_toSubmodule g.2 m.2⟩, ?_⟩
      simp only [T, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.coe_subtype, eval_tmul, multRep_apply]
      rw [IntertwiningMap.isIntertwining, second_first_apply]
    | add a b ha hb =>
      rw [map_add, map_add, map_add]
      exact Submodule.add_mem _ ha hb
  let R : Subrepresentation ρ :=
    { toSubmodule := LinearMap.range (eval U ∘ₗ T)
      apply_mem_toSubmodule := by
        rintro g _ ⟨t, rfl⟩
        exact hstab g t }
  have hR : R ≠ ⊥ := by
    intro h
    have h1 : (n : Mult U) u ∈ R := ⟨u ⊗ₜ ⟨n, hn⟩, by simp [T, eval_tmul]⟩
    rw [h] at h1
    apply hn0
    apply hinj
    rw [map_zero]
    exact mem_bot_iff.mp h1
  have hRtop : R = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top R).resolve_left hR
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hu
  let Φ : U.toSubmodule ⊗[ℂ] Mult U →ₗ[ℂ] Mult U :=
    (TensorProduct.lid ℂ (Mult U)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hΦ : ∀ s, Φ (T s) ∈ N.toSubmodule := by
    intro s
    induction s with
    | tmul v m =>
      simp only [Φ, T, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.coe_subtype, LinearEquiv.coe_coe, TensorProduct.lid_tmul]
      exact N.toSubmodule.smul_mem _ m.2
    | add a b ha hb =>
      rw [map_add, map_add]
      exact N.toSubmodule.add_mem ha hb
  refine eq_top_of_forall N fun f => ?_
  have hfR : f u ∈ R := by
    rw [hRtop]
    exact mem_top _
  obtain ⟨t, ht⟩ := LinearMap.mem_range.mp (hfR : f u ∈ LinearMap.range (eval U ∘ₗ T))
  have ht' : T t = u ⊗ₜ f := by
    apply eval_injective U hS
    rw [eval_tmul, ← ht, LinearMap.comp_apply]
  have h1 := hΦ t
  rw [ht'] at h1
  have h2 : Φ (u ⊗ₜ f) = f := by
    simp [Φ, hφ]
  rw [h2] at h1
  exact h1

omit [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
/-- A cyclic vector that is cyclic for every nonzero vector of its orbit span
generates an irreducible first-factor subrepresentation. -/
theorem isIrreducible_spanOrbit {y : V} (hy : y ≠ 0)
    (hcyc : ∀ u ∈ spanOrbit ρ y, u ≠ 0 → y ∈ spanOrbit ρ u) :
    (spanOrbit ρ y).toRepresentation.IsIrreducible := by
  have key : ∀ P : Subrepresentation (spanOrbit ρ y).toRepresentation, P ≠ ⊥ →
      ∀ w : (spanOrbit ρ y).toSubmodule, w ∈ P := by
    intro P hP w
    obtain ⟨p, hp, hp0⟩ := exists_ne_zero_of_ne_bot hP
    let Q : Subrepresentation (first ρ) :=
      { toSubmodule := P.toSubmodule.map (spanOrbit ρ y).toSubmodule.subtype
        apply_mem_toSubmodule := by
          rintro g _ ⟨v, hv, rfl⟩
          exact ⟨(spanOrbit ρ y).toRepresentation g v, P.apply_mem_toSubmodule g hv, rfl⟩ }
    have hpQ : (p : V) ∈ Q := ⟨p, hp, rfl⟩
    have hp0' : (p : V) ≠ 0 := fun h => hp0 (Subtype.ext h)
    have hyQ : y ∈ Q := spanOrbit_le ρ hpQ (hcyc p p.2 hp0')
    have hwQ : (w : V) ∈ P.toSubmodule.map (spanOrbit ρ y).toSubmodule.subtype :=
      spanOrbit_le ρ hyQ w.2
    obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.mp hwQ
    have hvw' : v = w := Subtype.ext hvw
    rw [← hvw']
    exact hv
  have hy' : (⟨y, mem_spanOrbit_self ρ y⟩ : (spanOrbit ρ y).toSubmodule) ≠ 0 :=
    fun h => hy (congrArg Subtype.val h)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hy' ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
  · have h1 := mem_top (σ := (spanOrbit ρ y).toRepresentation) ⟨y, mem_spanOrbit_self ρ y⟩
    rw [← h] at h1
    exact mem_bot_iff.mp h1
  · by_cases hP : P = ⊥
    · exact Or.inl hP
    · exact Or.inr (eq_top_of_forall P (key P hP))

omit [IsTopologicalGroup G₂] in
/-- Choice of compact open `K₁`, open `K₂` and a nonzero jointly fixed vector whose
first-factor orbit span is generated by each of its nonzero vectors. The vector
minimizes the dimension of the `K₁ × K₂`-fixed part of its orbit span. -/
theorem exists_cyclic [T2Space G₁] [LocallyCompactSpace G₁] [TotallyDisconnectedSpace G₁]
    [ρ.IsIrreducible] (ha : IsAdmissible ρ) :
    ∃ (K₁ : OpenSubgroup G₁) (K₂ : OpenSubgroup G₂) (y : V), IsCompact (K₁ : Set G₁) ∧
      y ≠ 0 ∧ y ∈ fixedVectors (first ρ) K₁.toSubgroup ∧
      y ∈ fixedVectors (second ρ) K₂.toSubgroup ∧
      ∀ u ∈ spanOrbit ρ y, u ≠ 0 → y ∈ spanOrbit ρ u := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (G₁ × G₂)) ρ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨W, hW⟩ := ha.1 x
  obtain ⟨K₁, hK₁W, hK₁, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G₁ ∅
    (W.comap (MonoidHom.inl G₁ G₂) continuous_inl')
  let K₂ := W.comap (MonoidHom.inr G₁ G₂) continuous_inr'
  let M : Submodule ℂ V :=
    fixedVectors (first ρ) K₁.toSubgroup ⊓ fixedVectors (second ρ) K₂.toSubgroup
  have hMle : M ≤ fixedVectors ρ (K₁.prod K₂).toSubgroup := by
    intro v hv
    obtain ⟨h₁, h₂⟩ := Submodule.mem_inf.mp hv
    refine mem_fixedVectors_iff.mpr fun g hg => ?_
    rw [OpenSubgroup.toSubgroup_prod, Subgroup.mem_prod] at hg
    rw [← first_second_apply ρ g, (mem_fixedVectors_iff.mp h₂) g.2 hg.2,
      (mem_fixedVectors_iff.mp h₁) g.1 hg.1]
  have : FiniteDimensional ℂ (fixedVectors ρ (K₁.prod K₂).toSubgroup) := ha.2 (K₁.prod K₂)
  have : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMle
  have hxM : x ∈ M := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact mem_fixedVectors_iff.mpr fun k hk =>
        (mem_fixedVectors_iff.mp hW) (MonoidHom.inl G₁ G₂ k) (hK₁W hk)
    · exact mem_fixedVectors_iff.mpr fun k hk =>
        (mem_fixedVectors_iff.mp hW) (MonoidHom.inr G₁ G₂ k) hk
  let S : V → Submodule ℂ V := fun z => (spanOrbit ρ z).toSubmodule ⊓ M
  have hSfin : ∀ z, FiniteDimensional ℂ (S z) := fun z =>
    Submodule.finiteDimensional_of_le inf_le_right
  have hex : ∃ d, ∃ z ∈ M, z ≠ 0 ∧ Module.finrank ℂ (S z) = d := ⟨_, x, hxM, hx, rfl⟩
  obtain ⟨y, hyM, hy0, hyd⟩ := Nat.find_spec hex
  have hmin : ∀ z ∈ M, z ≠ 0 → Module.finrank ℂ (S y) ≤ Module.finrank ℂ (S z) := by
    intro z hz hz0
    rw [hyd]
    exact Nat.find_min' hex ⟨z, hz, hz0, rfl⟩
  obtain ⟨hy₁, hy₂⟩ := Submodule.mem_inf.mp hyM
  refine ⟨K₁, K₂, y, hK₁, hy0, hy₁, hy₂, fun u hu hu0 => ?_⟩
  have hN : spanOrbit ρ u ≠ ⊥ := by
    intro h
    have h1 := mem_spanOrbit_self ρ u
    rw [h] at h1
    exact hu0 (mem_bot_iff.mp h1)
  obtain ⟨n, hn, hn0, hn₁⟩ := exists_fixed_of_ne_bot ha.1 K₁ hK₁ hy0 hy₁ hN
  have hny : n ∈ spanOrbit ρ y := spanOrbit_le ρ hu hn
  have hn₂ : n ∈ fixedVectors (second ρ) K₂.toSubgroup :=
    spanOrbit_le ρ (P := secondFixed ρ K₂.toSubgroup) hy₂ hny
  have hle : S n ≤ S y := inf_le_inf_right M fun v hv => spanOrbit_le ρ hny hv
  have := hSfin y
  have heq : S n = S y :=
    Submodule.eq_of_le_of_finrank_le hle (hmin n (Submodule.mem_inf.mpr ⟨hn₁, hn₂⟩) hn0)
  have hyS : y ∈ S y := Submodule.mem_inf.mpr ⟨mem_spanOrbit_self ρ y, hyM⟩
  rw [← heq] at hyS
  exact spanOrbit_le ρ hn (Submodule.mem_inf.mp hyS).1

end Topology

end Langlands.TwoFactorExistence

namespace Langlands

open Representation TwoFactorExistence

universe uG₁ uG₂ uV

/-- Flath's two-factor existence theorem: every admissible irreducible smooth complex
representation of a product of two locally profinite groups is an external tensor
product of admissible irreducible representations of the factors. -/
theorem admissibleProductFactorization :
    AdmissibleProductFactorizationStatement.{uG₁, uG₂, uV} := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ V _ _ ρ ha hi
  have := hi
  obtain ⟨K₁, K₂, y, hK₁, hy0, hy₁, hy₂, hcyc⟩ := exists_cyclic ha
  let U := spanOrbit ρ y
  let u : U.toSubmodule := ⟨y, mem_spanOrbit_self ρ y⟩
  have hu : u ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hUi : U.toRepresentation.IsIrreducible := isIrreducible_spanOrbit hy0 hcyc
  have hUa : IsAdmissible U.toRepresentation :=
    isAdmissible_of_le_secondFixed ha K₂ U
      (spanOrbit_le ρ (P := secondFixed ρ K₂.toSubgroup) hy₂)
  have hS : ∀ f : U.toRepresentation.IntertwiningMap U.toRepresentation,
      ∃ c : ℂ, f = c • IntertwiningMap.id U.toRepresentation :=
    fun f => (admissibleSchur_scalarEndomorphism U.toRepresentation hUa hUi f).exists
  have hsurj : Function.Surjective (eval U) :=
    eval_surjective U u (subtypeHom U) (show (subtypeHom U) u ≠ 0 from hy0)
  refine ⟨ModuleCat.of ℂ U.toSubmodule, ModuleCat.of ℂ (Mult U), U.toRepresentation,
    multRep U, hUa, hUi, isAdmissible_multRep U ha hu K₁ hy₁, isIrreducible_multRep U hS hu,
    ⟨?_⟩⟩
  exact (IntertwiningMap.ofBijective (evalHom U) ⟨eval_injective U hS, hsurj⟩).symm

end Langlands
