import Langlands.Representation.Smooth.CentralOperatorExpansionStatement
import Langlands.Representation.Smooth.IntertwinerFiniteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

namespace Langlands

universe uG uA uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [IsTopologicalGroup G] [TopologicalSpace A] [IsTopologicalGroup A] in
/-- The span of the actual central action is finite dimensional. -/
theorem centralActionSpan_finite (ρ : Representation ℂ G V)
    (c : A →* Subgroup.center G) (hρ : IsAdmissible ρ)
    (hfin : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule) :
    Module.Finite ℂ (Submodule.span ℂ (Set.range fun a : A => ρ (c a : G))) := by
  let := finite_intertwiningMap_of_finiteType ρ ρ hρ.1 hfin hρ
  let F := Representation.IntertwiningMap.toLinearMapl (ρ := ρ) (σ := ρ)
  have hle : Submodule.span ℂ (Set.range fun a : A => ρ (c a : G)) ≤ F.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨Representation.IntertwiningMap.centralMul ρ (c a : G) (c a).property, rfl⟩
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

omit [IsTopologicalGroup A] in
/-- Smooth finite generation makes the entire central action locally constant. -/
theorem centralAction_isLocallyConstant (ρ : Representation ℂ G V)
    (c : A →* Subgroup.center G) (hc : Continuous c) (hρ : IsSmooth ρ)
    (hfin : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule) :
    IsLocallyConstant (fun a : A => ρ (c a : G)) := by
  classical
  let := hfin
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  choose K hK using fun i => hρ (ρ.asModuleEquiv (v i))
  let F (a : A) := Representation.IntertwiningMap.centralMul ρ (c a : G) (c a).property
  apply (IsLocallyConstant.iff_exists_open _).2
  intro a
  refine ⟨{b | ∀ i, (c a : G)⁻¹ * (c b : G) ∈ K i}, ?_, ?_, ?_⟩
  · have hopen : IsOpen (⋂ i, {b : A | (c a : G)⁻¹ * (c b : G) ∈ K i}) :=
      isOpen_iInter_of_finite fun i =>
      (K i).isOpen.preimage (continuous_const.mul (continuous_subtype_val.comp hc))
    convert hopen using 1
    ext b
    simp
  · intro i
    simp
  · intro b hb
    have hF : F b = F a := by
      apply (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ).injective
      apply LinearMap.ext_on_range hv
      intro i
      change ρ (c b : G) (ρ.asModuleEquiv (v i)) = ρ (c a : G) (ρ.asModuleEquiv (v i))
      calc
        ρ (c b : G) (ρ.asModuleEquiv (v i)) = ρ (c a : G) (ρ ((c a : G)⁻¹ * (c b : G)) (ρ.asModuleEquiv (v i))) := by
          rw [← Module.End.mul_apply, ← map_mul]
          simp
        _ = ρ (c a : G) (ρ.asModuleEquiv (v i)) := congrArg (ρ (c a : G)) (hK i ⟨_, hb i⟩)
    exact congrArg Representation.IntertwiningMap.toLinearMap hF

/-- The complete uniform expansion, before evaluation on any vector. -/
theorem centralOperatorExpansion : CentralOperatorExpansionStatement.{uG,uA,uV} := by
  classical
  intro G _ _ _ A _ _ _ V _ _ ρ c hc hρ hfin
  let S := Submodule.span ℂ (Set.range fun a : A => ρ (c a : G))
  let s (a : A) : S := ⟨ρ (c a : G), Submodule.subset_span ⟨a, rfl⟩⟩
  have hspan : Submodule.span ℂ (Set.range s) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S _).mpr rfl
  let : Module.Finite ℂ S := centralActionSpan_finite ρ c hρ hfin
  let B := Module.finBasis ℂ S
  let χ (i : Fin (Module.finrank ℂ S)) (a : A) : ℂ := B.coord i (s a)
  have hχ : Function.Injective χ := by
    intro i j hij
    apply B.linearIndependent_coord.injective
    apply LinearMap.ext_on_range hspan
    intro a
    exact congrFun hij a
  have hs : IsLocallyConstant s := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro a
    exact ((centralAction_isLocallyConstant ρ c hc hρ.1 hfin).eventually_eq a).mono
      fun b hb => Subtype.ext hb
  have hcont (i : Fin (Module.finrank ℂ S)) : Continuous (χ i) :=
    (hs.comp (B.coord i)).continuous
  have hmul (b : A) (x : Module.End ℂ V) (hx : x ∈ S) : ρ (c b : G) * x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact Submodule.subset_span ⟨b * a, by simp [map_mul]⟩
    | zero => simp
    | add x y hx hy h₁ h₂ => simpa [mul_add] using S.add_mem h₁ h₂
    | smul r x hx h => simpa [mul_smul_comm] using S.smul_mem r h
  let L (b : A) : S →ₗ[ℂ] S :=
    { toFun x := ⟨ρ (c b : G) * x.val, hmul b x.val x.property⟩
      map_add' x y := by ext; simp [mul_add]
      map_smul' r x := by ext; simp }
  let E : (S →ₗ[ℂ] ℂ) →ₗ[ℂ] (A → ℂ) :=
    { toFun f a := f (s a)
      map_add' f g := rfl
      map_smul' r f := rfl }
  have hfinite (i : Fin (Module.finrank ℂ S)) :
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : A => fun a : A => χ i (b * a))) := by
    have hle : Submodule.span ℂ (Set.range fun b : A => fun a : A => χ i (b * a)) ≤
        E.range := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      refine ⟨(B.coord i).comp (L b), ?_⟩
      funext a
      change B.coord i (L b (s a)) = B.coord i (s (b * a))
      congr 1
      apply Subtype.ext
      simp [L, s, map_mul]
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  let T : (A → ℂ) → Module.End ℂ V :=
    Function.extend χ (fun i => (B i : Module.End ℂ V)) (fun _ => 0)
  have hT (i : Fin (Module.finrank ℂ S)) : T (χ i) = (B i : Module.End ℂ V) :=
    hχ.extend_apply _ _ i
  refine ⟨Finset.univ.image χ, T, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨hcont i, hfinite i⟩
  · intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    rw [hT]
    exact (B i).property
  · intro a
    rw [Finset.sum_image (fun i _ j _ hij => hχ hij)]
    simp_rw [hT]
    simpa only [χ, Module.Basis.coord_apply, Submodule.coe_sum, Submodule.coe_smul] using
      (congrArg Subtype.val (B.sum_repr (s a))).symm

end Langlands
