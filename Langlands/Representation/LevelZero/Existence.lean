import Langlands.Representation.LevelZero.Admissible
import Langlands.Representation.FiniteGeneralLinear.CuspidalExistence
import Langlands.Representation.Aubert.General.JacquetCommonConstituent
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.OrbitSpan

/-!
# An irreducible supercuspidal representation of `GL_{m+1}(F)` from a cuspidal type of level zero

Let `σ` be an irreducible cuspidal representation of `GL_{m+1}(k)` and `Λ` its inflation to
`J = ϖ^ℤ GL_{m+1}(𝒪)`. The subrepresentation of the smooth induced representation spanned by
the translates of one function supported on `J` is finitely generated, admissible, and every
vector of it is killed in the Jacquet coinvariants of every conjugate of the unipotent radical
of every proper block parabolic. An irreducible quotient of it is therefore an irreducible
admissible representation with vanishing Jacquet coinvariants.
-/

noncomputable section

open Filter Topology
open scoped MonoidAlgebra

namespace Langlands.LevelZero

open GeneralLinear ValuativeRel Langlands.Induction

universe u uG uV

section Generic

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The subrepresentation spanned by the orbit of a vector. -/
def orbitSpan (ρ : Representation ℂ G V) (x : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  apply_mem_toSubmodule := by
    intro g w hw
    have hle : Submodule.span ℂ (Set.range fun h : G => ρ h x) ≤
        (Submodule.span ℂ (Set.range fun h : G => ρ h x)).comap (ρ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
    exact hle hw

theorem mem_orbitSpan_self (ρ : Representation ℂ G V) (x : V) : x ∈ orbitSpan ρ x :=
  Submodule.subset_span ⟨1, by simp⟩

/-- A representation spanned over `ℂ` by one orbit is cyclic over the group algebra. -/
theorem moduleFinite_asModule_of_span_orbit (ρ : Representation ℂ G V) (v : V)
    (hv : Submodule.span ℂ (Set.range fun g : G => ρ g v) = ⊤) :
    Module.Finite ℂ[G] ρ.asModule := by
  classical
  refine ⟨⟨{ρ.asModuleEquiv.symm v}, ?_⟩⟩
  rw [Finset.coe_singleton, eq_top_iff]
  intro w _
  set N := Submodule.span ℂ[G] ({ρ.asModuleEquiv.symm v} : Set ρ.asModule)
  have hsm : ∀ (g : G) (c : ℂ) (y : V), ρ.asModuleEquiv.symm (c • ρ g y) =
      MonoidAlgebra.single g c • ρ.asModuleEquiv.symm y := by
    intro g c y
    rw [Representation.single_smul]
    rfl
  have key : ∀ u ∈ Submodule.span ℂ (Set.range fun g : G => ρ g v),
      ρ.asModuleEquiv.symm u ∈ N := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have := hsm g 1 v
      rw [one_smul] at this
      rw [this]
      exact N.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
    | zero => simp
    | add x y _ _ hx hy => simpa using N.add_mem hx hy
    | smul c x _ hx =>
      have := hsm 1 c x
      rw [map_one, Module.End.one_apply] at this
      rw [this]
      exact N.smul_mem _ hx
  have hw : ρ.asModuleEquiv w ∈ Submodule.span ℂ (Set.range fun g : G => ρ g v) :=
    hv ▸ Submodule.mem_top
  simpa using key _ hw

end Generic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Every open subgroup of `GL_n(F)` contains a compact open subgroup. -/
theorem compactOpen_cofinal (n : ℕ) (H : OpenSubgroup (GeneralLinear n F)) :
    ∃ K : OpenSubgroup (GeneralLinear n F), IsCompact (K : Set (GeneralLinear n F)) ∧ K ≤ H := by
  obtain ⟨K, hK, hKH⟩ := LocalFieldTopology.generalLinear_compactOpen F n
    (H : Set (GeneralLinear n F)) (H.isOpen.mem_nhds H.one_mem)
  exact ⟨K, hK, fun x hx => hKH hx⟩

variable (F) in
/-- **Existence at level zero.** `GL_{m+1}(F)` has an irreducible admissible smooth
representation whose Jacquet coinvariants vanish for every conjugate of the unipotent radical
of every proper standard block parabolic. -/
theorem exists_irreducible_supercuspidal_smoothRep (m : ℕ) :
    ∃ τ : SmoothRep.{0, u, u} ℂ (GeneralLinear (m + 1) F),
      τ.IsIrreducible ∧ τ.IsAdmissible ∧
        ∀ B : BlockShape (m + 1), B.parabolic F ≠ ⊤ → ∀ g : GeneralLinear (m + 1) F,
          Subsingleton (Jacquet.Coinvariants τ.representation (B.conjugateUnipotent g)) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F
  obtain ⟨V₀, hirr, hcusp⟩ := FiniteGeneralLinear.exists_irreducible_cuspidal_fdRep
    (k := IsLocalRing.ResidueField (integers F)) (Nat.succ_pos m)
  obtain ⟨L, hLK, hLred⟩ := exists_openSubgroup_reduction_trivial (F := F) m
  let E : SmoothRep.{0, u, u} ℂ (GeneralLinear (m + 1) F) :=
    SmoothRep.of (smoothInduced (inducingSubgroup m ϖ) (inducingRep m hϖ V₀.ρ))
      (smoothInduced_smooth _ _)
  have hEadm : E.IsAdmissible := smoothInduced_isAdmissible hϖ V₀.ρ hcusp
  obtain ⟨v₀, hv₀⟩ : ∃ v : V₀, v ≠ 0 := by
    by_contra! h
    apply (bot_ne_top : (⊥ : Subrepresentation V₀.ρ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext w
    change w ∈ (⊥ : Submodule ℂ V₀) ↔ w ∈ (⊤ : Submodule ℂ V₀)
    simp [h w]
  let x₀ : E := levelZeroIndicator hϖ V₀.ρ L hLK hLred v₀
  have hx₀ : x₀ ≠ 0 := by
    intro h
    apply hv₀
    have h1 := congrArg (fun f : SmoothFunctions (inducingSubgroup m ϖ)
      (inducingRep m hϖ V₀.ρ) => eval _ _ f 1) h
    rw [eval_zero] at h1
    rw [← h1]
    exact (indicator_one_eval (inducingSubgroup m ϖ) (inducingRep m hϖ V₀.ρ) L
      (openSubgroup_le_inducingSubgroup L hLK) (inducingRep_openSubgroup hϖ V₀.ρ L hLK hLred)
      v₀).symm
  let T := orbitSpan E.representation x₀
  let A := SmoothRep.subrepresentation E T
  let a₀ : A := ⟨x₀, mem_orbitSpan_self _ _⟩
  let ι := SmoothRep.hom (SmoothRep.subtype E T)
  have hι : Function.Injective ι := SmoothRep.subtype_injective E T
  have hspanA : Submodule.span ℂ (Set.range fun g => A.representation g a₀) = ⊤ := by
    have himage : Submodule.map ι.toLinearMap
        (Submodule.span ℂ (Set.range fun g => A.representation g a₀)) = T.toSubmodule := by
      rw [Submodule.map_span]
      change _ = Submodule.span ℂ (Set.range fun g => E.representation g x₀)
      congr 1
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨_, ⟨g, rfl⟩, rfl⟩
    rw [eq_top_iff]
    intro y _
    have hy : ι.toLinearMap y ∈ T.toSubmodule := y.2
    rw [← himage] at hy
    obtain ⟨b, hb, hbeq⟩ := hy
    rwa [← hι hbeq]
  have hfin : Module.Finite ℂ[GeneralLinear (m + 1) F] A.representation.asModule :=
    moduleFinite_asModule_of_span_orbit _ a₀ hspanA
  have hA : Nontrivial A := ⟨⟨a₀, 0, fun h => hx₀ (congrArg Subtype.val h)⟩⟩
  obtain ⟨τ, hτ, q, hq⟩ :=
    Aubert.General.JacquetCommonConstituent.exists_irreducible_quotient_of_moduleFinite A hA hfin
  refine ⟨τ, hτ, ?_, ?_⟩
  · have hAadm : A.IsAdmissible :=
      isAdmissible_of_injective (SmoothRep.hom (SmoothRep.subtype E T))
        (SmoothRep.subtype_injective E T) hEadm
    exact Unramified.SphericalExistence.isAdmissible_of_surjective (compactOpen_cofinal (m + 1))
      (SmoothRep.hom q) hq hAadm
  · intro B hB g
    set w₀ := SmoothRep.hom q a₀
    have hw₀ : w₀ ≠ 0 := by
      intro h0
      have hall : ∀ a : A, SmoothRep.hom q a = 0 := by
        intro a
        have ha : a ∈ Submodule.span ℂ (Set.range fun g => A.representation g a₀) :=
          hspanA ▸ Submodule.mem_top
        have hle : Submodule.span ℂ (Set.range fun g => A.representation g a₀) ≤
            LinearMap.ker (SmoothRep.hom q).toLinearMap := by
          rw [Submodule.span_le]
          rintro _ ⟨h, rfl⟩
          change SmoothRep.hom q (A.representation h a₀) = 0
          rw [Representation.IntertwiningMap.isIntertwining]
          change τ.representation h w₀ = 0
          rw [h0, map_zero]
        exact hle ha
      have hτnt : Nontrivial τ :=
        IsSimpleModule.nontrivial ℂ[GeneralLinear (m + 1) F] τ.representation.asModule
      obtain ⟨t, ht⟩ := exists_ne (0 : τ)
      obtain ⟨a, rfl⟩ := hq t
      exact ht (hall a)
    apply coinvariants_subsingleton_of_span τ.representation _
      (Set.range fun h => τ.representation h w₀) (span_range_orbit_eq_top hτ hw₀)
    rintro _ ⟨h, rfl⟩
    obtain ⟨ι, _, _, c, hc⟩ := exists_sum_translate_eq_zero hϖ V₀.ρ hcusp L hLK hLred B hB g h v₀
    apply mem_relations_of_sum_eq_zero τ.representation _ c
    have hsumA : ∑ i, A.representation (c i) (A.representation h a₀) = 0 := by
      apply hι
      rw [map_sum, map_zero]
      exact hc
    calc ∑ i, τ.representation (c i) (τ.representation h w₀)
        = SmoothRep.hom q (∑ i, A.representation (c i) (A.representation h a₀)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Representation.IntertwiningMap.isIntertwining,
            Representation.IntertwiningMap.isIntertwining]
      _ = 0 := by rw [hsumA, map_zero]

end Langlands.LevelZero
