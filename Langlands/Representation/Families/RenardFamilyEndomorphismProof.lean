import Langlands.Representation.Families.RenardFamilyEndomorphismStatement
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.Topology.LocallyProfiniteProof
import Langlands.GroupScheme.KostantRosenlicht.Points
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Proof of Renard VI.8.6: endomorphisms of a family with irreducible fibers

We prove `EndomorphismScalarStatement`. The route avoids local freeness. Compact
averaging makes each `V^K` a direct summand of `V`, hence finite projective. Linear
forms on `V` therefore separate vectors, and the ideal `I` of values `ℓ x` of linear
forms satisfies `I • V = V`. Schur's lemma at the points of `Ξ` and the
Nullstellensatz give `ℓ x • φ m = ℓ (φ x) • m`. Nakayama's lemma gives `e ∈ I` acting
as the identity on `V`, and writing `e = ∑ cⱼ ℓⱼ xⱼ` gives `b = ∑ cⱼ ℓⱼ (φ xⱼ)`.
-/

open TensorProduct Langlands.Topology

namespace Langlands.Renard.AlgebraicFamily

universe uB uG uV

section Helpers

variable {B : Type uB} [CommRing B] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module B V]
  (ρ : Representation B G V)

/-- In a locally profinite group, every smooth vector is fixed by a compact open
subgroup. -/
theorem exists_compact_mem_fixedVectors (hG : IsLocallyProfinite G) (hρ : IsSmooth ρ)
    (v : V) : ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      v ∈ fixedVectors ρ K.toSubgroup := by
  obtain ⟨L, hL⟩ := hρ v
  obtain ⟨K, hKc, hKL⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig G).mp hG).2 L L.mem_nhds_one
  exact ⟨K, hKc, fun k => hL ⟨k.val, hKL k.property⟩⟩

variable [Algebra ℂ B]

/-- Compact averaging gives a `B`-linear retraction of `V` onto `V^K`. -/
theorem exists_fixedVectors_retraction (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    ∃ r : V →ₗ[B] fixedVectors ρ K.toSubgroup,
      r ∘ₗ (fixedVectors ρ K.toSubgroup).subtype = LinearMap.id := by
  let : Module ℂ V := Module.compHom V (algebraMap ℂ B)
  have : IsScalarTower ℂ B V := IsScalarTower.of_compHom ℂ B V
  let ρc := Jacquet.CoefficientRestriction.complexRepresentation ρ
  have hρc : IsSmooth ρc := hρ
  let avg := Compact.averageMap ρc hρc K hK
  have hsmul : ∀ (b : B) (v : V), avg (b • v) = b • avg v := by
    intro b v
    let f : ρc.IntertwiningMap ρc :=
      { toLinearMap := (b • LinearMap.id : V →ₗ[B] V).restrictScalars ℂ
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro w
          exact ((ρ g).map_smul b w).symm }
    exact (LinearMap.congr_fun (Compact.averageMap_commute ρc ρc hρc hρc K hK f) v).symm
  refine ⟨{ toFun := fun v => ⟨avg v, Compact.averageMap_mem_fixedVectors ρc hρc K hK v⟩
            map_add' := fun v w => Subtype.ext (avg.map_add v w)
            map_smul' := fun b v => Subtype.ext (hsmul b v) }, ?_⟩
  apply LinearMap.ext
  intro x
  exact Subtype.ext (Compact.averageMap_id ρc hρc K hK x.val x.property)

/-- For a flat `V` over a Noetherian ring, a finite `V^K` is projective. -/
theorem projective_fixedVectors [IsNoetherianRing B] (hρ : IsSmooth ρ)
    [Module.Flat B V] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [Module.Finite B (fixedVectors ρ K.toSubgroup)] :
    Module.Projective B (fixedVectors ρ K.toSubgroup) := by
  obtain ⟨r, hr⟩ := exists_fixedVectors_retraction ρ hρ K hK
  have : Module.Flat B (fixedVectors ρ K.toSubgroup) :=
    Module.Flat.of_retract _ r hr
  have := Module.finitePresentation_of_finite B (fixedVectors ρ K.toSubgroup)
  exact Module.Flat.projective_of_finitePresentation

variable [IsNoetherianRing B] (hG : IsLocallyProfinite G) (hρ : IsSmooth ρ)
  [Module.Flat B V]
  (hfin : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    Module.Finite B (fixedVectors ρ K.toSubgroup))
include hG hρ hfin

/-- Linear forms separate the vectors of `V`. -/
theorem eq_zero_of_forall_linearForm {x : V} (hx : ∀ ℓ : V →ₗ[B] B, ℓ x = 0) :
    x = 0 := by
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_fixedVectors ρ hG hρ x
  have := hfin K hK
  have := projective_fixedVectors ρ hρ K hK
  obtain ⟨r, hr⟩ := exists_fixedVectors_retraction ρ hρ K hK
  have hrx : r x = ⟨x, hxK⟩ := LinearMap.congr_fun hr ⟨x, hxK⟩
  have h0 : (⟨x, hxK⟩ : fixedVectors ρ K.toSubgroup) = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff B _).mp fun f => ?_
    rw [← hrx]
    exact hx (f ∘ₗ r)
  exact congrArg Subtype.val h0

/-- Every vector lies in `I • V`, where `I` is the ideal of values of linear forms. -/
theorem mem_linearFormIdeal_smul_top (v : V) :
    v ∈ Ideal.span {a : B | ∃ (ℓ : V →ₗ[B] B) (x : V), ℓ x = a} •
      (⊤ : Submodule B V) := by
  obtain ⟨K, hK, hvK⟩ := exists_compact_mem_fixedVectors ρ hG hρ v
  have := hfin K hK
  have := projective_fixedVectors ρ hρ K hK
  obtain ⟨r, hr⟩ := exists_fixedVectors_retraction ρ hρ K hK
  obtain ⟨s, hs⟩ := Module.projective_def'.mp
    (inferInstance : Module.Projective B (fixedVectors ρ K.toSubgroup))
  have h1 : r v = ⟨v, hvK⟩ := LinearMap.congr_fun hr ⟨v, hvK⟩
  have h2 := LinearMap.congr_fun hs (r v)
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply, LinearMap.id_apply] at h2
  have hv : v = ∑ p ∈ (s (r v)).support, s (r v) p • (p : V) := by
    have h3 := congrArg Subtype.val h2
    rw [Finsupp.sum, Submodule.coe_sum] at h3
    calc v = ((r v : fixedVectors ρ K.toSubgroup) : V) := by rw [h1]
      _ = _ := by simpa using h3.symm
  rw [hv]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  exact Ideal.subset_span ⟨Finsupp.lapply p ∘ₗ s ∘ₗ r, v, rfl⟩

end Helpers

section Nakayama

variable {B : Type uB} [CommRing B] [IsNoetherianRing B] {V : Type uV} [AddCommGroup V]
  [Module B V]

/-- If `I • V = V` for the ideal `I` of values of linear forms, some `e ∈ I` acts as the
identity. -/
theorem exists_mem_linearFormIdeal_smul_eq
    (htop : ∀ v : V, v ∈ Ideal.span {a : B | ∃ (ℓ : V →ₗ[B] B) (x : V), ℓ x = a} •
      (⊤ : Submodule B V)) :
    ∃ e ∈ Ideal.span {a : B | ∃ (ℓ : V →ₗ[B] B) (x : V), ℓ x = a}, ∀ v : V, e • v = v := by
  set I := Ideal.span {a : B | ∃ (ℓ : V →ₗ[B] B) (x : V), ℓ x = a} with hI
  have hle : I ≤ I • I := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨ℓ, x, rfl⟩
    have hmap : (I • (⊤ : Submodule B V)).map ℓ ≤ I • I := by
      rw [Submodule.map_smul'']
      refine smul_mono_right _ ?_
      rintro _ ⟨y, -, rfl⟩
      exact Ideal.subset_span ⟨ℓ, y, rfl⟩
    exact hmap ⟨x, htop x, rfl⟩
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I I
    (IsNoetherian.noetherian I) hle
  refine ⟨1 - r, ?_, fun v => ?_⟩
  · have := I.neg_mem hr1
    rwa [neg_sub] at this
  · have hrv : r • v = 0 := by
      refine Submodule.smul_induction_on (htop v) ?_ ?_
      · intro a ha y _
        rw [smul_smul, ← smul_eq_mul, hr a ha, zero_smul]
      · intro x y hx hy
        rw [smul_add, hx, hy, add_zero]
    rw [sub_smul, one_smul, hrv, sub_zero]

omit [IsNoetherianRing B] in
/-- The relation `ℓ x • φ m = ℓ (φ x) • m` and an element of the linear-form ideal acting
as the identity make `φ` a scalar. -/
theorem exists_eq_smul_of_linearForm_relation (φ : V →ₗ[B] V)
    (hrel : ∀ (ℓ : V →ₗ[B] B) (x m : V), ℓ x • φ m = ℓ (φ x) • m) {e : B}
    (he : e ∈ Ideal.span {a : B | ∃ (ℓ : V →ₗ[B] B) (x : V), ℓ x = a})
    (hev : ∀ v : V, e • v = v) :
    ∃ b : B, ∀ v : V, φ v = b • v := by
  have key : ∀ a ∈ Ideal.span {a : B | ∃ (ℓ : V →ₗ[B] B) (x : V), ℓ x = a},
      ∃ b : B, ∀ m : V, a • φ m = b • m := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨ℓ, x, rfl⟩ := ha
      exact ⟨ℓ (φ x), hrel ℓ x⟩
    | zero => exact ⟨0, fun m => by simp⟩
    | add a a' _ _ ha ha' =>
      obtain ⟨b, hb⟩ := ha
      obtain ⟨b', hb'⟩ := ha'
      exact ⟨b + b', fun m => by rw [add_smul, add_smul, hb, hb']⟩
    | smul c a _ ha =>
      obtain ⟨b, hb⟩ := ha
      exact ⟨c * b, fun m => by rw [smul_eq_mul, mul_smul, mul_smul, hb]⟩
  obtain ⟨b, hb⟩ := key e he
  exact ⟨b, fun v => by rw [← hb, hev]⟩

end Nakayama

section Schur

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module B V] (ρ : Representation B G V)

/-- Schur's lemma at an irreducible fiber: `φ` acts on the fiber at `χ` by a scalar `c`,
so `χ (ℓ (φ v)) = c * χ (ℓ v)` for every linear form `ℓ`. -/
theorem exists_fiber_scalar (hG : IsLocallyProfinite G) (hρ : IsSmooth ρ)
    (hfin : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      Module.Finite B (fixedVectors ρ K.toSubgroup))
    (φ : V →ₗ[B] V) (hφ : ∀ (g : G) (v : V), φ (ρ g v) = ρ g (φ v)) (χ : B →ₐ[ℂ] ℂ)
    (hirr : letI : Algebra B ℂ := χ.toRingHom.toAlgebra
      Representation.IsIrreducible ((Module.End.baseChangeHom B ℂ V).toMonoidHom.comp ρ)) :
    ∃ c : ℂ, ∀ (ℓ : V →ₗ[B] B) (v : V), χ (ℓ (φ v)) = c * χ (ℓ v) := by
  let : Algebra B ℂ := χ.toRingHom.toAlgebra
  let ρW := (Module.End.baseChangeHom B ℂ V).toMonoidHom.comp ρ
  have : Representation.IsIrreducible ρW := hirr
  have hρW : ∀ g, ρW g = (ρ g).baseChange ℂ := fun g => rfl
  let φW : (ℂ ⊗[B] V) →ₗ[ℂ] (ℂ ⊗[B] V) := φ.baseChange ℂ
  have hφW : ∀ g, φW ∘ₗ ρW g = ρW g ∘ₗ φW := by
    intro g
    rw [hρW, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact LinearMap.ext fun v => hφ g v
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, (1 : ℂ) ⊗ₜ[B] v₀ ≠ 0 := by
    by_contra! h
    have hsub : ∀ w : ℂ ⊗[B] V, w = 0 := by
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul z v =>
        rw [show z ⊗ₜ[B] v = z • ((1 : ℂ) ⊗ₜ[B] v) by rw [smul_tmul', smul_eq_mul, mul_one],
          h v, smul_zero]
      | add w w' hw hw' => rw [hw, hw', add_zero]
    have : Subsingleton (ℂ ⊗[B] V) := ⟨fun a b => (hsub a).trans (hsub b).symm⟩
    exact bot_ne_top (α := Subrepresentation ρW) (Subrepresentation.ext (Subsingleton.elim _ _))
  obtain ⟨K, hK, hv₀K⟩ := exists_compact_mem_fixedVectors ρ hG hρ v₀
  have := hfin K hK
  obtain ⟨r, hr⟩ := exists_fixedVectors_retraction ρ hρ K hK
  have hφM : ∀ x ∈ fixedVectors ρ K.toSubgroup, φ x ∈ fixedVectors ρ K.toSubgroup := by
    intro x hx k
    change ρ k (φ x) = φ x
    rw [← hφ]
    exact congrArg φ (hx k)
  let φM := φ.restrict hφM
  let ι := (fixedVectors ρ K.toSubgroup).subtype
  let ιC : (ℂ ⊗[B] fixedVectors ρ K.toSubgroup) →ₗ[ℂ] (ℂ ⊗[B] V) := ι.baseChange ℂ
  have hιC : Function.Injective ιC := by
    have hleft : (r.baseChange ℂ) ∘ₗ ιC = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := r.baseChange ℂ)
      (fun w => LinearMap.congr_fun hleft w)
  have hcomm : ιC ∘ₗ φM.baseChange ℂ = φW ∘ₗ ιC := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
  have : Nontrivial (ℂ ⊗[B] fixedVectors ρ K.toSubgroup) := by
    refine ⟨⟨(1 : ℂ) ⊗ₜ[B] (⟨v₀, hv₀K⟩ : fixedVectors ρ K.toSubgroup), 0, fun h => hv₀ ?_⟩⟩
    have := congrArg ιC h
    rwa [map_zero, LinearMap.baseChange_tmul] at this
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φM.baseChange ℂ)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hu0 : ιC x ≠ 0 := fun h => hx.2 (hιC (h.trans ιC.map_zero.symm))
  have hu : φW (ιC x) = c • ιC x := by
    have h := LinearMap.congr_fun hcomm x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hx.apply_eq_smul, map_smul] at h
    exact h.symm
  let f : Representation.IntertwiningMap ρW ρW :=
    { toLinearMap := φW - c • LinearMap.id
      isIntertwining' := fun g => by
        rw [LinearMap.sub_comp, LinearMap.comp_sub, hφW g, LinearMap.smul_comp,
          LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id] }
  have hf : f = 0 := by
    refine (Representation.IsIrreducible.injective_or_eq_zero f).resolve_left fun hinj => hu0 ?_
    apply hinj
    change φW (ιC x) - c • ιC x = φW 0 - c • (0 : ℂ ⊗[B] V)
    rw [hu, sub_self, map_zero, smul_zero, sub_self]
  have hscalar : ∀ w, φW w = c • w := by
    intro w
    have h := congrArg (fun F : Representation.IntertwiningMap ρW ρW => F.toLinearMap w) hf
    exact sub_eq_zero.mp h
  refine ⟨c, fun ℓ v => ?_⟩
  let ev : (ℂ ⊗[B] V) →ₗ[B] ℂ := (TensorProduct.rid B ℂ).toLinearMap ∘ₗ LinearMap.lTensor ℂ ℓ
  have h1 := congrArg ev (hscalar ((1 : ℂ) ⊗ₜ[B] v))
  simp only [ev, φW, LinearMap.baseChange_tmul, smul_tmul', smul_eq_mul, mul_one,
    LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at h1
  rw [mul_comm]
  simpa using h1

end Schur

/-- Renard VI.8.6 Proposition. -/
theorem endomorphismScalar : EndomorphismScalarStatement.{uB, uG, uV} := by
  intro B _ _ _ _ _ G _ _ _ hG V _ _ ρ hρ hflat hfin φ hφ Ξ hdense hirr
  have := hflat
  have hsep : ∀ b : B, (∀ χ ∈ Ξ, χ b = 0) → b = 0 := fun b hb =>
    GroupScheme.KostantRosenlicht.eq_zero_of_forall_algHom (k := ℂ) (hdense b hb)
  have hc : ∀ χ ∈ Ξ, ∃ c : ℂ, ∀ (ℓ : V →ₗ[B] B) (v : V), χ (ℓ (φ v)) = c * χ (ℓ v) :=
    fun χ hχ => exists_fiber_scalar ρ hG hρ hfin φ hφ χ (hirr χ hχ)
  have hrel : ∀ (ℓ : V →ₗ[B] B) (x m : V), ℓ x • φ m = ℓ (φ x) • m := by
    intro ℓ x m
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_linearForm ρ hG hρ hfin fun ℓ' => ?_
    refine hsep _ fun χ hχ => ?_
    obtain ⟨c, hc⟩ := hc χ hχ
    simp only [map_sub, map_smul, smul_eq_mul, map_mul, hc]
    ring
  obtain ⟨e, he, hev⟩ :=
    exists_mem_linearFormIdeal_smul_eq (mem_linearFormIdeal_smul_top ρ hG hρ hfin)
  exact exists_eq_smul_of_linearForm_relation φ hrel he hev

end Langlands.Renard.AlgebraicFamily
