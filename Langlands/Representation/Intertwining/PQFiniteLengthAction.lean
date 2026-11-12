import Langlands.Representation.Smooth.RenardSigmaCompactSchurProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthReduction
import Langlands.Representation.Intertwining.PQFiniteActionRegularity
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Finite-dimensional central actions of finite-length smooth representations -/

noncomputable section

universe uG uV uW uX

namespace Langlands.PQFiniteLengthAction

private theorem finite_of_exact
    {X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (hex : LinearMap.range f = LinearMap.ker g)
    [Module.Finite ℂ X] [Module.Finite ℂ Z] : Module.Finite ℂ Y := by
  apply Module.Finite.of_exact (f := f) (g := g.rangeRestrict) ?_ g.surjective_rangeRestrict
  intro y
  change (g.rangeRestrict y = 0 ↔ ∃ x, f x = y)
  rw [← LinearMap.mem_range, hex]
  exact Subtype.ext_iff

section Extension

variable {G : Type uG} [Group G]
  {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}

private theorem finite_hom_source_extension
    {T : Type*} [AddCommGroup T] [Module ℂ T] (π : Representation ℂ G T)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hq : Function.Surjective q)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    [Module.Finite ℂ (ρ.IntertwiningMap π)]
    [Module.Finite ℂ (τ.IntertwiningMap π)] :
    Module.Finite ℂ (σ.IntertwiningMap π) := by
  let f := (Representation.IntertwiningMap.llcomp σ τ π).flip q
  let g := (Representation.IntertwiningMap.llcomp ρ σ π).flip i
  apply finite_of_exact f g
  ext h
  constructor
  · rintro ⟨a, rfl⟩
    apply Representation.IntertwiningMap.ext
    ext v
    change a (q (i v)) = 0
    have hz : q (i v) = 0 := by
      apply hex.le
      exact ⟨v, rfl⟩
    rw [hz, map_zero]
  · intro hh
    let q' := Representation.IntertwiningMap.equivLinearMapAsModule σ τ q
    let h' := Representation.IntertwiningMap.equivLinearMapAsModule σ π h
    have hk : q'.ker ≤ h'.ker := by
      intro v hv
      obtain ⟨w, hw⟩ := hex.ge hv
      change h v = 0
      rw [← hw]
      exact congrArg (fun a : ρ.IntertwiningMap π => a w) hh
    let e := q'.quotKerEquivOfSurjective hq
    let a := (q'.ker.liftQ h' hk).comp e.symm.toLinearMap
    refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule τ π).symm a, ?_⟩
    apply Representation.IntertwiningMap.ext
    ext v
    change q'.ker.liftQ h' hk (e.symm (q' v)) = h' v
    have he : e.symm (q' v) = q'.ker.mkQ (σ.asModuleEquiv.symm v) := by
      exact q'.quotKerEquivOfSurjective_symm_apply hq (σ.asModuleEquiv.symm v)
    rw [he]
    rfl

private theorem finite_hom_target_extension
    {T : Type*} [AddCommGroup T] [Module ℂ T] (π : Representation ℂ G T)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hi : Function.Injective i)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    [Module.Finite ℂ (π.IntertwiningMap ρ)]
    [Module.Finite ℂ (π.IntertwiningMap τ)] :
    Module.Finite ℂ (π.IntertwiningMap σ) := by
  let f := Representation.IntertwiningMap.llcomp π ρ σ i
  let g := Representation.IntertwiningMap.llcomp π σ τ q
  apply finite_of_exact f g
  ext h
  constructor
  · rintro ⟨a, rfl⟩
    apply Representation.IntertwiningMap.ext
    ext v
    change q (i (a v)) = 0
    apply hex.le
    exact ⟨a v, rfl⟩
  · intro hh
    let i' := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ i
    let h' := Representation.IntertwiningMap.equivLinearMapAsModule π σ h
    have hr : ∀ v, h' v ∈ i'.range := by
      intro v
      apply hex.ge
      exact congrArg (fun a : π.IntertwiningMap τ => a v) hh
    let a := (LinearEquiv.ofInjective i' hi).symm.toLinearMap.comp
      (h'.codRestrict i'.range hr)
    refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule π ρ).symm a, ?_⟩
    apply Representation.IntertwiningMap.ext
    ext v
    exact congrArg Subtype.val ((LinearEquiv.ofInjective i' hi).apply_symm_apply
      (h'.codRestrict i'.range hr v))

end Extension

section Simple

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SigmaCompactSpace G]
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem finite_hom_simple
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hs : IsSmooth ρ) (hi : ρ.IsIrreducible) (hj : σ.IsIrreducible) :
    Module.Finite ℂ (ρ.IntertwiningMap σ) := by
  classical
  let := hi
  let := hj
  by_cases hz : ∀ f : ρ.IntertwiningMap σ, f = 0
  · let : Subsingleton (ρ.IntertwiningMap σ) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    infer_instance
  · obtain ⟨f, hf⟩ := not_forall.mp hz
    let e := f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)
    have hschur (a : ρ.IntertwiningMap ρ) :
        ∃ c : ℂ, a = c • Representation.IntertwiningMap.id ρ :=
      (countableDimensionalSchur ρ
        (Renard.Smooth.sigmaCompact_irreducible_rank_le_aleph0 ρ hs hi) hi a).exists
    let L : ℂ →ₗ[ℂ] ρ.IntertwiningMap σ :=
      LinearMap.toSpanSingleton ℂ _ f
    apply Module.Finite.of_surjective L
    intro a
    obtain ⟨c, hc⟩ := hschur (e.symm.toIntertwiningMap.comp a)
    refine ⟨c, ?_⟩
    apply Representation.IntertwiningMap.ext
    ext v
    have hv := congrArg (fun b : ρ.IntertwiningMap ρ => e (b v)) hc
    simpa [L, e, map_smul] using hv.symm

end Simple

section FiniteLength

open scoped MonoidAlgebra

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SigmaCompactSpace G]

private noncomputable abbrev restrictedModule (M : Type*) [AddCommGroup M]
    [Module ℂ[G] M] :
    @Module ℂ (RestrictScalars ℂ ℂ[G] M) _ AddCommGroup.toAddCommMonoid :=
  RestrictScalars.module ℂ ℂ[G] M

attribute [local instance] restrictedModule

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIntertwiner
    {M N : Type*} [AddCommGroup M] [Module ℂ[G] M]
    [AddCommGroup N] [Module ℂ[G] N] (f : M →ₗ[ℂ[G]] N) :
    (Representation.ofModule (k := ℂ) (G := G) M).IntertwiningMap
      (Representation.ofModule (k := ℂ) (G := G) N) where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := f.map_smul (algebraMap ℂ ℂ[G] c) x
  isIntertwining' g := by ext; apply f.map_smul

omit [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G] in
private theorem module_short_exact
    {M : Type*} [AddCommGroup M] [Module ℂ[G] M] (N : Submodule ℂ[G] M) :
    LinearMap.range (moduleIntertwiner N.subtype).toLinearMap =
      LinearMap.ker (moduleIntertwiner N.mkQ).toLinearMap := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    let x : N := RestrictScalars.addEquiv ℂ ℂ[G] N w
    change N.mkQ (x : M) = 0
    exact (Submodule.Quotient.mk_eq_zero N).mpr x.property
  · intro hv
    let x : M := RestrictScalars.addEquiv ℂ ℂ[G] M v
    have hx : x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hv
    exact ⟨(RestrictScalars.addEquiv ℂ ℂ[G] N).symm ⟨x, hx⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finite_hom_simple_module_target
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    {M : Type uW} [AddCommGroup M] [Module ℂ[G] M]
    (hM : IsFiniteLength ℂ[G] M) :
    Module.Finite ℂ (ρ.IntertwiningMap (Representation.ofModule M)) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      let : Subsingleton (RestrictScalars ℂ ℂ[G] M) :=
        (RestrictScalars.addEquiv ℂ ℂ[G] M).injective.subsingleton
      let : Subsingleton (ρ.IntertwiningMap (Representation.ofModule M)) :=
        ⟨fun f g => by ext v; exact Subsingleton.elim _ _⟩
      infer_instance
  | @of_simple_quotient M _ _ N _ _ ih =>
      let : Module.Finite ℂ (ρ.IntertwiningMap (Representation.ofModule N)) := ih
      let := finite_hom_simple ρ (Representation.ofModule (M ⧸ N)) hs hi
        ((Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp
          inferInstance)
      exact finite_hom_target_extension ρ (moduleIntertwiner N.subtype)
        (moduleIntertwiner N.mkQ) N.injective_subtype (module_short_exact N)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_hom_simple_target
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (hσ : IsFiniteLength ℂ[G] σ.asModule) :
    Module.Finite ℂ (ρ.IntertwiningMap σ) := by
  let : Module.Finite ℂ (ρ.IntertwiningMap (Representation.ofModule σ.asModule)) :=
    finite_hom_simple_module_target ρ hs hi hσ
  let f := representationToModuleIntertwiner σ
  have hf : Function.Injective f :=
    (RestrictScalars.addEquiv ℂ ℂ[G] σ.asModule).symm.injective.comp
      σ.asModuleEquiv.symm.injective
  let L := Representation.IntertwiningMap.llcomp ρ σ _ f
  apply Module.Finite.of_injective L
  intro a b hab
  ext v
  apply hf
  exact congrArg (fun c : ρ.IntertwiningMap (Representation.ofModule σ.asModule) =>
    c v) hab

set_option backward.isDefEq.respectTransparency false in
private theorem finite_hom_module_source
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : IsFiniteLength ℂ[G] σ.asModule)
    {M : Type uV} [AddCommGroup M] [Module ℂ[G] M]
    (hM : IsFiniteLength ℂ[G] M) :
    IsSmooth (Representation.ofModule (k := ℂ) (G := G) M) →
      Module.Finite ℂ ((Representation.ofModule M).IntertwiningMap σ) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      intro _
      let : Subsingleton (RestrictScalars ℂ ℂ[G] M) :=
        (RestrictScalars.addEquiv ℂ ℂ[G] M).injective.subsingleton
      let : Subsingleton ((Representation.ofModule M).IntertwiningMap σ) :=
        ⟨fun f g => by ext v; exact (by simp only [Subsingleton.elim v 0, map_zero])⟩
      infer_instance
  | @of_simple_quotient M _ _ N _ _ ih =>
      intro hs
      let i := moduleIntertwiner N.subtype
      let q := moduleIntertwiner N.mkQ
      have hNs := isSmooth_of_injective i N.injective_subtype hs
      have hQs := isSmooth_of_surjective q N.mkQ_surjective hs
      let : Module.Finite ℂ ((Representation.ofModule N).IntertwiningMap σ) := ih hNs
      let := finite_hom_simple_target (Representation.ofModule (M ⧸ N)) σ hQs
        ((Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp
          inferInstance) hσ
      exact finite_hom_source_extension σ i q N.mkQ_surjective (module_short_exact N)

/-- Over a sigma-compact topological group, intertwiners from a smooth
finite-length complex representation to any finite-length representation form a
finite-dimensional complex vector space. The two carrier universes are independent. -/
theorem finite_hom
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hs : IsSmooth ρ) (hρ : IsFiniteLength ℂ[G] ρ.asModule)
    (hσ : IsFiniteLength ℂ[G] σ.asModule) :
    Module.Finite ℂ (ρ.IntertwiningMap σ) := by
  let f := representationToModuleIntertwiner ρ
  have hf : Function.Bijective f :=
    (RestrictScalars.addEquiv ℂ ℂ[G] ρ.asModule).symm.bijective.comp
      ρ.asModuleEquiv.symm.bijective
  let := finite_hom_module_source σ hσ hρ (isSmooth_of_surjective f hf.2 hs)
  let e := f.ofBijective hf
  let L := (Representation.IntertwiningMap.llcomp _ ρ σ).flip e.symm.toIntertwiningMap
  apply Module.Finite.of_injective L
  intro a b hab
  ext v
  have hv := congrArg (fun c : (Representation.ofModule ρ.asModule).IntertwiningMap σ =>
    c (e v)) hab
  change a (e.symm (e v)) = b (e.symm (e v)) at hv
  simpa using hv

/-- The actual span of central operators is finite dimensional in finite length. -/
theorem centralActionSpan_finite
    {A : Type uX} [CommGroup A]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (c : A →* Subgroup.center G)
    (hs : IsSmooth ρ) (hρ : IsFiniteLength ℂ[G] ρ.asModule) :
    Module.Finite ℂ (Submodule.span ℂ (Set.range fun a : A => ρ (c a : G))) := by
  let := finite_hom ρ ρ hs hρ hρ
  let F := Representation.IntertwiningMap.toLinearMapl (ρ := ρ) (σ := ρ)
  have hle : Submodule.span ℂ (Set.range fun a : A => ρ (c a : G)) ≤ F.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨Representation.IntertwiningMap.centralMul ρ (c a : G) (c a).property, rfl⟩
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- The faithful group-algebra quotient of any central restricted action is
finite dimensional. No admissibility assumption is needed. -/
theorem finite_actionQuotient
    {A : Type uX} [CommGroup A]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (c : A →* Subgroup.center G)
    (hs : IsSmooth ρ) (hρ : IsFiniteLength ℂ[G] ρ.asModule) :
    Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (ρ.comp ((Subgroup.center G).subtype.comp c))) := by
  let : Module.Finite ℂ (Submodule.span ℂ
      (Set.range (ρ.comp ((Subgroup.center G).subtype.comp c)))) := by
    change Module.Finite ℂ (Submodule.span ℂ (Set.range fun a : A => ρ (c a : G)))
    exact centralActionSpan_finite ρ c hs hρ
  exact PQFiniteActionRegularity.finite_actionQuotient_of_finite_span _

end FiniteLength

/-- A finite-length smooth complex representation of a sigma-compact group
has a finite-dimensional faithful action algebra on every central subgroup. -/
def FiniteLengthCentralActionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ →
      IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule →
    ∀ (A : Type uX) [CommGroup A] (c : A →* Subgroup.center G),
      Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
        (ρ.comp ((Subgroup.center G).subtype.comp c)))

/-- The central-action finiteness statement, with independent universes for
the group, the representation carrier and the central group. -/
theorem finiteLengthCentralAction : FiniteLengthCentralActionStatement.{uG, uV, uX} := by
  intro G _ _ _ _ V _ _ ρ hs hρ A _ c
  exact finite_actionQuotient ρ c hs hρ

end Langlands.PQFiniteLengthAction
