import Langlands.Representation.Smooth.Contragredient.FiniteLengthStatement
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.Admissibility.ExactProof
import Mathlib.RingTheory.Length

/-! # Finite length of admissible smooth contragredients -/

noncomputable section

namespace Langlands

open scoped MonoidAlgebra

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private noncomputable abbrev restrictedComplexModule (M : Type uV)
    [AddCommGroup M] [Module ℂ[G] M] :
    @Module ℂ (RestrictScalars ℂ ℂ[G] M) _ AddCommGroup.toAddCommMonoid :=
  RestrictScalars.module ℂ ℂ[G] M

attribute [local instance] restrictedComplexModule

set_option backward.isDefEq.respectTransparency false in
private def moduleIntertwiner
    {M N : Type uV} [AddCommGroup M] [Module ℂ[G] M]
    [AddCommGroup N] [Module ℂ[G] N] (f : M →ₗ[ℂ[G]] N) :
    (Representation.ofModule (k := ℂ) (G := G) M).IntertwiningMap
      (Representation.ofModule (k := ℂ) (G := G) N) where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := f.map_smul (algebraMap ℂ ℂ[G] c) x
  isIntertwining' g := by ext; apply f.map_smul

set_option backward.isDefEq.respectTransparency false in
private theorem module_contragredient_finiteLength
    (hcof : CompactOpenCofinal G)
    {M : Type uV} [AddCommGroup M] [Module ℂ[G] M]
    (hM : IsFiniteLength ℂ[G] M) :
    IsAdmissible (Representation.ofModule (k := ℂ) (G := G) M) →
      IsFiniteLength ℂ[G]
        (smoothContragredient (Representation.ofModule (k := ℂ) (G := G) M)).asModule := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      intro _
      have : Subsingleton (RestrictScalars ℂ ℂ[G] M) :=
        (RestrictScalars.addEquiv ℂ ℂ[G] M).injective.subsingleton
      have : Subsingleton (SmoothDual (Representation.ofModule (k := ℂ) (G := G) M)) := by
        constructor
        intro f g
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        rw [Subsingleton.elim v 0, map_zero, map_zero]
      have : Subsingleton
          (smoothContragredient (Representation.ofModule (k := ℂ) (G := G) M)).asModule :=
        (smoothContragredient (Representation.ofModule (k := ℂ) (G := G) M)).asModuleEquiv.injective.subsingleton
      exact .of_subsingleton
  | @of_simple_quotient M _ _ N _ _ ih =>
      intro hA
      let i := moduleIntertwiner N.subtype
      let q := moduleIntertwiner N.mkQ
      have hi : Function.Injective i := N.injective_subtype
      have hq : Function.Surjective q := N.mkQ_surjective
      have hexact : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
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
      obtain ⟨hNadm, hQadm⟩ :=
        (isAdmissible_iff_of_shortExact hcof i q hi hq hexact hA.1).mp hA
      have hNfinite := ih hNadm
      have hQirr :
          (SmoothRep.of (Representation.ofModule (k := ℂ) (G := G) (M ⧸ N))
            hQadm.1).IsIrreducible :=
        (Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp inferInstance
      have hQdualirr :=
        (SmoothRep.isIrreducible_contragredient_iff hcof
          (SmoothRep.of (Representation.ofModule (k := ℂ) (G := G) (M ⧸ N))
            hQadm.1) hQadm).mpr hQirr
      have hQfinite : IsFiniteLength ℂ[G]
          (smoothContragredient
            (Representation.ofModule (k := ℂ) (G := G) (M ⧸ N))).asModule := by
        have hsimple : IsSimpleModule ℂ[G]
            (smoothContragredient
              (Representation.ofModule (k := ℂ) (G := G) (M ⧸ N))).asModule :=
          (Representation.irreducible_iff_isSimpleModule_asModule _).mp hQdualirr
        rw [← Module.length_ne_top_iff, Module.length_eq_one_iff.mpr hsimple]
        exact ENat.one_ne_top
      let di := contragredientMap q
      let dq := contragredientMap i
      have hdi : Function.Injective di :=
        contragredientMap_injective_of_surjective q hq
      have hdq : Function.Surjective dq :=
        contragredientMap_surjective_of_injective_of_compact_cofinal
          hcof hNadm.1 hA.1 i hi
      have hdexact : Function.Exact di dq :=
        contragredientMap_exact_of_surjective i q
          (LinearMap.exact_iff.mpr hexact.symm) hq
      let fi :
          (smoothContragredient
            (Representation.ofModule (k := ℂ) (G := G) (M ⧸ N))).asModule →ₗ[ℂ[G]]
          (smoothContragredient
            (Representation.ofModule (k := ℂ) (G := G) M)).asModule :=
        Representation.IntertwiningMap.equivLinearMapAsModule _ _ di
      let fq :
          (smoothContragredient
            (Representation.ofModule (k := ℂ) (G := G) M)).asModule →ₗ[ℂ[G]]
          (smoothContragredient
            (Representation.ofModule (k := ℂ) (G := G) N)).asModule :=
        Representation.IntertwiningMap.equivLinearMapAsModule _ _ dq
      have hfi : Function.Injective fi := by
        intro v w hvw
        exact hdi hvw
      have hfq : Function.Surjective fq := by
        intro v
        exact hdq v
      have hfexact : Function.Exact fi fq := by
        intro v
        exact hdexact v
      have hlength := Module.length_eq_add_of_exact
        (R := ℂ[G])
        (N := (smoothContragredient
          (Representation.ofModule (k := ℂ) (G := G) (M ⧸ N))).asModule)
        (M := (smoothContragredient
          (Representation.ofModule (k := ℂ) (G := G) M)).asModule)
        (P := (smoothContragredient
          (Representation.ofModule (k := ℂ) (G := G) N)).asModule)
        fi fq hfi hfq hfexact
      rw [← Module.length_ne_top_iff] at hQfinite hNfinite ⊢
      rw [hlength]
      simpa only [ne_eq, ENat.add_eq_top, not_or] using And.intro hQfinite hNfinite

set_option backward.isDefEq.respectTransparency false in
private def toModuleRepresentation
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    ρ.IntertwiningMap (Representation.ofModule (k := ℂ) (G := G) ρ.asModule) where
  toFun v := (RestrictScalars.addEquiv ℂ ℂ[G] ρ.asModule).symm (ρ.asModuleEquiv.symm v)
  map_add' v w := rfl
  map_smul' c v := by
    simp only [Representation.asModuleEquiv_symm_map_smul]
    rfl
  isIntertwining' g := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Representation.ofModule_asModule_act]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The smooth dual of an admissible finite-length smooth complex
representation has finite length. -/
theorem SmoothRep.contragredient_hasFiniteLength (hcof : CompactOpenCofinal G)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
    (hfinite : A.HasFiniteLength) : A.contragredient.HasFiniteLength := by
  let f := toModuleRepresentation A.representation
  have hf : Function.Bijective f :=
    (RestrictScalars.addEquiv ℂ ℂ[G] A.representation.asModule).symm.bijective.comp
      A.representation.asModuleEquiv.symm.bijective
  let e := f.ofBijective hf
  have hMadm := isAdmissible_of_injective e.symm.toIntertwiningMap e.symm.injective hA
  have hMfinite := module_contragredient_finiteLength hcof hfinite hMadm
  exact hMfinite.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (contragredientMap f))
    (contragredientMap_surjective_of_injective_of_compact_cofinal
      hcof A.isSmooth hMadm.1 f hf.1)

/-- Generic finite-length preservation, retaining the admissibility premise. -/
theorem smoothContragredientFiniteLength :
    SmoothContragredientFiniteLengthStatement.{uG, uV} := by
  intro G _ _ _ hcof A hA hfinite
  exact A.contragredient_hasFiniteLength hcof hA hfinite

end Langlands
