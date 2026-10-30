import Langlands.Representation.Smooth.Admissibility.FiniteLengthStatement
import Langlands.Representation.Smooth.Admissibility.ExactProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof
import Langlands.Group.GL.CompactOpen

/-! Finite-length induction for admissibility, with GL and product-Levi specializations. -/

namespace Langlands

open scoped MonoidAlgebra

universe uF uV uG

section FiniteLengthInduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private noncomputable abbrev restrictedComplexModule (M : Type uV) [AddCommGroup M] [Module ℂ[G] M] :
    @Module ℂ (RestrictScalars ℂ ℂ[G] M) _ AddCommGroup.toAddCommMonoid :=
  RestrictScalars.module ℂ ℂ[G] M

attribute [local instance] restrictedComplexModule

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIntertwiner
    {M N : Type uV} [AddCommGroup M] [Module ℂ[G] M]
    [AddCommGroup N] [Module ℂ[G] N] (f : M →ₗ[ℂ[G]] N) :
    (Representation.ofModule (k := ℂ) (G := G) M).IntertwiningMap
      (Representation.ofModule (k := ℂ) (G := G) N) where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := f.map_smul (algebraMap ℂ ℂ[G] c) x
  isIntertwining' g := by ext; apply f.map_smul

private theorem module_admissible_of_finiteLength
    (hcofinal : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H)
    (hirr : ∀ A : SmoothRep.{0, uG, uV} ℂ G, A.IsIrreducible → A.IsAdmissible)
    {M : Type uV} [AddCommGroup M] [Module ℂ[G] M]
    (hM : IsFiniteLength ℂ[G] M) :
    IsSmooth (Representation.ofModule (k := ℂ) (G := G) M) →
      IsAdmissible (Representation.ofModule (k := ℂ) (G := G) M) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      intro hsmooth
      have : Subsingleton (RestrictScalars ℂ ℂ[G] M) :=
        (RestrictScalars.addEquiv ℂ ℂ[G] M).injective.subsingleton
      exact ⟨hsmooth, fun _ => inferInstance⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
      intro hsmooth
      let i := moduleIntertwiner N.subtype
      let q := moduleIntertwiner N.mkQ
      have hi : Function.Injective i := N.injective_subtype
      have hq : Function.Surjective q := N.mkQ_surjective
      have hN := isSmooth_of_injective i hi hsmooth
      have hQ := isSmooth_of_surjective q hq hsmooth
      have hNadm := ih hN
      have hQadm : IsAdmissible (Representation.ofModule (k := ℂ) (G := G) (M ⧸ N)) :=
        hirr (SmoothRep.of _ hQ)
          ((Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp
            inferInstance)
      apply (isAdmissible_iff_of_shortExact hcofinal i q hi hq ?_ hsmooth).mpr
        ⟨hNadm, hQadm⟩
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
private noncomputable def toModuleRepresentation
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

private theorem admissible_of_finiteLength_of_irreducible
    (hcofinal : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H)
    (hirr : ∀ A : SmoothRep.{0, uG, uV} ℂ G, A.IsIrreducible → A.IsAdmissible)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength) : A.IsAdmissible := by
  let f := toModuleRepresentation A.representation
  have hf : Function.Bijective f :=
    (RestrictScalars.addEquiv ℂ ℂ[G] A.representation.asModule).symm.bijective.comp
      A.representation.asModuleEquiv.symm.bijective
  have hsmooth := isSmooth_of_surjective f hf.2 A.isSmooth
  exact isAdmissible_of_injective f hf.1
    (module_admissible_of_finiteLength hcofinal hirr hA hsmooth)

end FiniteLengthInduction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Finite-length smooth representations of every GL rank are admissible. -/
theorem glFiniteLengthAdmissibility :
    GLFiniteLengthAdmissibilityStatement.{uF, uV} F T := by
  let := T.topology
  intro n A hA
  let := T.generalLinearTopologicalGroup n
  apply admissible_of_finiteLength_of_irreducible (A := A) (hA := hA)
  · intro H
    obtain ⟨K, hK, hKH⟩ := T.generalLinearCompactOpen n (H : Set _) (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, hKH⟩
  · intro σ hσ
    exact (CuspidalSupport.cuspidalEmbedding F T n σ hσ).1

/-- Finite-length smooth representations of every product Levi are admissible. -/
theorem leviFiniteLengthAdmissibility :
    LeviFiniteLengthAdmissibilityStatement.{uF, uV} F T := by
  let := T.topology
  intro n B A hA
  let := T.leviTopologicalGroup B
  apply admissible_of_finiteLength_of_irreducible (A := A) (hA := hA)
  · intro H
    obtain ⟨K, hK, hKH⟩ := T.leviCompactOpen B (H : Set _) (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, hKH⟩
  · intro σ hσ
    exact CuspidalSupport.irreducibleLeviAdmissibility F T n B σ hσ

/-- Finite-length smooth GL and product-Levi representations are admissible. -/
theorem finiteLengthAdmissibility :
    FiniteLengthAdmissibilityStatement.{uF, uV} F T :=
  ⟨glFiniteLengthAdmissibility F T, leviFiniteLengthAdmissibility F T⟩

/-- The theorem also applies to the carriers used by the finite-length class maps. -/
example : FiniteLengthAdmissibilityStatement.{uF, max uF uV} F T :=
  finiteLengthAdmissibility.{uF, max uF uV} F T

end Langlands
