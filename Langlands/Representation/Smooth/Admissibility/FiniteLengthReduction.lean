import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Admissibility.Extension
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! General finite-length induction for admissibility using extension closure. -/

namespace Langlands

open scoped MonoidAlgebra

universe uR uG uV

section FiniteLengthInduction

variable {k : Type uR} [Field k]
variable {G : Type uG} [Group G] [TopologicalSpace G]

private noncomputable abbrev restrictedModule (M : Type uV) [AddCommGroup M] [Module k[G] M] :
    @Module k (RestrictScalars k k[G] M) _ AddCommGroup.toAddCommMonoid :=
  RestrictScalars.module k k[G] M

attribute [local instance] restrictedModule

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIntertwiner
    {M N : Type uV} [AddCommGroup M] [Module k[G] M]
    [AddCommGroup N] [Module k[G] N] (f : M →ₗ[k[G]] N) :
    (Representation.ofModule (k := k) (G := G) M).IntertwiningMap
      (Representation.ofModule (k := k) (G := G) N) where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := f.map_smul (algebraMap k k[G] c) x
  isIntertwining' g := by ext; apply f.map_smul

private theorem module_admissible_of_finiteLength
    (hirr : ∀ A : SmoothRep.{uR, uG, uV} k G, A.IsIrreducible → A.IsAdmissible)
    {M : Type uV} [AddCommGroup M] [Module k[G] M]
    (hM : IsFiniteLength k[G] M) :
    IsSmooth (Representation.ofModule (k := k) (G := G) M) →
      IsAdmissible (Representation.ofModule (k := k) (G := G) M) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      intro hsmooth
      have : Subsingleton (RestrictScalars k k[G] M) :=
        (RestrictScalars.addEquiv k k[G] M).injective.subsingleton
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
      have hQadm : IsAdmissible (Representation.ofModule (k := k) (G := G) (M ⧸ N)) :=
        hirr (SmoothRep.of _ hQ)
          ((Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp
            inferInstance)
      apply isAdmissible_of_extension i q hi ?_ hsmooth hNadm hQadm
      intro v hv
      let x : M := RestrictScalars.addEquiv k k[G] M v
      have hx : x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hv
      exact ⟨(RestrictScalars.addEquiv k k[G] N).symm ⟨x, hx⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The intertwiner from a representation to the representation associated
with its group-algebra module, using the canonical restriction-of-scalars
identification of carriers. Its underlying function is bijective. -/
noncomputable def representationToModuleIntertwiner
    {V : Type uV} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    ρ.IntertwiningMap (Representation.ofModule (k := k) (G := G) ρ.asModule) where
  toFun v := (RestrictScalars.addEquiv k k[G] ρ.asModule).symm (ρ.asModuleEquiv.symm v)
  map_add' v w := rfl
  map_smul' c v := by
    simp only [Representation.asModuleEquiv_symm_map_smul]
    rfl
  isIntertwining' g := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Representation.ofModule_asModule_act]
    rfl

/-- If every irreducible smooth representation at a fixed carrier universe is
admissible, every finite-length smooth representation at that universe is
admissible, for an arbitrary group topology and arbitrary coefficient field. -/
theorem SmoothRep.isAdmissible_of_finiteLength_of_irreducible
    (hirr : ∀ A : SmoothRep.{uR, uG, uV} k G, A.IsIrreducible → A.IsAdmissible)
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.HasFiniteLength) : A.IsAdmissible := by
  let f := representationToModuleIntertwiner A.representation
  have hf : Function.Bijective f :=
    (RestrictScalars.addEquiv k k[G] A.representation.asModule).symm.bijective.comp
      A.representation.asModuleEquiv.symm.bijective
  have hsmooth := isSmooth_of_surjective f hf.2 A.isSmooth
  exact isAdmissible_of_injective f hf.1
    (module_admissible_of_finiteLength hirr hA hsmooth)

end FiniteLengthInduction

end Langlands
