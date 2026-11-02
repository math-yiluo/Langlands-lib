import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCobar
import Langlands.AlgebraicGeometry.GroupoidCoactionExact

/-! # Stable submodules and restriction of coactions -/

universe u v w

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type v} [AddCommGroup M] [Module B M]

/-- A submodule is stable if its coaction lands in the tensor image of that submodule. -/
def IsStableSubmodule (θ : GroupoidCoaction t M) (N : Submodule B M) : Prop :=
  ∀ m : N, θ.coaction m ∈ LinearMap.range (AlgebraTensorModule.lTensor C C N.subtype)

variable (θ : GroupoidCoaction t M) (N : Submodule B M)

/-- The semilinear restriction to a stable submodule. -/
noncomputable def submoduleSemilinearMap [Module.Flat B C]
    (hN : θ.IsStableSubmodule N) : N →ₛₗ[t] C ⊗[B] N :=
  (LinearEquiv.ofInjective (AlgebraTensorModule.lTensor C C N.subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.subtype_injective)).symm.toLinearMap.comp
    ((θ.semilinearMap.domRestrict N).codRestrict
      (LinearMap.range (AlgebraTensorModule.lTensor C C N.subtype)) hN)

theorem submoduleSemilinearMap_subtype [Module.Flat B C]
    (hN : θ.IsStableSubmodule N) (m : N) :
    LinearMap.lTensor C N.subtype (submoduleSemilinearMap θ N hN m) =
      θ.coaction m := by
  exact LinearEquiv.ofInjective_symm_apply
    (AlgebraTensorModule.lTensor C C N.subtype)
    (h := Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.subtype_injective) _

/-- Restriction of a coaction to a stable submodule. -/
noncomputable def submodule (hE : RingEtaleEquivalenceRelation t)
    (hN : θ.IsStableSubmodule N) : GroupoidCoaction t N := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  exact ofInjective hE θ N.subtype N.subtype_injective
    (submoduleSemilinearMap θ N hN).toAddMonoidHom
    (fun b m => (submoduleSemilinearMap θ N hN).map_smulₛₗ b m)
    (fun m => (submoduleSemilinearMap_subtype θ N hN m).symm)

/-- The inclusion of a stable submodule is equivariant. -/
theorem submodule_subtype_isHom (hE : RingEtaleEquivalenceRelation t)
    (hN : θ.IsStableSubmodule N) :
    (submodule θ N hE hN).IsHom θ N.subtype := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  intro m
  exact (submoduleSemilinearMap_subtype θ N hN m).symm

/-- Stability is equivalent to the existence of an equivariant coaction on the submodule. -/
theorem isStableSubmodule_iff_exists_coaction (hE : RingEtaleEquivalenceRelation t) :
    θ.IsStableSubmodule N ↔ ∃ θN : GroupoidCoaction t N, θN.IsHom θ N.subtype := by
  constructor
  · intro hN
    exact ⟨submodule θ N hE hN, submodule_subtype_isHom θ N hE hN⟩
  · rintro ⟨θN, hi⟩ m
    exact ⟨θN.coaction m, (hi m).symm⟩

/-- The semilinear map induced on the quotient by a stable submodule. -/
def submoduleQuotientSemilinearMap (hN : θ.IsStableSubmodule N) :
    M ⧸ N →ₛₗ[t] C ⊗[B] (M ⧸ N) :=
  N.liftQ ((AlgebraTensorModule.lTensor C C N.mkQ).comp θ.semilinearMap) (by
    intro m hm
    obtain ⟨x, hx⟩ := hN ⟨m, hm⟩
    change LinearMap.lTensor C N.mkQ (θ.coaction m) = 0
    rw [← hx]
    change LinearMap.lTensor C N.mkQ (LinearMap.lTensor C N.subtype x) = 0
    rw [← LinearMap.lTensor_comp_apply]
    have hq : N.mkQ.comp N.subtype = 0 := by
      ext n
      exact (Submodule.Quotient.mk_eq_zero N).mpr n.property
    rw [hq]
    simp)

/-- The quotient coaction induced by a stable submodule. -/
def submoduleQuotient (hN : θ.IsStableSubmodule N) : GroupoidCoaction t (M ⧸ N) :=
  ofSurjective θ N.mkQ N.mkQ_surjective
    (submoduleQuotientSemilinearMap θ N hN).toAddMonoidHom
    (fun b m => (submoduleQuotientSemilinearMap θ N hN).map_smulₛₗ b m)
    (fun _ => rfl)

theorem submoduleQuotient_mkQ_isHom (hN : θ.IsStableSubmodule N) :
    θ.IsHom (submoduleQuotient θ N hN) N.mkQ := fun _ => rfl

/-- A tensor belongs to one member of a directed submodule cover. -/
theorem exists_lTensor_subtype_of_directed {ι : Type w} (F : ι → Submodule B M)
    (hdir : Directed (· ≤ ·) F) (hcover : ∀ m : M, ∃ i, m ∈ F i)
    (x : C ⊗[B] M) :
    ∃ (i : ι) (y : C ⊗[B] F i), LinearMap.lTensor C (F i).subtype y = x := by
  induction x with
  | tmul c m =>
      obtain ⟨i, hi⟩ := hcover m
      exact ⟨i, c ⊗ₜ[B] (⟨m, hi⟩ : F i), rfl⟩
  | add x y hx hy =>
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      obtain ⟨k, hik, hjk⟩ := hdir i j
      refine ⟨k, LinearMap.lTensor C (Submodule.inclusion hik) xi +
        LinearMap.lTensor C (Submodule.inclusion hjk) yj, ?_⟩
      rw [map_add, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply,
        Submodule.subtype_comp_inclusion, Submodule.subtype_comp_inclusion, hxi, hyj]

/-- Cocycle vanishing passes to a directed union of stable submodules. -/
theorem oneCohomologyVanishes_of_directed_submodules
    (hE : RingEtaleEquivalenceRelation t) {ι : Type w} (F : ι → Submodule B M)
    (hdir : Directed (· ≤ ·) F) (hcover : ∀ m : M, ∃ i, m ∈ F i)
    (hstable : ∀ i, θ.IsStableSubmodule (F i))
    (hvan : ∀ i, (submodule θ (F i) hE (hstable i)).OneCohomologyVanishes) :
    θ.OneCohomologyVanishes := by
  intro x hx
  obtain ⟨i, y, hy⟩ := exists_lTensor_subtype_of_directed F hdir hcover x
  have hcy : (submodule θ (F i) hE (hstable i)).IsOneCocycle y :=
    isOneCocycle_of_injective (F i).subtype
      (submodule_subtype_isHom θ (F i) hE (hstable i))
      (F i).subtype_injective y (hy.symm ▸ hx)
  obtain ⟨m, hm⟩ := hvan i y hcy
  refine ⟨m, ?_⟩
  change θ.coboundary ((F i).subtype m) = x
  rw [coboundary_naturality (F i).subtype
    (submodule_subtype_isHom θ (F i) hE (hstable i)), hm, hy]

end Langlands.AlgebraicGeometry.GroupoidCoaction
