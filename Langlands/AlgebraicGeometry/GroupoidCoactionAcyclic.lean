import Langlands.AlgebraicGeometry.GroupoidCoactionCokernel

/-! # Exactness of invariants under all-module acyclicity -/

universe u v

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N P : Type v} [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]

/-- Equivariance can be checked after an injective equivariant map. -/
lemma IsHom.of_comp_injective [Module.Flat B C]
    {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    {θP : GroupoidCoaction t P} {f : M →ₗ[B] N} {i : N →ₗ[B] P}
    (hi : θN.IsHom θP i) (hinj : Function.Injective i)
    (hf : θM.IsHom θP (i.comp f)) : θM.IsHom θN f := by
  intro m
  apply Module.Flat.lTensor_preserves_injective_linearMap i hinj
  rw [← hi (f m), ← LinearMap.lTensor_comp_apply]
  exact hf m

/-- The first map of an exact sequence, with codomain restricted to the
kernel of the second map. -/
def kernelLift (i : M →ₗ[B] N) (p : N →ₗ[B] P)
    (hex : LinearMap.range i = LinearMap.ker p) : M →ₗ[B] LinearMap.ker p :=
  i.codRestrict (LinearMap.ker p) (fun m => hex ▸ LinearMap.mem_range_self i m)

@[simp]
lemma kernelLift_subtype (i : M →ₗ[B] N) (p : N →ₗ[B] P)
    (hex : LinearMap.range i = LinearMap.ker p) :
    (LinearMap.ker p).subtype.comp (kernelLift i p hex) = i :=
  rfl

/-- All-module acyclicity makes invariants exact also for sequences whose
first map need not be injective. -/
lemma invariantsMap_exact_of_acyclic
    (hE : RingEtaleEquivalenceRelation t)
    (hacyclic : ∀ (K : Type v) [AddCommGroup K] [Module B K]
      (θK : GroupoidCoaction t K), θK.IsAcyclic)
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (θP : GroupoidCoaction t P) (i : M →ₗ[B] N) (p : N →ₗ[B] P)
    (hi : θM.IsHom θN i) (hp : θN.IsHom θP p)
    (hex : LinearMap.range i = LinearMap.ker p) :
    LinearMap.range (θM.invariantsMap θN i hi) =
      LinearMap.ker (θN.invariantsMap θP p hp) := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  let θK := kernel hE θN θP p hp
  have hsub : θK.IsHom θN (LinearMap.ker p).subtype :=
    kernel_subtype_isHom hE θN θP p hp
  let iK := kernelLift i p hex
  have hiK : θM.IsHom θK iK :=
    hsub.of_comp_injective (LinearMap.ker p).subtype_injective hi
  have hsurj : Function.Surjective iK := by
    intro k
    have hk : (k : N) ∈ LinearMap.range i := by
      rw [hex]
      exact k.property
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hk
    exact ⟨m, Subtype.ext hm⟩
  have hinv := invariantsMap_surjective hE hacyclic θM θK iK hiK hsurj
  ext n
  constructor
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    change p (i (m : M)) = 0
    exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self i m)
  · intro hn
    have hpn : p (n : N) = 0 := congrArg Subtype.val hn
    let k : θK.invariantSubmodule :=
      ⟨⟨n, hpn⟩, (hsub.mem_invariants_iff
        (LinearMap.ker p).subtype_injective _).mp n.property⟩
    obtain ⟨m, hm⟩ := hinv k
    exact ⟨m, Subtype.ext (congrArg
      (fun x : θK.invariantSubmodule => ((x : LinearMap.ker p) : N)) hm)⟩

end Langlands.AlgebraicGeometry.GroupoidCoaction
