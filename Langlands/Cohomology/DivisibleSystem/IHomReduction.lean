import Langlands.Cohomology.DivisibleSystem.FreeReduction
import Langlands.Cohomology.DivisibleSystem.LeftExact
import Langlands.Representation.Induction.PermutationDual

/-!
# Hom into reductions: Harris's system `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all `m`."
Here `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` (p.311), which the published `reductionSystem ℓ L` models by the
cokernels `L / ℓ ^ m L` of multiplication by `ℓ ^ m`.

For representations `A` and `L` of a group `G` over a commutative ring `R`, with the underlying
`R`-module of `A` projective, this module shows that the internal Hom `Hom_R(A, -)`
(`Rep.ihom A`) commutes with reduction modulo `ℓ ^ m`:

* `ihom_map_surjective`, `epi_ihom_map`: `Hom_R(A, -)` preserves epimorphisms;
* `exists_pow_smul_of_ihom_map_reductionπ_eq_zero`, `ihomReductionComplex_exact`: the sequence
  `Hom_R(A, L) → Hom_R(A, L) → Hom_R(A, L / ℓ ^ m L)` (multiplication by `ℓ ^ m`, then
  composition with the projection) is exact, and its second map is an epimorphism;
* `ihomReductionIso`, `ihomReductionTowerIso`: hence `Hom_R(A, L) / ℓ ^ m ≅ Hom_R(A, L / ℓ ^ m L)`,
  compatibly with the projections (`ihomReductionIso_naturality`) and with the maps induced by
  `ℓ ^ (m - m')` (`ihomReductionIso_inclusion`);
* `mono_powSMul_ihom`: if multiplication by `ℓ` is injective on `L`, it is injective on
  `Hom_R(A, L)`.

For representations with carriers in the universe of `R`, `Hom_R(A, -)` preserves finite limits,
so `ihomReductionSystem ℓ A L`, the image of `reductionSystem ℓ L` under `Hom_R(A, -)`, is an
`ℓ`-divisible system with levels `Hom_R(A, L / ℓ ^ m L)`, and `reductionSystemIhomIso` identifies
it with the reduction system of `Hom_R(A, L)`. If moreover `G` is in the universe of `R` and
`Hom_R(A, L)` is free over `R[G]`, every level is free over `(R ⧸ (ℓ ^ m))[G]`
(`freeOverPowQuotient_ihom_reduction`). For Harris's modules
(`freeOverPowQuotient_permutation_ihom_reduction`,
`freeOverPowQuotient_subgroup_permutation_ihom_reduction`), `A` is the permutation
representation on `M[X]` for a free action on a finite set `X` (Harris's `C_p/H_p`, acted on by
`S(ẽ)/H_p`), `M` is finite free (Harris's `𝒪^M`) and `L` is free with the trivial action
(Harris's lattice `𝓛`).

The Lean target is `Hom_R(M[X], L / ℓ ^ m L)`; its identification with Harris's
`Hom_{𝒪_m}(𝒪_m[X]^M, 𝓛_m)` is not formalized. The definitions and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v

section IHom

variable {R : Type u} [CommRing R] {G : Type v} [Group G] (ℓ : ℕ) (A : Rep.{w} R G)

/-- `Hom_R(A, -)` sends a morphism `f` to composition with `f`. -/
lemma ihom_map_hom_apply {X Y : Rep.{w} R G} (f : X ⟶ Y) (φ : A →ₗ[R] X) (a : A) :
    (show A →ₗ[R] Y from ((Rep.ihom A).map f).hom φ) a = f.hom (φ a) :=
  rfl

/-- `Hom_R(A, -)` is additive. -/
instance ihom_additive : (Rep.ihom A).Additive where
  map_add {_ _ _ _} := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- If multiplication by `ℓ` is injective on `L`, it is injective on `Hom_R(A, L)`. -/
instance mono_powSMul_ihom (L : Rep.{w} R G) [Mono (powSMul ℓ 1 L)] :
    Mono (powSMul ℓ 1 ((Rep.ihom A).obj L)) :=
  (mono_powSMul_one_iff_isSMulRegular ℓ _).2 fun _ _ h => LinearMap.ext fun a =>
    (mono_powSMul_one_iff_isSMulRegular ℓ L).1 inferInstance (LinearMap.congr_fun h a)

variable (L : Rep.{w} R G)

/-- Multiplication by `ℓ ^ m` on `Hom_R(A, L)` followed by composition with the projection
`L ⟶ L / ℓ ^ m L` is zero. -/
lemma powSMul_comp_ihom_map_reductionπ (m : ℕ) :
    powSMul ℓ m ((Rep.ihom A).obj L) ≫ (Rep.ihom A).map (reductionπ ℓ L m) = 0 := by
  rw [← map_powSMul (Rep.ihom A), ← Functor.map_comp, powSMul_comp_reductionπ, Functor.map_zero]

/-- The short complex `Hom_R(A, L) → Hom_R(A, L) → Hom_R(A, L / ℓ ^ m L)` formed by
multiplication by `ℓ ^ m` and composition with the projection. -/
abbrev ihomReductionComplex (m : ℕ) : ShortComplex (Rep.{w} R G) :=
  ShortComplex.mk (powSMul ℓ m ((Rep.ihom A).obj L)) ((Rep.ihom A).map (reductionπ ℓ L m))
    (powSMul_comp_ihom_map_reductionπ ℓ A L m)

variable [Module.Projective R A]

/-- For `A` projective over `R`, composition with a surjective morphism `p` is surjective on
`Hom_R(A, -)`: lift along `p`. -/
lemma ihom_map_surjective {X Y : Rep.{w} R G} (p : X ⟶ Y) [Epi p] :
    Function.Surjective ((Rep.ihom A).map p).hom := fun ψ => by
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property p.hom.toLinearMap ψ
    ((Rep.epi_iff_surjective p).1 inferInstance)
  exact ⟨φ, hφ⟩

/-- For `A` projective over `R`, `Hom_R(A, -)` preserves epimorphisms. -/
instance epi_ihom_map {X Y : Rep.{w} R G} (p : X ⟶ Y) [Epi p] : Epi ((Rep.ihom A).map p) :=
  (Rep.epi_iff_surjective _).2 (ihom_map_surjective A p)

variable {A L} in
/-- A map `φ : A → L` whose composition with the projection `L ⟶ L / ℓ ^ m L` vanishes is
`ℓ ^ m ψ` for some `ψ : A → L`: `φ` lands in the image of `ℓ ^ m`, and `A` is projective. -/
lemma exists_pow_smul_of_ihom_map_reductionπ_eq_zero (m : ℕ) {φ : A →ₗ[R] L}
    (hφ : ((Rep.ihom A).map (reductionπ ℓ L m)).hom φ = 0) :
    ∃ ψ : A →ₗ[R] L, ((ℓ : R) ^ m) • ψ = φ := by
  have hex : (ShortComplex.mk (powSMul ℓ m L) (reductionπ ℓ L m)
      (powSMul_comp_reductionπ ℓ L m)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (reductionπIsCokernel ℓ L m)
  have hex' := ((ShortComplex.mk (powSMul ℓ m L) (reductionπ ℓ L m)
      (powSMul_comp_reductionπ ℓ L m)).exact_map_iff_of_faithful
    (forget₂ (Rep.{w} R G) (ModuleCat.{w} R))).mpr hex
  have h0 : (reductionπ ℓ L m).hom.toLinearMap ∘ₗ φ = 0 := hφ
  have hmem : ∀ a, φ a ∈ LinearMap.range (powSMul ℓ m L).hom.toLinearMap := fun a => by
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex' (φ a)
      (LinearMap.congr_fun h0 a)
    exact ⟨y, hy⟩
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property
    (powSMul ℓ m L).hom.toLinearMap.rangeRestrict (LinearMap.codRestrict _ φ hmem)
    (LinearMap.surjective_rangeRestrict _)
  refine ⟨ψ, LinearMap.ext fun a => ?_⟩
  have h := congrArg Subtype.val (LinearMap.congr_fun hψ a)
  rw [LinearMap.smul_apply, ← powSMul_hom_apply]
  exact h

/-- For `A` projective over `R`, the short complex `ihomReductionComplex ℓ A L m` is exact. -/
lemma ihomReductionComplex_exact (m : ℕ) : (ihomReductionComplex ℓ A L m).Exact := by
  apply ((ihomReductionComplex ℓ A L m).exact_map_iff_of_faithful
    (forget₂ (Rep.{w} R G) (ModuleCat.{w} R))).mp
  refine (ShortComplex.moduleCat_exact_iff _).mpr fun φ hφ => ?_
  obtain ⟨ψ, hψ⟩ := exists_pow_smul_of_ihom_map_reductionπ_eq_zero ℓ m hφ
  exact ⟨ψ, (powSMul_hom_apply ((Rep.ihom A).obj L) ψ).trans hψ⟩

/-- For `A` projective over `R`, `Hom_R(A, L) / ℓ ^ m ≅ Hom_R(A, L / ℓ ^ m L)`: composition
with the projection `L ⟶ L / ℓ ^ m L` identifies the cokernel of multiplication by `ℓ ^ m`. -/
def ihomReductionIso (m : ℕ) :
    (reductionTower ℓ ((Rep.ihom A).obj L)).obj (op m) ≅
      (Rep.ihom A).obj ((reductionTower ℓ L).obj (op m)) :=
  (reductionπIsCokernel ℓ _ m).coconePointUniqueUpToIso
    (ihomReductionComplex_exact ℓ A L m).gIsCokernel

/-- The projection onto `Hom_R(A, L) / ℓ ^ m` followed by `ihomReductionIso` is composition
with the projection `L ⟶ L / ℓ ^ m L`. -/
@[reassoc (attr := simp)]
lemma reductionπ_ihomReductionIso_hom (m : ℕ) :
    reductionπ ℓ ((Rep.ihom A).obj L) m ≫ (ihomReductionIso ℓ A L m).hom =
      (Rep.ihom A).map (reductionπ ℓ L m) :=
  (reductionπIsCokernel ℓ _ m).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- `ihomReductionIso` commutes with the projections `· / ℓ ^ m ⟶ · / ℓ ^ n` for `n ≤ m`. -/
lemma ihomReductionIso_naturality {m n : ℕ} (f : (op m : ℕᵒᵖ) ⟶ op n) :
    (reductionTower ℓ ((Rep.ihom A).obj L)).map f ≫ (ihomReductionIso ℓ A L n).hom =
      (ihomReductionIso ℓ A L m).hom ≫ (Rep.ihom A).map ((reductionTower ℓ L).map f) := by
  rw [← cancel_epi (reductionπ ℓ ((Rep.ihom A).obj L) m), reductionπ_map_assoc,
    reductionπ_ihomReductionIso_hom, reductionπ_ihomReductionIso_hom_assoc, ← Functor.map_comp,
    reductionπ_map]

/-- `ihomReductionIso` commutes with the maps `· / ℓ ^ m' ⟶ · / ℓ ^ m` induced by
multiplication by `ℓ ^ (m - m')`. -/
lemma ihomReductionIso_inclusion {m' m : ℕ} (h : m' < m) :
    reductionInclusion ℓ ((Rep.ihom A).obj L) h ≫ (ihomReductionIso ℓ A L m).hom =
      (ihomReductionIso ℓ A L m').hom ≫ (Rep.ihom A).map (reductionInclusion ℓ L h) := by
  rw [← cancel_epi (reductionπ ℓ ((Rep.ihom A).obj L) m'), reductionπ_inclusion_assoc,
    reductionπ_ihomReductionIso_hom, reductionπ_ihomReductionIso_hom_assoc, ← Functor.map_comp,
    reductionπ_inclusion, Functor.map_comp, map_powSMul]

/-- The isomorphisms `ihomReductionIso`, as an isomorphism of inverse systems
`{Hom_R(A, L) / ℓ ^ m} ≅ {Hom_R(A, L / ℓ ^ m L)}`. -/
def ihomReductionTowerIso :
    reductionTower ℓ ((Rep.ihom A).obj L) ≅ reductionTower ℓ L ⋙ Rep.ihom A :=
  NatIso.ofComponents (fun m => ihomReductionIso ℓ A L m.unop) fun {m n} f => by
    induction m using Opposite.rec with | op m =>
    induction n using Opposite.rec with | op n =>
    exact ihomReductionIso_naturality ℓ A L f

/-- The component of `ihomReductionTowerIso` at `m` is `ihomReductionIso`. -/
lemma ihomReductionTowerIso_hom_app (m : ℕ) :
    (ihomReductionTowerIso ℓ A L).hom.app (op m) = (ihomReductionIso ℓ A L m).hom :=
  rfl

end IHom

section System

variable {R : Type u} [CommRing R] {G : Type v} [Group G] (ℓ : ℕ) (A : Rep.{u} R G)

/-- For representations in the universe of `R`, `Hom_R(A, -)` is a right adjoint (to `A ⊗ -`),
so it preserves finite limits. -/
instance ihom_preservesFiniteLimits :
    PreservesFiniteLimits (Rep.ihom A : Rep.{u} R G ⥤ Rep.{u} R G) :=
  have : PreservesLimits (Rep.ihom A : Rep.{u} R G ⥤ Rep.{u} R G) :=
    (ihom.adjunction A).rightAdjoint_preservesLimits
  inferInstance

variable [Module.Projective R A] (L : Rep.{u} R G) [Mono (powSMul ℓ 1 L)]

/-- Harris's system `m ↦ Hom_R(A, L / ℓ ^ m L)`: the image of the reduction system of `L` under
`Hom_R(A, -)`, an `ℓ`-divisible system because `Hom_R(A, -)` preserves finite limits and, `A`
being projective, the epimorphisms `j`. -/
def ihomReductionSystem : DivisibleSystem (Rep.{u} R G) ℓ :=
  (reductionSystem ℓ L).mapLeftExact (Rep.ihom A) fun h =>
    have := (reductionSystem ℓ L).epi_projection h
    inferInstance

/-- The level `m` of `ihomReductionSystem ℓ A L` is `Hom_R(A, L / ℓ ^ m L)`. -/
lemma ihomReductionSystem_obj (m : ℕ) :
    (ihomReductionSystem ℓ A L).obj m = (Rep.ihom A).obj ((reductionTower ℓ L).obj (op m)) :=
  rfl

/-- The reduction system of `Hom_R(A, L)` is isomorphic to Harris's system
`m ↦ Hom_R(A, L / ℓ ^ m L)`. -/
def reductionSystemIhomIso :
    reductionSystem ℓ ((Rep.ihom A).obj L) ≅ ihomReductionSystem ℓ A L where
  hom := ⟨(ihomReductionTowerIso ℓ A L).hom, fun h => ihomReductionIso_inclusion ℓ A L h⟩
  inv := ⟨(ihomReductionTowerIso ℓ A L).inv, fun {m' m} h => by
    change (Rep.ihom A).map (reductionInclusion ℓ L h) ≫ (ihomReductionIso ℓ A L m).inv =
      (ihomReductionIso ℓ A L m').inv ≫ reductionInclusion ℓ ((Rep.ihom A).obj L) h
    rw [Iso.comp_inv_eq, Category.assoc, ihomReductionIso_inclusion, Iso.inv_hom_id_assoc]⟩
  hom_inv_id := hom_ext (ihomReductionTowerIso ℓ A L).hom_inv_id
  inv_hom_id := hom_ext (ihomReductionTowerIso ℓ A L).inv_hom_id

end System

section Free

variable {R : Type u} [CommRing R] {G : Type u} [Group G] {ℓ : ℕ} (A : Rep.{u} R G)
  [Module.Projective R A] (L : Rep.{u} R G)

/-- If `Hom_R(A, L)` is free over `R[G]`, then `Hom_R(A, L / ℓ ^ m L)` is free over
`(R ⧸ (ℓ ^ m))[G]`: it is the cokernel of `ℓ ^ m` on `Hom_R(A, L)`. -/
theorem freeOverPowQuotient_ihom_reduction
    [Module.Free (MonoidAlgebra R G) ((Rep.ihom A).obj L).ρ.asModule] (m : ℕ) :
    FreeOverPowQuotient ℓ m ((Rep.ihom A).obj ((reductionTower ℓ L).obj (op m))) :=
  freeOverPowQuotient_of_iso (ihomReductionIso ℓ A L m)
    (freeOverPowQuotient_cokernel_powSMul_of_free.{u, u, u} ℓ m ((Rep.ihom A).obj L))

/-- If `Hom_R(A, L)` is free over `R[G]`, every level of `ihomReductionSystem ℓ A L` is
`FreeOverPowQuotient`. -/
theorem freeOverPowQuotient_ihomReductionSystem_obj [Mono (powSMul ℓ 1 L)]
    [Module.Free (MonoidAlgebra R G) ((Rep.ihom A).obj L).ρ.asModule] (m : ℕ) :
    FreeOverPowQuotient ℓ m ((ihomReductionSystem ℓ A L).obj m) :=
  freeOverPowQuotient_ihom_reduction A L m

end Free

section Permutation

variable {R : Type u} [CommRing R] {ℓ : ℕ} {M L : Type u} [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] [AddCommGroup L] [Module R L] [Module.Free R L]

/-- Harris's freeness of `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`: if `G` acts freely on a finite set `X`,
`M` is finite free and `L` is free over `R` (both with the trivial action), then
`Hom_R(M[X], L / ℓ ^ m L)` is free over `(R ⧸ (ℓ ^ m))[G]`. -/
theorem freeOverPowQuotient_permutation_ihom_reduction {G : Type u} [Group G] {X : Type u}
    [MulAction G X] [Finite X] (h : ∀ x : X, MulAction.stabilizer G x = ⊥) (m : ℕ) :
    FreeOverPowQuotient ℓ m ((Rep.ihom (Rep.of (Induction.permutation R G X M))).obj
      ((reductionTower ℓ (Rep.of (Representation.trivial R G L))).obj (op m))) :=
  have : Module.Free (MonoidAlgebra R G) ((Rep.ihom (Rep.of (Induction.permutation R G X M))).obj
      (Rep.of (Representation.trivial R G L))).ρ.asModule :=
    Induction.linHom_permutation_asModule_free h
  freeOverPowQuotient_ihom_reduction _ _ m

/-- The case of Harris's proof of Prop. 4.10: for a subgroup `S` of a finite group `Q` (acting
on `Q` by left multiplication), `Hom_R(M[Q], L / ℓ ^ m L)` is free over `(R ⧸ (ℓ ^ m))[S]`. -/
theorem freeOverPowQuotient_subgroup_permutation_ihom_reduction {Q : Type u} [Group Q] [Finite Q]
    (S : Subgroup Q) (m : ℕ) :
    FreeOverPowQuotient ℓ m ((Rep.ihom (Rep.of (Induction.permutation R S Q M))).obj
      ((reductionTower ℓ (Rep.of (Representation.trivial R S L))).obj (op m))) :=
  freeOverPowQuotient_permutation_ihom_reduction IsCancelSMul.stabilizer_eq_bot m

end Permutation

end Langlands.Cohomology.DivisibleSystem
