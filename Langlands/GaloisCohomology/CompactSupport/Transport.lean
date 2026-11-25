import Langlands.GaloisCohomology.CompactSupport.DualityMap
import Langlands.GaloisCohomology.CompactSupport.Internal.ConeHomotopy
import Langlands.GaloisCohomology.CompactSupport.OpenSubgroupCup

/-!
# Transport of cohomology with compact support along isomorphisms

Let `θ : G ≃ₜ* G'` be an isomorphism of topological groups, `(φ_i : H_i →ₜ* G)_{i ∈ ι}` and
`(φ'_j : H'_j →ₜ* G')_{j ∈ ι'}` two families, `e : ι ≃ ι'` a bijection of the index sets and
`ψ_i : H_i ≃ₜ* H'_{e i}` isomorphisms with `θ ∘ φ_i = φ'_{e i} ∘ ψ_i`. A morphism
`f : Res_θ A' → A` from a `G'`-module to a `G`-module induces maps of cochains compatible with the
localizations (`localRes_transportLocal`), hence a map of cohomology with compact support
`compactTransport : H_cⁿ(G', A') → H_cⁿ(G, A)`, compatible with `H_c → H` and with cup products
(`compactTransport_compactCupRes`). When `f` is an isomorphism, so is `compactTransport`
(`compactTransportIso`), by the five lemma for mapping cocones.

This is used to identify the cohomology with compact support of an open subgroup of `G_S`, with the
Mackey family of local groups, with that of the Galois group `G_{S_L}(L)` of its fixed field.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory MonoidalCategory Langlands.ProfiniteCohomology

universe u

noncomputable section

section Transport

variable {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, Group (H' j)] [∀ j, TopologicalSpace (H' j)] [∀ j, IsTopologicalGroup (H' j)]
  (φ : ∀ i, H i →ₜ* G) (φ' : ∀ j, H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι')
  (ψ : ∀ i, H i ≃ₜ* H' (e i)) (hcomm : ∀ i h, θ (φ i h) = φ' (e i) (ψ i h))

section Cochains

variable {A' : Rep.{u} k G'} [IsSmoothRep A'] {A : Rep.{u} k G} [IsSmoothRep A]
  (f : Rep.res (θ : G →* G') A' ⟶ A)

/-- The local coefficient map at `i` induced by `f`. -/
def transportLocalMor (i : ι) :
    Rep.res (ψ i : H i →* H' (e i)) (Rep.res (φ' (e i) : H' (e i) →* G') A') ⟶
      Rep.res (φ i : H i →* G) A :=
  Rep.ofHom ⟨f.hom.toLinearMap, fun h => LinearMap.ext fun a => by
    change f.hom (A'.ρ (φ' (e i) (ψ i h)) a) = A.ρ (φ i h) (f.hom a)
    rw [← hcomm]
    exact Rep.hom_comm_apply f (φ i h) a⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, IsTopologicalGroup (H' j)] [IsSmoothRep A'] [IsSmoothRep A] in
theorem transportLocalMor_hom_apply (i : ι) (a : A') :
    (transportLocalMor φ φ' θ e ψ hcomm f i).hom a = f.hom a :=
  rfl

/-- The map of global cochains induced by `f` along `θ`. -/
abbrev transportGlobal : cochains A' ⟶ cochains A :=
  cochainsMap (θ : G →ₜ* G') f

/-- The map of local cochains induced by `f`. -/
def transportLocal :
    piComplex (fun j => cochains (Rep.res (φ' j : H' j →* G') A')) ⟶
      piComplex (fun i => cochains (Rep.res (φ i : H i →* G) A)) :=
  piLift fun i => piProj (fun j => cochains (Rep.res (φ' j : H' j →* G') A')) (e i) ≫
    cochainsMap (ψ i : H i →ₜ* H' (e i)) (transportLocalMor φ φ' θ e ψ hcomm f i)

theorem localRes_transportLocal :
    localRes φ' A' (fun j => Rep.res (φ' j : H' j →* G') A') (fun _ => 𝟙 _) ≫
        transportLocal φ φ' θ e ψ hcomm f =
      transportGlobal θ f ≫ localRes φ A (fun i => Rep.res (φ i : H i →* G) A) (fun _ => 𝟙 _) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
    funext fun i => cochainOf_injective (funext fun σ => ?_))
  change f.hom (cochainOf A' x (⇑(φ' (e i)) ∘ ⇑(ψ i) ∘ σ)) = f.hom (cochainOf A' x (⇑θ ∘ ⇑(φ i) ∘ σ))
  congr 2
  funext j
  exact (hcomm i (σ j)).symm

/-- The map of cochains with compact support induced by `f`. -/
def compactTransportCochains :
    compactSupportCochains φ' A' (fun j => Rep.res (φ' j : H' j →* G') A') (fun _ => 𝟙 _) ⟶
      compactSupportCochains φ A (fun i => Rep.res (φ i : H i →* G) A) (fun _ => 𝟙 _) :=
  mappingCoconeNat.mapOfHomotopy (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm f))

/-- The map `H_cⁿ(G', A') → H_cⁿ(G, A)` induced by `f`. -/
def compactTransport (n : ℕ) :
    compactSupportCohomologyRes φ' A' n ⟶ compactSupportCohomologyRes φ A n :=
  HomologicalComplex.homologyMap (compactTransportCochains φ φ' θ e ψ hcomm f) n

theorem compactTransport_compactToGlobal (n : ℕ) :
    compactTransport φ φ' θ e ψ hcomm f n ≫ compactToGlobal φ A _ (fun _ => 𝟙 _) n =
      compactToGlobal φ' A' _ (fun _ => 𝟙 _) n ≫ map (θ : G →ₜ* G') f n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
      (mappingCoconeNat.mapOfHomotopy_fst _)).trans (HomologicalComplex.homologyMap_comp _ _ n))

/-- The map of local cohomology groups induced by `f`. -/
def transportLocalCohomology (n : ℕ) :
    ModuleCat.of k (∀ j, cohomology (Rep.res (φ' j : H' j →* G') A') n) ⟶
      ModuleCat.of k (∀ i, cohomology (Rep.res (φ i : H i →* G) A) n) :=
  ModuleCat.ofHom (LinearMap.pi fun i => (map (ψ i : H i →ₜ* H' (e i))
    (transportLocalMor φ φ' θ e ψ hcomm f i) n).hom.comp (LinearMap.proj (e i)))

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem homologyMap_transportLocal_localCohomologyIso (n : ℕ) :
    HomologicalComplex.homologyMap (transportLocal φ φ' θ e ψ hcomm f) n ≫
        (localCohomologyIso (fun i => Rep.res (φ i : H i →* G) A) n).hom =
      (localCohomologyIso (fun j => Rep.res (φ' j : H' j →* G') A') n).hom ≫
        transportLocalCohomology φ φ' θ e ψ hcomm f n := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => funext fun i => ?_)
  change (HomologicalComplex.homologyMap (piProj _ i) n).hom
      ((HomologicalComplex.homologyMap (transportLocal φ φ' θ e ψ hcomm f) n).hom z) =
    (map (ψ i : H i →ₜ* H' (e i)) (transportLocalMor φ φ' θ e ψ hcomm f i) n).hom
        ((HomologicalComplex.homologyMap (piProj _ (e i)) n).hom z)
  rw [hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm z,
    transportLocal, piLift_piProj, HomologicalComplex.homologyMap_comp]
  rfl

end Cochains

section Iso

variable {A' : Rep.{u} k G'} [IsSmoothRep A'] {A : Rep.{u} k G} [IsSmoothRep A]
  (f : Rep.res (θ : G →* G') A' ≅ A)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, IsTopologicalGroup (H' j)] [IsSmoothRep A'] [IsSmoothRep A] in
theorem bijective_transportLocalMor (i : ι) :
    Function.Bijective (transportLocalMor φ φ' θ e ψ hcomm f.hom i).hom := by
  refine Function.bijective_iff_has_inverse.2 ⟨f.inv.hom, fun a => ?_, fun a => ?_⟩
  · exact Rep.inv_hom_apply _ _ f a
  · exact Rep.hom_inv_apply _ _ f a

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem transportLocalCohomology_bijective (n : ℕ) :
    Function.Bijective (transportLocalCohomology φ φ' θ e ψ hcomm f.hom n).hom := by
  have hc : ∀ i, Function.Bijective (map (ψ i : H i →ₜ* H' (e i))
      (transportLocalMor φ φ' θ e ψ hcomm f.hom i) n).hom := fun i => by
    have := isIso_map_of_mulEquiv (ψ i).toMulEquiv (ψ i).continuous (ψ i).symm.continuous
      (transportLocalMor φ φ' θ e ψ hcomm f.hom i) (bijective_transportLocalMor φ φ' θ e ψ hcomm f i) n
    exact (ConcreteCategory.isIso_iff_bijective _).1 this
  have h1 : Function.Bijective (fun ξ : ∀ j, cohomology (Rep.res (φ' j : H' j →* G') A') n =>
      fun i => ξ (e i)) :=
    (Equiv.piCongrLeft (fun j => cohomology (Rep.res (φ' j : H' j →* G') A') n) e).symm.bijective
  exact (Function.Bijective.piMap hc).comp h1

theorem isIso_homologyMap_transportGlobal (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (transportGlobal θ f.hom) n) :=
  isIso_map_of_mulEquiv θ.toMulEquiv θ.continuous θ.symm.continuous f.hom
    (Function.bijective_iff_has_inverse.2 ⟨f.inv.hom, fun a => Rep.inv_hom_apply _ _ f a,
      fun a => Rep.hom_inv_apply _ _ f a⟩) n

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem isIso_homologyMap_transportLocal (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (transportLocal φ φ' θ e ψ hcomm f.hom) n) := by
  have hb := transportLocalCohomology_bijective φ φ' θ e ψ hcomm f n
  have : IsIso (transportLocalCohomology φ φ' θ e ψ hcomm f.hom n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have h := homologyMap_transportLocal_localCohomologyIso φ φ' θ e ψ hcomm f.hom n
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  infer_instance

theorem isIso_compactTransport (n : ℕ) : IsIso (compactTransport φ φ' θ e ψ hcomm f.hom n) :=
  mappingCoconeNat.isIso_homologyMap_mapOfHomotopy _
    (isIso_homologyMap_transportGlobal θ f) (isIso_homologyMap_transportLocal φ φ' θ e ψ hcomm f) n

/-- The isomorphism `H_cⁿ(G', A') ≅ H_cⁿ(G, A)` induced by an isomorphism `f`. -/
def compactTransportIso (n : ℕ) :
    compactSupportCohomologyRes φ' A' n ≅ compactSupportCohomologyRes φ A n :=
  @asIso _ _ _ _ (compactTransport φ φ' θ e ψ hcomm f.hom n)
    (isIso_compactTransport φ φ' θ e ψ hcomm f n)

theorem compactTransportIso_hom (n : ℕ) :
    (compactTransportIso φ φ' θ e ψ hcomm f n).hom = compactTransport φ φ' θ e ψ hcomm f.hom n :=
  rfl

end Iso

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, IsTopologicalGroup (H' j)] in
theorem homotopy_ofEq_hom_apply {C D : CochainComplex (ModuleCat.{u} k) ℕ} {f g : C ⟶ D} (h : f = g)
    (i j : ℕ) (x : C.X i) : ((Homotopy.ofEq h).hom i j).hom x = 0 :=
  rfl

section CupGeneral

variable {K₁ K₂ : Type u} [Group K₁] [TopologicalSpace K₁] [IsTopologicalGroup K₁] [Group K₂]
  [TopologicalSpace K₂] [IsTopologicalGroup K₂] (ι₀ : K₁ →ₜ* K₂)
  {A B C : Rep.{u} k K₂} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {A₁ B₁ C₁ : Rep.{u} k K₁} [IsSmoothRep A₁] [IsSmoothRep B₁] [IsSmoothRep C₁]
  (a : Rep.res (ι₀ : K₁ →* K₂) A ⟶ A₁) (b : Rep.res (ι₀ : K₁ →* K₂) B ⟶ B₁)
  (c : Rep.res (ι₀ : K₁ →* K₂) C ⟶ C₁) (μ : A ⊗ B ⟶ C) (μ₁ : A₁ ⊗ B₁ ⟶ C₁)
  (hμ : (Rep.resFunctor (ι₀ : K₁ →* K₂)).map μ ≫ c = resTensorHom (ι₀ : K₁ →* K₂) a b ≫ μ₁)

include hμ in
/-- Maps of cochains along a homomorphism are compatible with cup products of cochains. -/
theorem cochainsMap_cupPairingCochains {r s n : ℕ} (h : r + s = n) (x : (cochains A).X r)
    (z : (cochains B).X s) :
    ((cochainsMap ι₀ c).f n).hom (cupPairingCochains μ h x z) =
      cupPairingCochains μ₁ h (((cochainsMap ι₀ a).f r).hom x)
        (((cochainsMap ι₀ b).f s).hom z) := by
  apply cochainOf_injective
  funext σ
  change c.hom (μ.hom (cupCochain h (cochainOf A x) (cochainOf B z) (⇑ι₀ ∘ σ))) =
    μ₁.hom (cupCochain h (fun τ => a.hom (cochainOf A x (⇑ι₀ ∘ τ)))
      (fun τ => b.hom (cochainOf B z (⇑ι₀ ∘ τ))) σ)
  rw [cupCochain_apply, cupCochain_apply, ← Rep.hom_comm_apply, partialProd_comp_monoidHom]
  exact congrArg (fun F : Rep.res (ι₀ : K₁ →* K₂) (A ⊗ B) ⟶ C₁ => F.hom
    ((cochainOf A x fun i => (⇑ι₀ ∘ σ) ⟨i, by omega⟩) ⊗ₜ[k]
      B.ρ (ι₀ (Fin.partialProd σ ⟨r, by omega⟩))
        (cochainOf B z fun j => (⇑ι₀ ∘ σ) ⟨r + j, by omega⟩) :
      (A ⊗ B : Rep k K₂))) hμ

end CupGeneral

section Cup

variable {A' B' C' : Rep.{u} k G'} [IsSmoothRep A'] [IsSmoothRep B'] [IsSmoothRep C']
  {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  (fA : Rep.res (θ : G →* G') A' ⟶ A) (fB : Rep.res (θ : G →* G') B' ⟶ B)
  (fC : Rep.res (θ : G →* G') C' ⟶ C) (μ' : A' ⊗ B' ⟶ C') (μ : A ⊗ B ⟶ C)
  (hμ : (Rep.resFunctor (θ : G →* G')).map μ' ≫ fC = resTensorHom (θ : G →* G') fA fB ≫ μ)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, IsTopologicalGroup (H' j)] [IsSmoothRep A'] [IsSmoothRep B'] [IsSmoothRep C']
  [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C] in
include hμ in
theorem transportLocalMor_pairing (i : ι) :
    (Rep.resFunctor (ψ i : H i →* H' (e i))).map
        ((Rep.resFunctor (φ' (e i) : H' (e i) →* G')).map μ') ≫
        transportLocalMor φ φ' θ e ψ hcomm fC i =
      resTensorHom (ψ i : H i →* H' (e i)) (transportLocalMor φ φ' θ e ψ hcomm fA i)
        (transportLocalMor φ φ' θ e ψ hcomm fB i) ≫ (Rep.resFunctor (φ i : H i →* G)).map μ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro a b
  change fC.hom (μ'.hom ((a : A') ⊗ₜ[k] (b : B') : (A' ⊗ B' : Rep k G'))) =
    μ.hom ((fA.hom a ⊗ₜ[k] fB.hom b : (A ⊗ B : Rep k G)))
  exact congrArg (fun F : Rep.res (θ : G →* G') (A' ⊗ B') ⟶ C =>
    F.hom ((a : A') ⊗ₜ[k] (b : B') : (A' ⊗ B' : Rep k G'))) hμ

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hμ in
theorem transportLocal_pi_cup {r s n : ℕ} (hh : r + s = n)
    (y₀ : (piComplex fun j => cochains (Rep.res (φ' j : H' j →* G') A')).X r)
    (w₀ : (piComplex fun j => cochains (Rep.res (φ' j : H' j →* G') B')).X s) :
    ((transportLocal φ φ' θ e ψ hcomm fC).f n).hom
        ((LeibnizPairing.pi fun j => cupLeibniz (A := Rep.res (φ' j : H' j →* G') A')
          (B := Rep.res (φ' j : H' j →* G') B') (C := Rep.res (φ' j : H' j →* G') C')
          ((Rep.resFunctor (φ' j : H' j →* G')).map μ')).μ hh y₀ w₀) =
      (LeibnizPairing.pi fun i => cupLeibniz (A := Rep.res (φ i : H i →* G) A)
        (B := Rep.res (φ i : H i →* G) B) (C := Rep.res (φ i : H i →* G) C)
        ((Rep.resFunctor (φ i : H i →* G)).map μ)).μ hh
        (((transportLocal φ φ' θ e ψ hcomm fA).f r).hom y₀)
        (((transportLocal φ φ' θ e ψ hcomm fB).f s).hom w₀) := by
  funext i
  exact cochainsMap_cupPairingCochains (ψ i : H i →ₜ* H' (e i))
    (A := Rep.res (φ' (e i) : H' (e i) →* G') A') (B := Rep.res (φ' (e i) : H' (e i) →* G') B')
    (C := Rep.res (φ' (e i) : H' (e i) →* G') C') (A₁ := Rep.res (φ i : H i →* G) A)
    (B₁ := Rep.res (φ i : H i →* G) B) (C₁ := Rep.res (φ i : H i →* G) C)
    (transportLocalMor φ φ' θ e ψ hcomm fA i) (transportLocalMor φ φ' θ e ψ hcomm fB i)
    (transportLocalMor φ φ' θ e ψ hcomm fC i) ((Rep.resFunctor (φ' (e i) : H' (e i) →* G')).map μ')
    ((Rep.resFunctor (φ i : H i →* G)).map μ)
    (transportLocalMor_pairing φ φ' θ e ψ hcomm fA fB fC μ' μ hμ i) hh (y₀ (e i)) (w₀ (e i))

include hμ in
/-- `compactTransport` is compatible with cup products. -/
theorem compactTransport_compactCupRes {r s n : ℕ} (h : r + s = n)
    (y : compactSupportCohomologyRes φ' A' r) (x : cohomology B' s) :
    (compactTransport φ φ' θ e ψ hcomm fC n).hom (compactCupRes φ' μ' h y x) =
      compactCupRes φ μ h ((compactTransport φ φ' θ e ψ hcomm fA r).hom y)
        ((map (θ : G →ₜ* G') fB s).hom x) := by
  have hc := fun {r s n : ℕ} (hh : r + s = n) (x₀ : (cochains A').X r) (z₀ : (cochains B').X s) =>
    localRes_cupPairingCochains φ' μ'
      (Aᵥ := fun j => Rep.res (φ' j : H' j →* G') A') (Bᵥ := fun j => Rep.res (φ' j : H' j →* G') B')
      (Cᵥ := fun j => Rep.res (φ' j : H' j →* G') C')
      (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _)
      (fun j => (Rep.resFunctor (φ' j : H' j →* G')).map μ')
      (fun j => resFunctor_map_comp_id (φ' j : H' j →* G') _) hh x₀ z₀
  have hc' := fun {r s n : ℕ} (hh : r + s = n) (x₀ : (cochains A).X r) (z₀ : (cochains B).X s) =>
    localRes_cupPairingCochains φ μ
      (Aᵥ := fun i => Rep.res (φ i : H i →* G) A) (Bᵥ := fun i => Rep.res (φ i : H i →* G) B)
      (Cᵥ := fun i => Rep.res (φ i : H i →* G) C)
      (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _)
      (fun i => (Rep.resFunctor (φ i : H i →* G)).map μ)
      (fun i => resFunctor_map_comp_id (φ i : H i →* G) _) hh x₀ z₀
  exact mappingCoconeNat.homologyMap_mapOfHomotopy_coconeLeft
    (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm fA))
    (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm fC))
    (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm fB))
    (LeibnizPairing.pi fun j => cupLeibniz (A := Rep.res (φ' j : H' j →* G') A')
      (B := Rep.res (φ' j : H' j →* G') B') (C := Rep.res (φ' j : H' j →* G') C')
      ((Rep.resFunctor (φ' j : H' j →* G')).map μ'))
    (cupLeibniz μ')
    (LeibnizPairing.pi fun i => cupLeibniz (A := Rep.res (φ i : H i →* G) A)
      (B := Rep.res (φ i : H i →* G) B) (C := Rep.res (φ i : H i →* G) C)
      ((Rep.resFunctor (φ i : H i →* G)).map μ))
    (cupLeibniz μ) hc hc'
    (fun hh x₀ z₀ => cochainsMap_cupPairingCochains (θ : G →ₜ* G') fA fB fC μ' μ hμ hh x₀ z₀)
    (fun hh y₀ w₀ => transportLocal_pi_cup φ φ' θ e ψ hcomm fA fB fC μ' μ hμ hh y₀ w₀)
    (fun _ _ _ => by
      rw [homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply,
        LinearMap.map_zero₂, map_zero, smul_zero, add_zero])
    (fun _ _ _ => by rw [homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply, map_zero])
    (fun _ _ _ => by rw [homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply, LinearMap.map_zero₂])
    h y x

end Cup

end Transport

end

end Langlands.GaloisCohomology
