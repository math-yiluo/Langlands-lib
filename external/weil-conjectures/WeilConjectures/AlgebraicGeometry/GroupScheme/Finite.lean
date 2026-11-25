/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.RingTheory.HopfAlgebra.Etale

/-!
# Finite group schemes over a field

A finite group scheme over a field `K` is an object `G` of `Over (Spec (.of K))` equipped with
`CategoryTheory.GrpObj G` whose structure morphism `G.hom` is finite; its *order* is
`G.hom.finrankΓ = dim_K Γ(G, 𝒪_G)`. This file records the basic structural facts about such
group schemes that the abelian-variety block of the blueprint uses: the order of a connected
one is a power of the characteristic, one whose order is prime to the characteristic is étale,
and a finite étale group scheme over an algebraically closed field has exactly `|G|` rational
points, insensitive to enlarging the base field.

## Main statements

- `AlgebraicGeometry.exists_hopfAlgebra_iso`: a finite group scheme over `K` is the spectrum of a
  finite-dimensional commutative Hopf algebra.
- `AlgebraicGeometry.exists_finrankΓ_eq_pow`: a connected finite group scheme over a field of
  characteristic `p > 0` has order a power of `p`.
- `AlgebraicGeometry.etale_of_not_dvd_finrankΓ`: a finite group scheme whose order is prime to
  the characteristic is étale.
- `AlgebraicGeometry.card_points_eq_finrankΓ`: a finite étale group scheme over an algebraically
  closed field `K` has exactly `|G|` points over `K`.
- `AlgebraicGeometry.bijective_toUnit_comp`: base change of such a `G` to an algebraically
  closed extension `K'` is a bijection on points.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- A finite group scheme `G` over a field `K` is the spectrum of a finite-dimensional commutative
Hopf algebra `H` over `K`, and its order is `dim_K H`. -/
theorem exists_hopfAlgebra_iso (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra K H) (e : Spec (.of H) ≅ G.left),
      e.hom ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap K H)) ∧
        FiniteDimensional K H ∧ G.hom.finrankΓ = Module.finrank K H := by
  have : IsAffine G.left := isAffine_of_isAffineHom G.hom
  obtain ⟨H, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of K) (G := Grp.mk G)).2 ‹_›
  let e' : Spec (.of H.unop) ≅ G.left := (Grp.forget _ ⋙ Over.forget _).mapIso e
  have he : e'.hom ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap K H.unop)) :=
    Over.w e.hom.hom.hom
  refine ⟨H.unop, inferInstance, inferInstance, e', he, ?_, ?_⟩
  · have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K H.unop))) := by
      rw [← he]
      infer_instance
    rw [IsFinite.SpecMap_iff] at this
    exact RingHom.finite_algebraMap.1 this
  · rw [Scheme.Hom.finrankΓ_eq_of_iso G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K H.unop))) e'.symm (Iso.refl _)
      (by rw [Iso.refl_hom, Spec.map_id, Category.comp_id, ← he, Iso.symm_hom,
        Iso.inv_hom_id_assoc])]
    exact Scheme.Hom.finrankΓ_SpecMap K H.unop

/-- Blueprint `proposition-multiplication-n--2`: Connected finite group schemes have `p`-power order

Let `G` be a finite group scheme over a field `K` of characteristic `p > 0`. If `G` is
connected, then its order `|G| = dim_K Γ(G, 𝒪_G)` is a power of `p`.

`G` is the spectrum of a finite-dimensional commutative Hopf algebra `H`, which is local since
`Spec H` is connected; conclude by `Bialgebra.exists_finrank_eq_pow`. This also proves blueprint
`proposition-multiplication-n--2`. -/
theorem exists_finrankΓ_eq_pow (p : ℕ) [Fact p.Prime] [CharP K p]
    (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] [ConnectedSpace G.left] :
    ∃ r : ℕ, G.hom.finrankΓ = p ^ r := by
  obtain ⟨H, _, _, e, -, _, hfin⟩ := exists_hopfAlgebra_iso G
  have : IsArtinianRing H := .of_finite K H
  have : ConnectedSpace (PrimeSpectrum H) :=
    (Scheme.homeoOfIso e.symm).surjective.connectedSpace (Scheme.homeoOfIso e.symm).continuous
  have : Subsingleton (PrimeSpectrum H) := subsingleton_of_preconnected_totallyDisconnected
  have : Nontrivial H := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  have : IsLocalRing H := .of_unique_max_ideal <| by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal H
    exact ⟨M, hM, fun N hN ↦ congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (⟨N, hN.isPrime⟩ : PrimeSpectrum H) ⟨M, hM.isPrime⟩)⟩
  rw [hfin]
  exact Bialgebra.exists_finrank_eq_pow K H p

/-- Blueprint `proposition-multiplication-n--2`: Group schemes of order prime to `p` are étale

Let `G` be a finite group scheme over a field `K` of characteristic `p`, of order `m`. If
`p ∤ m` — which for `p = 0` just says `m ≠ 0` — then `G` is étale over `K`. This also proves
blueprint `proposition-multiplication-n--2`.

`G` is the spectrum of a finite-dimensional commutative Hopf algebra `H` of dimension `m`, which
is étale by `HopfAlgebra.etale_of_not_dvd_finrank`. -/
theorem etale_of_not_dvd_finrankΓ (p : ℕ) [CharP K p] (G : Over (Spec (.of K))) [GrpObj G]
    [IsFinite G.hom] (hp : ¬ p ∣ G.hom.finrankΓ) :
    Etale G.hom := by
  obtain ⟨H, _, _, e, he, _, hfin⟩ := exists_hopfAlgebra_iso G
  have := HopfAlgebra.etale_of_not_dvd_finrank K H p (hfin ▸ hp)
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K H))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 this
  rw [← he] at this
  exact (MorphismProperty.cancel_left_of_respectsIso @Etale e.hom G.hom).1 this

/-- `Spec K`, viewed over itself through `Spec` of `algebraMap K K`, is the terminal object of
`Over (Spec K)`. -/
noncomputable def specAlgebraMapSelfIso :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K))) ≅ 𝟙_ (Over (Spec (.of K))) :=
  (Over.isoMk (Iso.refl (Spec (.of K))) ((Category.comp_id _).trans (Spec.map_id (.of K)).symm) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K))) ≅ Over.mk (𝟙 (Spec (.of K)))) ≪≫
    Over.mkIdTerminal.uniqueUpToIso isTerminalTensorUnit

/-- The `K`-points of an affine `K`-scheme `G` are the `K`-algebra homomorphisms
`Γ(G, ⊤) →ₐ[K] K`. -/
noncomputable def pointsEquivAlgHom (G : Over (Spec (.of K))) [IsAffine G.left] :
    letI := G.hom.ΓAlgebra
    (𝟙_ (Over (Spec (.of K))) ⟶ G) ≃ (Γ(G.left, ⊤) →ₐ[K] K) :=
  specAlgebraMapSelfIso.symm.homCongr (Iso.refl G) |>.trans (G.hom.overHomEquivAlgHom K)

/-- Blueprint `proposition-integral-tate-module`: Points of finite étale group schemes

A finite étale group scheme `G` of order `m` over an algebraically closed field `K` has exactly
`m` points with values in `K`. This is the first half of blueprint
`proposition-integral-tate-module`.

The proof identifies the points with `K`-algebra homomorphisms `Γ(G, ⊤) →ₐ[K] K`; as `Γ(G, ⊤)`
is an étale `K`-algebra it is a product of `m` copies of `K`, so there are `m` of them. -/
theorem card_points_eq_finrankΓ [IsAlgClosed K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsFinite G.hom] [Etale G.hom] :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ G) = G.hom.finrankΓ := by
  have : IsAffine G.left := isAffine_of_isAffineHom G.hom
  let := G.hom.ΓAlgebra
  have := G.hom.etale_ΓAlgebra
  rw [Nat.card_congr (pointsEquivAlgHom G), Algebra.Etale.natCard_algHom_eq_finrank]
  rfl

/-- Blueprint `proposition-integral-tate-module`: Points of finite étale group schemes

Let `G` be a finite étale group scheme over an algebraically closed field `K` and let `K'` be an
algebraically closed extension of `K`. Then base change along `K ⊆ K'`, that is precomposition
with the structure morphism of `Spec K'` over `K`, is a bijection `G(K) ≃ G(K')`. This is the
second half of blueprint `proposition-integral-tate-module`.

Under the identification of points with `K`-algebra homomorphisms out of `Γ(G, ⊤)`, the map is
composition with `K → K'`: it is injective, and both sides have `|G|` elements. -/
theorem bijective_toUnit_comp [IsAlgClosed K] {K' : Type u} [Field K'] [Algebra K K']
    [IsAlgClosed K'] (G : Over (Spec (.of K))) [GrpObj G] [IsFinite G.hom] [Etale G.hom] :
    Function.Bijective (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ G ↦
      toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s) := by
  have : IsAffine G.left := isAffine_of_isAffineHom G.hom
  let := G.hom.ΓAlgebra
  have := G.hom.etale_ΓAlgebra
  have := Algebra.FormallyUnramified.finite_of_free K Γ(G.left, ⊤)
  let ψ : (Γ(G.left, ⊤) →ₐ[K] K) → (Γ(G.left, ⊤) →ₐ[K] K') := (Algebra.ofId K K').comp
  have hψ : Function.Bijective ψ := by
    have hinj : Function.Injective ψ := fun g₁ g₂ h ↦
      AlgHom.ext fun x ↦ (algebraMap K K').injective (DFunLike.congr_fun h x)
    refine hinj.bijective_of_nat_card_le ?_
    rw [Algebra.Etale.natCard_algHom_eq_finrank, Algebra.Etale.natCard_algHom_eq_finrank]
  have key : (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ G ↦
      toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s) =
      (G.hom.overHomEquivAlgHom K').symm ∘ ψ ∘ pointsEquivAlgHom G := by
    ext1 s
    refine (Equiv.eq_symm_apply _).2 ?_
    have hv : (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫
        specAlgebraMapSelfIso.inv).left = Spec.map (CommRingCat.ofHom (algebraMap K K')) := by
      have := Over.w (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫
        specAlgebraMapSelfIso.inv)
      exact ((Category.comp_id _).symm.trans
        (congrArg (_ ≫ ·) (Spec.map_id (.of K)).symm)).trans this
    have := G.hom.overHomEquivAlgHom_comp _ hv (specAlgebraMapSelfIso.hom ≫ s)
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at this
    exact this
  rw [key]
  exact (Equiv.bijective _).comp (hψ.comp (Equiv.bijective _))

end AlgebraicGeometry
