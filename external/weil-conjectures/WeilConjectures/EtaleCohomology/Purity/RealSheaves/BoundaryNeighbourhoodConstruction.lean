/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.InertiaNeighbourhood
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodData
public import WeilConjectures.WeilSheaf.BoundaryStrictHenselization

/-!
# Construction of strictly henselian neighbourhoods of boundary points

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field `k₀`, `z` a boundary point with closed point `x`, `W` the chosen affine chart at `z` with
ring `R = Γ(C₀, W)`, `B` the integral closure of `R` in the separable closure `Ω` of `k(C)` and
`Q` a maximal ideal of `B` over `z`. The ring `A = B_Q^{I_Q}` of inertia invariants gives a
strictly henselian neighbourhood of the boundary point
(`AlgebraicGeometry.WeilGroup.BoundaryNeighbourhood`, blueprint
`lemma-boundary-stalk--1`), provided `Q` is *compatible* with the geometric point
`x̄ = geometricFiberPointOfFinitePoint x`: the reduction modulo `Q` of the embedding
`ι : k̄ ↪ Ω` of the geometric generic point (`AlgebraicGeometry.WeilGroup.genericEmb`) induces on
`κ(x)` the embedding `κ(x) ↪ k̄` of `x̄`
(`AlgebraicGeometry.WeilGroup.nonempty_boundaryNeighbourhood_of_compatible`). The Frobenius lift
is given by an element `σ_F` of the decomposition group of `Q` acting on `ι(k̄)` as the
`deg x`-th power of the geometric Frobenius.

* `Spec A ⟶ C̄` is given by `Spec A ⟶ Spec R ⟶ C₀` and `ι(k̄) ⊆ A`;
* the lift of `x̄` is `Spec` of the residue map `A ⟶ κ(A) ≅ k̄`;
* the punctured part is `Spec Ω^{I_Q}` (`AlgebraicGeometry.exists_iso_pullback_geometricFiberMap`);
* the Frobenius lift is `Spec σ_F|_A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped Pointwise

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale ProEtale

private lemma residueMap_commutes_of_section {A k : Type u} [CommRing A] [CommRing k]
    (ε : k →+* A) (r : A →+* k) (σ : A →+* A) (Φ : k →+* k)
    (hrε : r.comp ε = RingHom.id _) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a)
    (hσ : ∀ a, IsUnit (σ a) → IsUnit a) (hσε : ∀ y, σ (ε y) = ε (Φ y)) (a : A) :
    r (σ a) = Φ (r a) := by
  have h0 : r (a - ε (r a)) = 0 := by
    rw [map_sub, show r (ε (r a)) = r a from RingHom.congr_fun hrε _, sub_self]
  have h1 : ¬ IsUnit (σ (a - ε (r a))) := fun hu ↦ (hr _).1 h0 (hσ _ hu)
  have h2 : r (σ a - σ (ε (r a))) = 0 := by
    rw [← map_sub]
    exact (hr _).2 h1
  exact (sub_eq_zero.1 ((RingHom.map_sub r _ _).symm.trans h2)).trans
    ((congrArg r (hσε (r a))).trans (RingHom.congr_fun hrε (Φ (r a))))

private lemma specMap_commutes_of_ringHom {A B : CommRingCat.{u}}
    (σ : A ⟶ A) (τ : B ⟶ B) (f : A ⟶ B) (hf : f ≫ τ = σ ≫ f) :
    Spec.map τ ≫ Spec.map f = Spec.map f ≫ Spec.map σ := by
  rw [← Spec.map_comp, ← Spec.map_comp, hf]

private lemma specMap_comp_geometricFiberPoint_of_section
    {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
    {A : CommRingCat.{u}} (x : C.finitePoints)
    (ε : CommRingCat.of (AlgebraicClosure K) ⟶ A)
    (r : A ⟶ CommRingCat.of (AlgebraicClosure K)) (hrε : ε ≫ r = 𝟙 _)
    (h : Spec A ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (hproj : Spec.map r ≫ h ≫ (C ↘ Spec (.of K)).geometricFiberProj =
      (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x ≫
        (C ↘ Spec (.of K)).geometricFiberProj)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = Spec.map ε) :
    Spec.map r ≫ h = 𝟙 _ ≫ (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x := by
  rw [Category.id_comp]
  apply Scheme.Hom.geometricFiber_hom_ext
  · exact (Category.assoc _ _ _).trans hproj
  · rw [Category.assoc, hhalg, ← Spec.map_comp, hrε, Spec.map_id,
      Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure]

private lemma exists_proEtale_pointLift_of_residueMap
    {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
    {A : Type u} [CommRing A] [IsLocalRing A] (x : C.finitePoints)
    (h : Spec (.of A) ⟶ (C ↘ Spec (.of K)).geometricFiber) [WeaklyEtale h]
    (r : A →+* AlgebraicClosure K) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a)
    (hw : Spec.map (CommRingCat.ofHom r) ≫ h =
      𝟙 _ ≫ (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) :
    ∃ t : ProEt.mk (𝟙 (Spec (.of (AlgebraicClosure K)))) ⟶
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤
          ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x)).obj (ProEt.mk h),
      t.left ≫ pullback.fst h ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) =
        Spec.map (CommRingCat.ofHom r) ∧
      (t.left ≫ pullback.fst h ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x))
        (closedPoint (AlgebraicClosure K)) = closedPoint A := by
  let t : ProEt.mk (𝟙 (Spec (.of (AlgebraicClosure K)))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤
        ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x)).obj (ProEt.mk h) :=
    MorphismProperty.Over.homMk (pullback.lift (Spec.map (CommRingCat.ofHom r)) (𝟙 _) hw)
      (pullback.lift_snd _ _ _)
  have htl : t.left ≫ pullback.fst h ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) =
      Spec.map (CommRingCat.ofHom r) := pullback.lift_fst _ _ _
  refine ⟨t, htl, ?_⟩
  rw [htl]
  exact specMap_closedPoint_of_forall_eq_zero_iff r hr

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [C.Over (Spec (.of K))]
  [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] [IsIntegral C]
  (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] [j.IsOver (Spec (.of K))]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of K)))

omit [Finite K] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] in
/-- The structure map `k₀ ⟶ Ω` of the generic geometric point factors through the sections over
an affine open. -/
lemma genericStructHom_eq {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W]
    [IsDedekindDomain Γ(C, W)] :
    genericStructHom (U ↘ Spec (.of K)) j =
      (algebraMap Γ(C, W) Ω).comp (sectionsStructHom (k₀ := K) hW) := by
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (integralClosure Γ(C, W) Ω)
  have hfp : hW.fromSpec ≫ (C ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (sectionsStructHom (k₀ := K) hW)) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h1 : genericBasePoint j ≫ (U ↘ Spec (.of K)) = Spec.map (CommRingCat.ofHom
      ((algebraMap Γ(C, W) Ω).comp (sectionsStructHom (k₀ := K) hW))) := by
    rw [← comp_over j (Spec (.of K)), ← Category.assoc, pointOfAlgebra_comp_eq_specAtPrime j hW Q,
      specAtPrime, Category.assoc, Category.assoc, hfp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply Γ(C, W) (integralClosure Γ(C, W) Ω)
      (Localization.AtPrime Q), Ideal.atPrimeToField_algebraMap]
    rfl
  have h2 := spec_genericStructHom (U ↘ Spec (.of K)) j
  rw [h1] at h2
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)

omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] [IsIntegral C] in
/-- A ring endomorphism `σ` of `A` fixing the image of `R` and acting on `ε : k̄ ⟶ A` as `Frⁿ`
lifts the `n`-th power of the geometric Galois Frobenius along a morphism `h : Spec A ⟶ C̄`
given by `Spec A ⟶ Spec R ⟶ C` and `Spec ε`. -/
lemma specMap_comp_eq_comp_geometricGaloisFrobenius_pow {A R : CommRingCat.{u}}
    (g : Spec R ⟶ C) (alg : R ⟶ A) (σ : A ⟶ A) (hσalg : alg ≫ σ = alg)
    (ε : CommRingCat.of (AlgebraicClosure K) ⟶ A) (n : ℕ)
    (hσε : Spec.map σ ≫ Spec.map ε = Spec.map ε ≫ (specGeometricFrobenius K ^ n).asIso.hom)
    (h : Spec A ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (hhproj : h ≫ (C ↘ Spec (.of K)).geometricFiberProj = Spec.map alg ≫ g)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = Spec.map ε) :
    Spec.map σ ≫ h = h ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom := by
  apply Scheme.Hom.geometricFiber_hom_ext
  · rw [Category.assoc, Category.assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj, hhproj,
      ← Category.assoc, ← Spec.map_comp, hσalg]
  · rw [Category.assoc, Category.assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
      hhalg, hσε, ← Category.assoc, hhalg]

omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))] [ConnectedSpace C]
  [Smooth (C ↘ Spec (.of K))] in
private lemma comp_pullback_snd_eq_genericGeomPoint {A R : CommRingCat.{u}}
    (g : Spec R ⟶ C) (alg : R ⟶ A) (ε : CommRingCat.of (AlgebraicClosure K) ⟶ A)
    (ι : A ⟶ CommRingCat.of Ω) (ζ : R ⟶ CommRingCat.of Ω)
    (h : Spec A ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (hhproj : h ≫ (C ↘ Spec (.of K)).geometricFiberProj = Spec.map alg ≫ g)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = Spec.map ε)
    {T : Scheme.{u}} (p : Spec (.of Ω) ⟶ T) (e : T ⟶ pullback h j̄)
    (hfst : p ≫ e ≫ pullback.fst h j̄ = Spec.map ι)
    (hgen : genericBasePoint j ≫ j = Spec.map ζ ≫ g)
    (hι : alg ≫ ι = ζ) (hε : ε ≫ ι = CommRingCat.ofHom (genericEmb (U ↘ Spec (.of K)) j)) :
    p ≫ e ≫ pullback.snd h j̄ = genericGeomPoint (U ↘ Spec (.of K)) j := by
  apply Scheme.Hom.geometricFiber_hom_ext
  · rw [genericGeomPoint_geometricFiberProj, ← cancel_mono j, hgen]
    change p ≫ (e ≫ pullback.snd h j̄) ≫ _ ≫ j = _
    rw [← Scheme.Hom.geometricFiberMap_comp_geometricFiberProj j (comp_over j _)]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, hhproj, reassoc_of% hfst, ← Spec.map_comp_assoc, hι]
  · rw [genericGeomPoint_geometricFiberToAlgebraicClosure]
    change p ≫ (e ≫ pullback.snd h j̄) ≫ _ = _
    rw [← Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure j (comp_over j _)]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, hhalg, reassoc_of% hfst, ← Spec.map_comp, hε]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))] [ConnectedSpace C]
  [Smooth (C ↘ Spec (.of K))] in
/-- **The Frobenius lift on `Spec B_Q^{I_Q}`.** Let `σ_F` be an element of the decomposition
group of `Q` acting on the image of an embedding `ε₀ : k̄ ↪ Ω`, contained in `B_Q^{I_Q}` through
`ε`, as the `n`-th power of the geometric Frobenius, and `h : Spec B_Q^{I_Q} ⟶ C̄` given by
`Spec B_Q^{I_Q} ⟶ C` and `Spec ε`. Then `α = Spec σ_F|_{B_Q^{I_Q}}` lifts the `n`-th power of the
geometric Galois Frobenius of `C̄`, compatibly with `Spec r` and the generic point. -/
theorem exists_frobeniusLift_inertiaInvariants {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W]
    (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal]
    {σF : Gal(Ω/C.functionField)} (hσF : σF ∈ MulAction.stabilizer Gal(Ω/C.functionField) Q)
    (ε₀ : AlgebraicClosure K →+* Ω)
    (ε : AlgebraicClosure K →+* Ideal.inertiaInvariants C.functionField Q)
    (r : Ideal.inertiaInvariants C.functionField Q →+* AlgebraicClosure K)
    (hrε : r.comp ε = RingHom.id _) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a)
    (hε : ∀ y, Ideal.inertiaInvariantsToField _ Q (ε y) = ε₀ y) (n : ℕ)
    (hσFk : ∀ y, σF (ε₀ y) = ε₀ (letI := Fintype.ofFinite K
       (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ n) y))
    (h : Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
      (C ↘ Spec (.of K)).geometricFiber)
    (hhproj : h ≫ (C ↘ Spec (.of K)).geometricFiberProj = specInertiaInvariantsTo hW Q)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom ε)) :
    ∃ α : Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
        Spec (.of (Ideal.inertiaInvariants C.functionField Q)),
      α ≫ h = h ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom ∧
      (specGeometricFrobenius K ^ n).asIso.hom ≫ Spec.map (CommRingCat.ofHom r) =
        Spec.map (CommRingCat.ofHom r) ≫ α ∧
      Spec.map (CommRingCat.ofHom (σF : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom
        (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom) =
        Spec.map (CommRingCat.ofHom
          (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom) ≫ α := by
  let _ := Fintype.ofFinite K
  let Φ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ n
  have hσε (y : AlgebraicClosure K) :
      Ideal.inertiaInvariantsMap C.functionField Q hσF (ε y) = ε (Φ y) :=
    Ideal.injective_inertiaInvariantsToField _ Q
      ((Ideal.inertiaInvariantsToField_inertiaInvariantsMap hσF (ε y)).trans
        ((congrArg σF (hε y)).trans ((hσFk y).trans (hε (Φ y)).symm)))
  have hrσ (a : Ideal.inertiaInvariants C.functionField Q) :
      r (Ideal.inertiaInvariantsMap C.functionField Q hσF a) = Φ (r a) :=
    residueMap_commutes_of_section ε r _ Φ.toRingHom hrε hr
      (fun _ ↦ Ideal.isUnit_of_isUnit_inertiaInvariantsMap hσF) hσε a
  have hσalg : CommRingCat.ofHom (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q))
      ≫ CommRingCat.ofHom (Ideal.inertiaInvariantsMap C.functionField Q hσF) =
      CommRingCat.ofHom (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q)) :=
    CommRingCat.hom_ext (RingHom.ext (Ideal.inertiaInvariantsMap_algebraMap hσF))
  have hσεc : CommRingCat.ofHom ε ≫ CommRingCat.ofHom
      (Ideal.inertiaInvariantsMap C.functionField Q hσF) =
      CommRingCat.ofHom Φ.toRingEquiv.toRingHom ≫ CommRingCat.ofHom ε :=
    CommRingCat.hom_ext (RingHom.ext hσε)
  have hrσc : CommRingCat.ofHom r ≫ CommRingCat.ofHom Φ.toRingEquiv.toRingHom =
      CommRingCat.ofHom (Ideal.inertiaInvariantsMap C.functionField Q hσF) ≫
        CommRingCat.ofHom r :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ (hrσ a).symm)
  have htfc : CommRingCat.ofHom (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom ≫
      CommRingCat.ofHom (σF : Ω →+* Ω) =
      CommRingCat.ofHom (Ideal.inertiaInvariantsMap C.functionField Q hσF) ≫
        CommRingCat.ofHom (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦
      (Ideal.inertiaInvariantsToField_inertiaInvariantsMap hσF a).symm)
  have hΦ : (specGeometricFrobenius K ^ n).asIso.hom =
      Spec.map (CommRingCat.ofHom Φ.toRingEquiv.toRingHom) :=
    specGeometricFrobenius_pow_hom K n
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.inertiaInvariantsMap C.functionField Q hσF)),
    ?_, ?_, ?_⟩
  · exact specMap_comp_eq_comp_geometricGaloisFrobenius_pow hW.fromSpec _ _ hσalg _ n
      ((specMap_commutes_of_ringHom _ _ _ hσεc).trans
        (congrArg (Spec.map (CommRingCat.ofHom ε) ≫ ·) hΦ.symm)) h hhproj hhalg
  · exact (congrArg (· ≫ Spec.map (CommRingCat.ofHom r)) hΦ).trans
      (specMap_commutes_of_ringHom _ _ _ hrσc)
  · exact specMap_commutes_of_ringHom _ _ _ htfc

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
omit [GeometricallyConnected (C ↘ Spec (.of K))] in
/-- **A strictly henselian neighbourhood of a boundary point from a compatible point.** Let `c`
be an affine chart at the boundary point `z` with closed point `x`, `Q` a maximal ideal over `z`
of the integral closure of `Γ(C, W)` in `Ω`, compatible with `x̄` and the geometric generic
point: `ι(ι_x(ā)) ≡ a mod Q` for `a ∈ Γ(C, W)`, where `ι : k̄ ↪ Ω` is `genericEmb` and
`ι_x : κ(x) ↪ k̄` the embedding of `x̄`. Let `σ_F` be an element of the decomposition group of
`Q` acting on `ι(k̄)` as the `deg x`-th power of the geometric Frobenius. Then the inertia
invariants `B_Q^{I_Q}` give a strictly henselian neighbourhood of the boundary point for the
inertia group of `Q` and `σ_F`. (blueprint `lemma-boundary-stalk--1`) -/
theorem nonempty_boundaryNeighbourhood_of_compatible {z : C} (hz : z ∉ Set.range j.base)
    (c : BoundaryChart (C ↘ Spec (.of K)) j z) (x : C.finitePoints) (hx : x.1 = z)
    (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal] [Q.LiesOver c.ideal]
    (hQ : ∀ a : Γ(C, c.W), ∃ b ∈ Q, (b : Ω) =
      genericEmb (U ↘ Spec (.of K)) j ((C ↘ Spec (.of K)).geometricFiberPointEmb x
        (sectionsResidue x (hx ▸ c.mem) a)) - algebraMap Γ(C, c.W) Ω a)
    (σF : Gal(Ω/C.functionField)) (hσF : σF ∈ MulAction.stabilizer Gal(Ω/C.functionField) Q)
    (hσFk : ∀ y, σF (genericEmb (U ↘ Spec (.of K)) j y) = genericEmb (U ↘ Spec (.of K)) j
      (letI := Fintype.ofFinite K
       (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^
        (C ↘ Spec (.of K)).degreeOver x.1) y)) :
    Nonempty (BoundaryNeighbourhood (K := K) j (Q.inertia Gal(Ω/C.functionField)) σF x) := by
  subst hx
  let _ := Fintype.ofFinite K
  have hW := c.isAffineOpen
  have hxW : x.1 ∈ c.W := c.mem
  have : IsDedekindDomain Γ(C, c.W) := isDedekindDomain_of_isAffineOpen (C ↘ Spec (.of K)) hW
  have := isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen hW Q
  -- the embedding of `k̄` and the residue map
  have hε₀ : (genericEmb (U ↘ Spec (.of K)) j).comp (algebraMap K (AlgebraicClosure K)) =
      (algebraMap Γ(C, c.W) Ω).comp (sectionsStructHom (k₀ := K) hW) := by
    rw [genericEmb_comp_algebraMap, genericStructHom_eq j hW]
  obtain ⟨ε, r, hrε, hr, hε, hφ⟩ := exists_algebraicClosure_inertiaInvariants hW Q x hxW _ hε₀
  have hgAp : specInertiaInvariantsTo hW Q ≫ (C ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom ε) ≫ (Scheme.specAlgebraicClosure K).hom := by
    have hfp : hW.fromSpec ≫ (C ↘ Spec (.of K)) =
        Spec.map (CommRingCat.ofHom (sectionsStructHom (k₀ := K) hW)) := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    simp only [specInertiaInvariantsTo, Category.assoc, hfp, Scheme.specAlgebraicClosure,
      Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  -- the neighbourhood `h`
  obtain ⟨h, hhW, hhproj, hhalg⟩ : ∃ h : Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
      (C ↘ Spec (.of K)).geometricFiber, WeaklyEtale h ∧
      h ≫ (C ↘ Spec (.of K)).geometricFiberProj = specInertiaInvariantsTo hW Q ∧
      h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure =
        Spec.map (CommRingCat.ofHom ε) :=
    ⟨_, weaklyEtale_specInertiaInvariantsToGeometricFiber hW Q x hxW ε hgAp,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- the lift of `x̄`
  have hpt := specMap_comp_specInertiaInvariantsTo_of_compatible hW Q x hxW _ ε r hrε hr hε _ hQ
  have hw : Spec.map (CommRingCat.ofHom r) ≫ h =
      𝟙 _ ≫ (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x :=
    specMap_comp_geometricFiberPoint_of_section x (CommRingCat.ofHom ε) (CommRingCat.ofHom r)
      (CommRingCat.hom_ext hrε) h
      ((congrArg (Spec.map (CommRingCat.ofHom r) ≫ ·) hhproj).trans
        (hpt.trans (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj
          (C ↘ Spec (.of K)) x).symm)) hhalg
  obtain ⟨t, htl, ht⟩ := exists_proEtale_pointLift_of_residueMap x h r hr hw
  -- the punctured neighbourhood
  obtain ⟨e', he'⟩ := exists_iso_pullback_geometricFiberMap hW Q x hxW j c.ϖ (c.opensRange_inf hz)
    c.ϖ_mem (c.ϖ_ne_zero hz) h hhproj
  let k := e'.hom ≫ pullback.snd h j̄
  let e : ProEt.mk k ≅ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j̄).obj (ProEt.mk h) :=
    MorphismProperty.Over.isoMk e' rfl
  have hfst : specFieldMap (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField))) Ω ≫
      e'.hom ≫ pullback.fst h j̄ = Spec.map (CommRingCat.ofHom
        (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom) :=
    (congrArg (specFieldMap
      (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField))) Ω ≫ ·) he').trans
        (Spec.map_comp _ _).symm
  have hgen : genericBasePoint j ≫ j =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(C, c.W) Ω)) ≫ hW.fromSpec := by
    change (Spec.map (CommRingCat.ofHom (algebraMap C.functionField Ω)) ≫
      genericPointLift j) ≫ j = _
    rw [Category.assoc, genericPointLift_comp, hW.fromSpecFunctionField_eq,
      ← Spec.map_comp_assoc]
    congr 2
  have hspec : specFieldMap (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField))) Ω ≫
      k = genericGeomPoint (U ↘ Spec (.of K)) j := by
    exact comp_pullback_snd_eq_genericGeomPoint j hW.fromSpec _ (CommRingCat.ofHom ε)
      (CommRingCat.ofHom (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom)
      (CommRingCat.ofHom (algebraMap Γ(C, c.W) Ω)) h hhproj hhalg _ e'.hom hfst hgen
      (CommRingCat.hom_ext (RingHom.ext
        (Ideal.inertiaInvariantsToField C.functionField Q).commutes))
      (CommRingCat.hom_ext (RingHom.ext hε))
  -- the Galois group of `Ω / K'` is the inertia group
  have hmem (σ : Gal(Ω/C.functionField)) : σ ∈ Q.inertia Gal(Ω/C.functionField) ↔
      ∀ b : IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField)),
        σ (algebraMap _ Ω b) = algebraMap _ Ω b := by
    refine ⟨fun hσ b ↦ (IntermediateField.mem_fixedField_iff _ _).1 b.2 σ hσ, fun hσ ↦ ?_⟩
    rw [← Ideal.fixingSubgroup_fixedField_inertia Q (K := C.functionField)]
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).2 fun y hy ↦ hσ ⟨y, hy⟩
  -- the Frobenius lift
  obtain ⟨α, hα, hcα, hεα⟩ := exists_frobeniusLift_inertiaInvariants hW Q hσF _ ε r hrε hr hε _
    hσFk h hhproj hhalg
  refine ⟨{
    A := Ideal.inertiaInvariants C.functionField Q
    h := h
    t := t
    ht := ht
    K' := IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField))
    exists_algebraMap_eq := fun a ↦ ⟨⟨algebraMap _ Ω a,
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ _ ↦ σ.commutes a⟩, rfl⟩
    k := k
    e := e
    specFieldMap_comp := hspec
    mem_iff := hmem
    α := α
    hα := hα
    hcα := (congrArg ((specGeometricFrobenius K ^
      (C ↘ Spec (.of K)).degreeOver x.1).asIso.hom ≫ ·) htl).trans
        (hcα.trans (congrArg (· ≫ α) htl.symm))
    hεα := (congrArg (Spec.map (CommRingCat.ofHom (σF : Ω →+* Ω)) ≫ ·) hfst).trans
      (hεα.trans (congrArg (· ≫ α) hfst.symm)) }⟩

end AlgebraicGeometry.WeilGroup
