/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.Pi

/-! # Transporting a root splitting through an affine chart

## References

* Stacks Project, Tag 0EYG, off-divisor case
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem root_split_transport_pullback
    (R : CommRingCat.{u}) (g : R) (n : ℕ) {Y : Scheme.{u}}
    (p : Y ⟶ Spec R) (d : ℕ) (S : CommRingCat.{u}) (φ : R →+* S)
    :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (e : Spec S ≅ V.toScheme),
      e.hom ≫ V.ι ≫ q = Spec.map (CommRingCat.ofHom φ) →
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ ∐ fun _ : Fin d ↦ Spec S,
      θ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 (Spec S)) =
        pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by
  dsimp
  intro e he δ hδ
  let t := pullback.map p (Spec.map (CommRingCat.ofHom φ)) p _
    (𝟙 Y) e.hom (𝟙 (Spec R)) (by simp) (by simpa using he.symm)
  let σ := Sigma.mapIso (fun _ : Fin d ↦ e.symm)
  refine ⟨asIso t ≪≫ δ ≪≫ σ, ?_⟩
  have hσ : σ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 (Spec S)) =
      Sigma.desc (fun _ : Fin d ↦ 𝟙 _) ≫ e.inv := by
    apply Sigma.hom_ext
    intro k
    simp [σ]
  change t ≫ δ.hom ≫ σ.hom ≫ _ = _
  rw [hσ, ← Category.assoc δ.hom, hδ]
  simp [t]

set_option backward.isDefEq.respectTransparency false in
private theorem root_split_degree_one_chart
    (S : CommRingCat.{u}) (a : S) (d : ℕ) :
    let N := Spec (CommRingCat.of (∀ _k : Fin d,
      AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C a)))
    let q := Spec.map (CommRingCat.ofHom
      (algebraMap S (∀ _k : Fin d,
        AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C a))))
    let V : N.Opens := PrimeSpectrum.basicOpen
      (algebraMap S (∀ _k : Fin d,
        AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C a)) a)
    IsUnit a →
    ∃ η : (∐ fun _ : Fin d ↦ Spec S) ≅ V.toScheme,
      η.hom ≫ V.ι ≫ q = Sigma.desc (fun _ : Fin d ↦ 𝟙 (Spec S)) := by
  dsimp
  intro ha
  let B := AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C a)
  let f : B →ₐ[S] S := AdjoinRoot.liftAlgHom _ (Algebra.ofId S S) a (by simp)
  let g : S →ₐ[S] B := Algebra.ofId S B
  have hroot : AdjoinRoot.root ((Polynomial.X : Polynomial S) ^ (1 : ℕ) -
      Polynomial.C a) = algebraMap S B a := by
    have h := AdjoinRoot.eval₂_root
      ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C a)
    simpa [sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using h
  let E : B ≃ₐ[S] S := AlgEquiv.ofAlgHom f g
    (by ext) (by
      apply AdjoinRoot.algHom_ext
      change g (f (AdjoinRoot.root _)) = AdjoinRoot.root _
      rw [show f (AdjoinRoot.root _) = a by exact AdjoinRoot.liftAlgHom_root _ _ _ _]
      exact hroot.symm)
  let e : Spec S ≅ Spec (CommRingCat.of B) :=
    Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op
  let ι := ULift.{u} (Fin d)
  let j : Fin d ≃ ι := Equiv.ulift.symm
  let re := Sigma.reindex j (fun _ : ι ↦ Spec (CommRingCat.of B))
  let pe : (Fin d → B) ≃+* (ι → B) := RingEquiv.piCongrLeft' (fun _ ↦ B) j
  let si := Scheme.Spec.mapIso pe.toCommRingCatIso.op
  let t := Sigma.mapIso (fun _ : Fin d ↦ e) ≪≫ re ≪≫
    asIso (AlgebraicGeometry.sigmaSpec (fun _ : ι ↦ CommRingCat.of B)) ≪≫ si
  let N := Spec (CommRingCat.of (Fin d → B))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S (Fin d → B) a)
  have hV : V = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext x
    change (algebraMap S (Fin d → B) a ∉ x.asIdeal) ↔ True
    rw [iff_true]
    intro h
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (ha.map (algebraMap S (Fin d → B))))
  let v : V.toScheme ≅ N := N.isoOfEq hV ≪≫ N.topIso
  refine ⟨t ≪≫ v.symm, ?_⟩
  have hv : v.inv ≫ V.ι = 𝟙 N := by
    simp [v]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change t.hom ≫ v.inv ≫ V.ι ≫ _ = _
  rw [← Category.assoc v.inv, hv, Category.id_comp]
  apply Sigma.hom_ext
  intro k
  simp only [t, Iso.trans_hom, Sigma.ι_mapIso_hom_assoc,
    Category.assoc, asIso_hom]
  change e.hom ≫ Sigma.ι ((fun _ : ι ↦ Spec (CommRingCat.of B)) ∘ j) k ≫
    re.hom ≫ _ = _
  rw [show re = Sigma.reindex j (fun _ : ι ↦ Spec (CommRingCat.of B)) from rfl,
    Sigma.ι_reindex_hom_assoc]
  simp only [AlgebraicGeometry.ι_sigmaSpec_assoc]
  simp only [e, si, Scheme.Spec.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    AlgebraicGeometry.Scheme.Spec_map, Sigma.ι_comp_desc]
  rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_id S]
  congr 1
  ext x
  exact E.commutes x

/-- Transport a specified root splitting through an affine chart over the base: if the pullback
of the punctured root cover along `p` splits as `d` copies of it, then the pullback of `p` along
an affine chart `Spec S ≅ D(g)` is the punctured cover of `d` degree-one root algebras over `S`. -/
theorem root_split_away_transport_chart
    (R : CommRingCat.{u}) (g : R) (n : ℕ) {Y : Scheme.{u}}
    (p : Y ⟶ Spec R) (d : ℕ) (S : CommRingCat.{u}) (φ : R →+* S)
    (hunit : IsUnit (φ g)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (e : Spec S ≅ V.toScheme),
      e.hom ≫ V.ι ≫ q = Spec.map (CommRingCat.ofHom φ) →
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    let N := Spec (CommRingCat.of (∀ _k : Fin d,
      AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))))
    let q := Spec.map (CommRingCat.ofHom
      (algebraMap S (∀ _k : Fin d,
        AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g)))))
    let V : N.Opens := PrimeSpectrum.basicOpen
      (algebraMap S (∀ _k : Fin d,
        AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))) (φ g))
    ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
      γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by
  dsimp
  intro e he δ hδ
  obtain ⟨θ, hθ⟩ := root_split_transport_pullback R g n p d S φ e he δ hδ
  obtain ⟨η, hη⟩ := root_split_degree_one_chart S (φ g) d hunit
  refine ⟨θ ≪≫ η, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hη, hθ]

end AlgebraicGeometry.Scheme
