/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover

/-! # The affine-line Artin–Schreier cover

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-lem-as-properties/
lem-fd-as-cover-affine-line.md, node statement (blueprint: lemma-integral-linear-character--2).

The affine-line cover is identified with affine one-space by sending the quotient
coordinate `T` to the affine coordinate `y`. The transported structural morphism
and prime-field translations are recorded explicitly.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

/-- The Artin–Schreier cover of the affine line is the affine line, with its
structural map and prime-field action in the displayed coordinates.

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-lem-as-properties/
lem-fd-as-cover-affine-line.proof.md, all four proof steps (blueprint:
lemma-integral-linear-character--2). Proof: (1) Write `A` for the affine line and use the defining
pullback of the cover, with quotient ring `B = Γ(A)[T]/(T^p-T-x)`. Evaluation at `x`, with
coefficient map `AS_p*`, kills this polynomial. The quotient universal property
`AdjoinRoot.lift` gives `B → Γ(A)`, and hence a pullback lift `g : A → Y`.
(2) Define `f : Y → A` over `k` by `f*x = T`. Then `g ≫ f = 𝟙` by the
base and coordinate formulas. Pulling back the quotient relation gives
`T^p-T = π*x`, so `f ≫ AS_p = π`.
(3) Check `f ≫ g = 𝟙` on the pullback projections. On the base this is the
previous equality; on the spectrum projection use `AdjoinRoot.ringHom_ext`.
The coefficient equality follows from `f ≫ AS_p = π`; the root equality
is `f*x = T`. Thus `f` and `g` give the required isomorphism.
(4) Take the action from lemma-artin-schreier-character-sheaf. Its conjugate fixes the base and
sends `x` to `g*(T+a) = x+a`, so `AffineSpace.hom_ext` identifies it with
the displayed translation. -/
theorem artinSchreierCover_affineLine (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [Finite k] [CharP k p] :
    ∃ e : (artinSchreierCover p (AffineSpace PUnit (Spec (CommRingCat.of k)))
        (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)).left ≅
        AffineSpace PUnit (Spec (CommRingCat.of k)),
      (e.hom.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit) =
        artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (CommRingCat.of k)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)) ∧
      (e.inv ≫ (artinSchreierCover p (AffineSpace PUnit (Spec (CommRingCat.of k)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)).hom =
        AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) p) ∧
      ∃ σ : Multiplicative (ZMod p) →* Aut
          (artinSchreierCover p (AffineSpace PUnit (Spec (CommRingCat.of k)))
            (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)),
        (∀ a : ZMod p, (σ (Multiplicative.ofAdd a)).asIso.hom.left.appTop
            (artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (.of k)))
              (AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
          artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (.of k)))
              (AffineSpace.coord (Spec (.of k)) PUnit.unit) +
            (a.val : Γ((artinSchreierCover p (AffineSpace PUnit (Spec (.of k)))
              (AffineSpace.coord (Spec (.of k)) PUnit.unit)).left, ⊤))) ∧
        ∀ a : ZMod p,
          e.inv ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ e.hom =
            AffineSpace.translation (fun _ : PUnit.{u + 1} ↦
              (Scheme.ΓSpecIso (.of k)).inv.hom (a.val : k)) := by
  -- Construct the maps using the polynomial quotient and the pullback.
  let A := AffineSpace PUnit (Spec (CommRingCat.of k))
  let x : Γ(A, ⊤) := AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit
  let F := artinSchreierCoverPolynomial p A x
  let B := AdjoinRoot F
  let Y := (artinSchreierCover p A x).left
  let c : Γ(Y, ⊤) := artinSchreierCoverCoordinate p A x
  let j : Γ(A, ⊤) →+* Γ(A, ⊤) :=
    (AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) p).appTop.hom
  let φ : B →+* Γ(A, ⊤) := AdjoinRoot.lift j x (by
    have hj : j x = x ^ p - x := by
      change (AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) p).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit) = _
      exact AffineSpace.artinSchreierMap_appTop_coord _ _ _ _
    change Polynomial.eval₂ j x (Polynomial.X ^ p - Polynomial.X - Polynomial.C x) = 0
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, hj]
    ring)
  let AS := AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) p
  let f : Y ⟶ A := AffineSpace.homOfVector
    ((artinSchreierCover p A x).hom ≫ A ↘ Spec (CommRingCat.of k)) (fun _ ↦ c)
  have hchar : (p : Γ(A, ⊤)) = 0 := by
    rw [← map_natCast ((A ↘ Spec (CommRingCat.of k)).appTop.hom.comp
      (Scheme.ΓSpecIso (.of k)).inv.hom), CharP.cast_eq_zero, map_zero]
  let g₀ : A ⟶ (pullback A.toSpecΓ
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of F)))) :=
    pullback.lift AS (A.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) (by
      rw [Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
      rw [cancel_epi]
      congr 1
      exact CommRingCat.hom_ext (by
        ext r
        change j r = φ ((algebraMap Γ(A, ⊤) B) r)
        rw [show (algebraMap Γ(A, ⊤) B) r = AdjoinRoot.of F r by
          rfl, AdjoinRoot.lift_of]))
  let g : A ⟶ Y := g₀
  have hg₀fst : g₀ ≫ pullback.fst A.toSpecΓ
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of F))) = AS :=
    pullback.lift_fst _ _ _
  have hg₀snd : g₀ ≫ pullback.snd A.toSpecΓ
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of F))) =
      A.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  -- One composite is determined by its base map and affine coordinate.
  have hf : g ≫ f = 𝟙 A := by
    dsimp [g, f, Y, artinSchreierCover]
    apply AffineSpace.hom_ext
    · rw [Category.assoc, AffineSpace.homOfVector_over]
      change g₀ ≫ pullback.fst A.toSpecΓ
          (Spec.map (CommRingCat.ofHom (AdjoinRoot.of F))) ≫
          (A ↘ Spec (CommRingCat.of k)) = _
      rw [← Category.assoc, hg₀fst, AffineSpace.artinSchreierMap_over, Category.id_comp]
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [AffineSpace.homOfVector_appTop_coord]
      change g₀.appTop c = _
      change (g₀ ≫ pullback.snd A.toSpecΓ
        (Spec.map (CommRingCat.ofHom (AdjoinRoot.of F)))).appTop
        ((Scheme.ΓSpecIso (.of B)).inv (AdjoinRoot.root F)) = _
      rw [hg₀snd]
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [Scheme.toSpecΓ_appTop, Scheme.specMap_appTop_ΓSpecIso_inv]
      rw [(Scheme.ΓSpecIso Γ(A, ⊤)).inv_hom_id_apply]
      dsimp [φ]
      rw [AdjoinRoot.lift_root]
      exact congrArg (AffineSpace.coord (Spec (CommRingCat.of k)))
        (Subsingleton.elim PUnit.unit i)
  -- The pullback equation identifies coefficients on the cover.
  let π : Y ⟶ A := (artinSchreierCover p A x).hom
  let q : Y ⟶ Spec (.of B) := pullback.snd A.toSpecΓ
    (Spec.map (CommRingCat.ofHom (AdjoinRoot.of F)))
  let β : B →+* Γ(Y, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom
  have hβ (r : Γ(A, ⊤)) : β (AdjoinRoot.of F r) = π.appTop r := by
    have h := congrArg (fun m : Y ⟶ Spec Γ(A, ⊤) ↦
      m.appTop ((Scheme.ΓSpecIso Γ(A, ⊤)).inv r))
        (pullback.condition (f := A.toSpecΓ)
          (g := Spec.map (CommRingCat.ofHom (AdjoinRoot.of F))))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.toSpecΓ_appTop, Scheme.specMap_appTop_ΓSpecIso_inv,
      Iso.inv_hom_id_apply] at h
    exact h.symm
  have hc : c ^ p - c = π.appTop x := by
    have hroot := AdjoinRoot.eval₂_root F
    change Polynomial.eval₂ (AdjoinRoot.of F) (AdjoinRoot.root F)
      (Polynomial.X ^ p - Polynomial.X - Polynomial.C x) = 0 at hroot
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at hroot
    have h := congrArg β hroot
    simp only [map_sub, map_pow, map_zero, hβ] at h
    exact sub_eq_zero.mp h
  have hπ : f ≫ AS = π := by
    apply AffineSpace.hom_ext
    · dsimp [f, AS, π]
      rw [Category.assoc, AffineSpace.artinSchreierMap_over,
        AffineSpace.homOfVector_over]
    · intro i
      cases i
      change (f ≫ AffineSpace.artinSchreierMap PUnit (Spec (.of k)) p).appTop
        (AffineSpace.coord (Spec (.of k)) PUnit.unit) = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow]
      change f.appTop x ^ p - f.appTop x = π.appTop x
      rw [show f.appTop x = c from AffineSpace.homOfVector_appTop_coord _ _ _]
      exact hc
  -- Check the other composite on the base and on the quotient generators.
  have hg : f ≫ g = 𝟙 Y := by
    change f ≫ g₀ = 𝟙 Y
    apply pullback.hom_ext
    · rw [Category.assoc, hg₀fst, Category.id_comp]
      exact hπ
    · rw [Category.assoc, hg₀snd, Category.id_comp]
      apply ext_to_Spec
      apply CommRingCat.hom_ext
      apply AdjoinRoot.ringHom_ext
      · ext r
        change (f ≫ A.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
          ((Scheme.ΓSpecIso (.of B)).inv (AdjoinRoot.of F r)) = β (AdjoinRoot.of F r)
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          Scheme.specMap_appTop_ΓSpecIso_inv, Scheme.toSpecΓ_appTop]
        rw [(Scheme.ΓSpecIso Γ(A, ⊤)).inv_hom_id_apply]
        rw [CommRingCat.ofHom_apply]
        rw [show φ (AdjoinRoot.of F r) = j r from AdjoinRoot.lift_of _]
        rw [hβ]
        exact congrArg (fun m : Y ⟶ A ↦ m.appTop r) hπ
      · change (f ≫ A.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
          ((Scheme.ΓSpecIso (.of B)).inv (AdjoinRoot.root F)) = c
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          Scheme.specMap_appTop_ΓSpecIso_inv, Scheme.toSpecΓ_appTop]
        rw [(Scheme.ΓSpecIso Γ(A, ⊤)).inv_hom_id_apply]
        rw [CommRingCat.ofHom_apply]
        rw [show φ (AdjoinRoot.root F) = x from AdjoinRoot.lift_root _]
        exact AffineSpace.homOfVector_appTop_coord _ _ _
  let e : Y ≅ A := { hom := f, inv := g, hom_inv_id := hg, inv_hom_id := hf }
  obtain ⟨_, _, _, σ, hσ, _⟩ := artinSchreier_cover_properties p A hchar x
  refine ⟨e, ?_, ?_, σ, hσ, ?_⟩
  · exact AffineSpace.homOfVector_appTop_coord _ _ _
  · exact hg₀fst
  · intro a
    change g ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ f = _
    have hgc : g.appTop c = x := by
      have h := congrArg (fun m : A ⟶ A ↦ m.appTop x) hf
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.Hom.id_appTop, CommRingCat.id_apply,
        show f.appTop x = c from AffineSpace.homOfVector_appTop_coord _ _ _] using h
    apply AffineSpace.hom_ext
    · rw [Category.assoc, Category.assoc]
      rw [show f ≫ A ↘ Spec (.of k) = π ≫ A ↘ Spec (.of k) from
        AffineSpace.homOfVector_over _ _]
      rw [← Category.assoc (σ (Multiplicative.ofAdd a)).asIso.hom.left,
        Over.w, ← Category.assoc]
      change (g₀ ≫ pullback.fst _ _) ≫ (A ↘ Spec (.of k)) = _
      rw [hg₀fst, AffineSpace.artinSchreierMap_over, AffineSpace.translation_over]
    · intro i
      cases i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [show f.appTop x = c from AffineSpace.homOfVector_appTop_coord _ _ _]
      rw [hσ a, map_add, map_natCast, hgc, AffineSpace.translation_appTop_coord]
      simp only [map_natCast]
      rfl

end AlgebraicGeometry
