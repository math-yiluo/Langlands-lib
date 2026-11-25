/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.PointedGaloisCoverLimitDescent

/-!
# Noetherian approximation data for spreading a finite torsor

## References

* Stacks Project, Tag 0EZJ, limit reduction
* Stacks Project, Tag 0EZJ, proof of Lemma 58.31.9
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Descend the family and its generic torsor, without constructing an extension. -/
theorem GaloisCover.exists_noetherian_spreading_data {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (S₀ C₀ : Scheme.{u}) (hI₀ : IsIntegral S₀),
      letI : IsIntegral S₀ := hI₀
      ∃ (c₀ : C₀ ⟶ S₀) (σ₀ : S₀ ⟶ C₀)
        (Cη₀ : Scheme.{u}) (q₀ : Cη₀ ⟶ Spec S₀.functionField) (j₀ : Cη₀ ⟶ C₀)
        (sη₀ : Spec S₀.functionField ⟶ Cη₀) (Z₀ : GaloisCover G Cη₀)
        (a : C ⟶ C₀) (k : Cη ⟶ Cη₀) (χ : Z.P ⟶ Z₀.P),
        IsNoetherian S₀ ∧ QuasiSeparatedSpace S₀ ∧
        (∀ x : S₀, IsIntegrallyClosed (S₀.presheaf.stalk x)) ∧
        QuasiCompact c₀ ∧ QuasiSeparated c₀ ∧ Smooth c₀ ∧ GeometricallyConnected c₀ ∧
        σ₀ ≫ c₀ = 𝟙 S₀ ∧ IsUnit (Nat.card G : Γ(S₀, ⊤)) ∧
        IsPullback q₀ j₀ (S₀.fromSpecStalk (genericPoint S₀)) c₀ ∧
        sη₀ ≫ q₀ = 𝟙 _ ∧ sη₀ ≫ j₀ = S₀.fromSpecStalk (genericPoint S₀) ≫ σ₀ ∧
        (∃ z₀ : Spec S₀.functionField ⟶ Z₀.P, z₀ ≫ Z₀.π = sη₀) ∧
        k ≫ j₀ = j ≫ a ∧ IsPullback χ Z.π Z₀.π k := by
  obtain ⟨I, hcat, hmodel⟩ :=
    exists_normal_family_generic_limit hS c σ hσ (Nat.card G) hG q j hCη sη hsq hsj
  let : SmallCategory I := hcat
  obtain ⟨hco, D, K, κ, b, s, hκ, hb, hDqc, hDqs, hKqc, hKqs, hDa, hKa, hs,
    S₀, C₀, hI₀, hfamily⟩ := hmodel
  let : IsCofiltered I := hco
  let : ∀ i, IsIntegral (S₀ i) := hI₀
  obtain ⟨c₀, σ₀, q₀, j₀, e, a, hstage⟩ := hfamily
  obtain ⟨i, Z₀, χ, hχ, z₀, hz₀⟩ :=
    GaloisCover.exists_pointed_stage_of_affine_limits D K hDqc hDqs hKqc hKqs hDa hKa
      κ b hκ hb s sη hs G Z hZ
  obtain ⟨hN, hqs, hnormal, hqc, hqsc, hsm, hconn, hsec, hn, hgen, hsq₀, hsj₀,
    hcomp⟩ := hstage i
  refine ⟨S₀ i, C₀ i, hI₀ i, c₀ i, σ₀ i, D.obj i, q₀ i, j₀ i,
    (e i).inv ≫ s.app i, Z₀, a i, κ.app i, χ, hN, hqs, hnormal, hqc, hqsc, hsm,
    hconn, hsec, hn, hgen, ?_, ?_, ?_, hcomp, hχ⟩
  · simpa only [Category.assoc] using hsq₀
  · simpa only [Category.assoc] using hsj₀
  · exact ⟨(e i).inv ≫ z₀, by rw [Category.assoc, hz₀]⟩

end AlgebraicGeometry.Scheme
