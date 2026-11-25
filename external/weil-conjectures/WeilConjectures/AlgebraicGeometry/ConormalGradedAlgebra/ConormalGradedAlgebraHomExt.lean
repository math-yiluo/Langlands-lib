/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra

/-! # Degree-one uniqueness for maps from the conormal algebra

Source: Stacks 0630, 0632, generation of the associated graded algebra by degree one.
(blueprint: lem-pur-conormal-graded-algebra-hom-ext).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ConormalGradedAlgebra

private theorem graded_hom_ext {R : Type u} [CommRing R] (I : Ideal R)
    {A : Type v} [CommRing A] (f g : Ideal.associatedGraded I →+* A)
    (hzero : f.comp (Ideal.associatedGradedRingHom I) =
      g.comp (Ideal.associatedGradedRingHom I))
    (hone : ∀ x : (I ^ 1 : Ideal R),
      f (DirectSum.of (Ideal.associatedGradedPiece I) 1 (Submodule.Quotient.mk x)) =
        g (DirectSum.of (Ideal.associatedGradedPiece I) 1 (Submodule.Quotient.mk x))) :
    f = g := by
  let q (n : ℕ) (x : (I ^ n : Ideal R)) : Ideal.associatedGraded I :=
    DirectSum.of (Ideal.associatedGradedPiece I) n (Submodule.Quotient.mk x)
  have qadd (n : ℕ) (x y : (I ^ n : Ideal R)) : q n (x + y) = q n x + q n y := by
    dsimp [q]
    rw [map_add]
  have hn (n : ℕ) (x : (I ^ n : Ideal R)) : f (q n x) = g (q n x) := by
    induction n with
    | zero => exact RingHom.congr_fun hzero x.val
    | succ n ih =>
      have hx : x.val ∈ (I ^ n) * (I ^ 1) := by
        rw [pow_one, ← pow_succ]
        exact x.property
      have h : ∀ (y : R) (hy : y ∈ (I ^ n) * (I ^ 1)),
          f (q (n + 1) ⟨y, by simpa [pow_succ] using hy⟩) =
            g (q (n + 1) ⟨y, by simpa [pow_succ] using hy⟩) := by
        intro y hy
        induction hy using Submodule.mul_induction_on' with
        | mem_mul_mem a ha b hb =>
          have hab : a * b ∈ I ^ (n + 1) := by
            simpa [pow_succ] using Ideal.mul_mem_mul ha hb
          have heq : q (n + 1) ⟨a * b, hab⟩ = q n ⟨a, ha⟩ * q 1 ⟨b, hb⟩ :=
            (Ideal.associatedGraded_mul I n 1 ⟨a, ha⟩ ⟨b, hb⟩).symm
          rw [heq, map_mul, map_mul, ih, hone]
        | add y hy z hz ihy ihz =>
          change f (q (n + 1) ((⟨y, by simpa [pow_succ] using hy⟩ : (I ^ (n + 1) : Ideal R)) +
            ⟨z, by simpa [pow_succ] using hz⟩)) = _
          change f (q (n + 1) ((⟨y, by simpa [pow_succ] using hy⟩ :
            (I ^ (n + 1) : Ideal R)) + ⟨z, by simpa [pow_succ] using hz⟩)) =
              g (q (n + 1) ((⟨y, by simpa [pow_succ] using hy⟩ :
                (I ^ (n + 1) : Ideal R)) + ⟨z, by simpa [pow_succ] using hz⟩))
          simp only [qadd, map_add, ihy, ihz]
      exact h x.val hx
  apply RingHom.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n x =>
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact hn n x
  | add x y ihx ihy => simp only [map_add, ihx, ihy]

/-- An algebra morphism out of the conormal algebra is determined by its values on the
classes of ideal sections in degree one, on all ambient affine charts.
Source: Stacks 0630, 0632, the degree-one generation of the associated graded algebra.
(blueprint: lem-pur-conormal-graded-algebra-hom-ext).

Proof: On an ambient affine chart, identify the source with gr_I(R). Its homogeneous
classes are represented by ideal-power sections, by powerIdentification and the affine
ideal-section theorem. Degree zero is fixed by the structure-algebra condition. Induct
on n, using I^(n+1)=I^n I and induction on ideal-product membership, to get equality on
every degree from equality in degree one. Additive direct-sum induction gives equality
on the chart. The inverse images of ambient affine opens form a basis on the closed
subscheme, so the sheaf-morphism basis criterion gives global equality. The induction
uses no finiteness or regularity, and includes zero and unit ideals and empty schemes. -/
theorem hom_ext_degree_one {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {B : Z.CommAlgebraSheaf} (f g : (presentation i).algebra ⟶ B)
    (h : ∀ (U : X.affineOpens) (a : (power i 1).val.obj (op U.1)),
      f.right.hom.app (op (i ⁻¹ᵁ U.1))
          (homogeneousClass i (presentation i).algebra (presentation i).inclusion 1 U.1 a) =
        g.right.hom.app (op (i ⁻¹ᵁ U.1))
          (homogeneousClass i (presentation i).algebra (presentation i).inclusion 1 U.1 a)) :
    f = g := by
  have hlift (U : X.affineOpens) (n : ℕ) (a : Γ(X, U.1))
      (ha : a ∈ i.ker.ideal U ^ n) :
      ∃ b : (power i n).val.obj (op U.1),
        (powerInclusion i n).val.app (op U.1) b = a := by
    obtain ⟨e, he⟩ := (presentation i).powerIdentification n
    have ha' : a ∈ (i.ker ^ n).ideal U := by simpa using ha
    have hc' : a ∈ Set.range ((i.ker ^ n).toModulesι.app U.1) := by
      rw [(i.ker ^ n).range_toModulesι_app U]
      exact ha'
    obtain ⟨c, hc⟩ := hc'
    refine ⟨e.inv.val.app (op U.1) c, ?_⟩
    have hh : e.inv ≫ powerInclusion i n = (i.ker ^ n).toModulesι := by
      rw [← he, Iso.inv_hom_id_assoc]
    exact (congrArg (fun k ↦ k.val.app (op U.1) c) hh).trans hc
  apply Under.UnderMorphism.ext
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (B := fun U : X.affineOpens ↦ i ⁻¹ᵁ U.1)
    (by
      convert! X.isBasis_affineOpens.of_isInducing i.isClosedEmbedding.isInducing using 1
      ext W
      constructor
      · rintro ⟨U, rfl⟩
        exact ⟨U.1, U.2, rfl⟩
      · rintro ⟨U, hU, rfl⟩
        exact ⟨⟨U, hU⟩, rfl⟩)
  intro U
  obtain ⟨e, he⟩ := (presentation i).affineChart U
  let f' := (f.right.hom.app (op (i ⁻¹ᵁ U.1))).hom.comp e.inv.hom
  let g' := (g.right.hom.app (op (i ⁻¹ᵁ U.1))).hom.comp e.inv.hom
  have hclass (n : ℕ) (a : (i.ker.ideal U ^ n : Ideal Γ(X, U.1))) :
      ∃ b : (power i n).val.obj (op U.1),
        e.inv (DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
          (Submodule.Quotient.mk a)) =
            homogeneousClass i (presentation i).algebra (presentation i).inclusion n U.1 b := by
    obtain ⟨b, hb⟩ := hlift U n a.val a.property
    obtain ⟨hb', he'⟩ := he n b
    refine ⟨b, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    simp [he', hb]
  have hfg : f' = g' := by
    apply graded_hom_ext (i.ker.ideal U)
    · apply RingHom.ext
      intro a
      obtain ⟨b, hb⟩ := hclass 0 ⟨a, by simp⟩
      change f.right.hom.app _ (e.inv (Ideal.associatedGradedRingHom _ a)) =
        g.right.hom.app _ (e.inv (Ideal.associatedGradedRingHom _ a))
      change f.right.hom.app _ (e.inv (DirectSum.of _ 0
          (Submodule.Quotient.mk (⟨a, by simp⟩ : (i.ker.ideal U ^ 0 : Ideal Γ(X, U.1)))))) = _
      change f.right.hom.app _ (e.inv (DirectSum.of _ 0
          (Submodule.Quotient.mk (⟨a, by simp⟩ : (i.ker.ideal U ^ 0 : Ideal Γ(X, U.1)))))) =
        g.right.hom.app _ (e.inv (DirectSum.of _ 0
          (Submodule.Quotient.mk (⟨a, by simp⟩ : (i.ker.ideal U ^ 0 : Ideal Γ(X, U.1))))))
      rw [hb, (presentation i).constants]
      exact congrArg (fun k ↦ k.hom.app (op (i ⁻¹ᵁ U.1)) (i.app U.1 b))
        (f.w.trans g.w.symm)
    · intro a
      obtain ⟨b, hb⟩ := hclass 1 a
      change f.right.hom.app _ (e.inv _) = g.right.hom.app _ (e.inv _)
      rw [hb]
      exact h U b
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  have hh := RingHom.congr_fun hfg (e.hom a)
  simpa [f', g'] using hh

end AlgebraicGeometry.ConormalGradedAlgebra
