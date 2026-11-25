/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.EtaleBaseChangePolynomialCertificate
import WeilConjectures.RingTheory.EtalePolynomialCertificateColimit

/-!
# Descent of etaleness along a directed colimit of rings

Source: Stacks Project, Algebra, Lemma 10.168.7 (Tag 07RI)
(blueprint: lem-weil-pbc-colimit-etale-ring-map).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finitely presented map of algebras over a stage of a directed system is etale
at some later stage if its base change to the colimit is etale.
Source: Stacks Project, Algebra, Lemma 10.168.7 (Tag 07RI)
(blueprint: lem-weil-pbc-colimit-etale-ring-map).

Proof:
1. Choose a finite polynomial presentation of `C₀` over `B₀`. Base change gives
   the same presentation at each stage and at the colimit, using
   `lem-weil-pbc-tensor-cancel-base-change`, `lem-weil-pbc-polynomial-scalar-extension`
   and `lem-weil-pbc-tensor-quotient-base-change`. The coefficient maps commute
   with partial derivatives.
2. By `lem-weil-pbc-etale-ring-map-conormal-criterion`, etaleness is equivalent to
   bijectivity of the conormal differential from the relation ideal modulo its
   square to the free module on the differentials of the variables.
3. Lift the basis differentials through its inverse. Write those lifts as linear
   combinations of the finitely many relations. The two inverse identities are
   finitely many polynomial identities: one modulo the relation ideal, the other
   modulo its square. Choose coefficients witnessing both ideal memberships.
4. By `lem-weil-pbc-directed-colimit-base-change-elementwise`, all these finitely
   many coefficients lift to a common stage, and the finitely many differences
   between the two sides vanish after passing to a common later stage.
5. The descended lifts define an inverse to the conormal differential: check one
   composite on the free basis and the other on the generating relation classes.
   The conormal criterion then gives etaleness at this stage. -/
theorem Etale.exists_stage_of_directedColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ C₀ : Type v) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfp : φ₀.FinitePresentation) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (colimit.ι F i₀).hom.toAlgebra
    Etale (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom)) →
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
      Etale (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).toRingHom)) := by
  obtain ⟨n, m, f, hf⟩ := exists_etale_baseChange_polynomialCertificate B₀ C₀ φ₀ hfp
  let : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
    (colimit.ι F i₀).hom.toAlgebra
  intro h
  have hc := (hf (colimit F : CommRingCat.{u})).mp h
  obtain ⟨i, hi, hcᵢ⟩ :=
    Algebra.exists_stage_etalePolynomialCertificate F i₀ B₀ n m f hc
  refine ⟨i, hi, ?_⟩
  let : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
  exact (hf (F.obj i)).mpr hcᵢ

end AlgebraicGeometry
