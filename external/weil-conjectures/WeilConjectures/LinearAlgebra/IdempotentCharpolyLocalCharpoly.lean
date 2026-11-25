/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.LinearAlgebra.IdempotentCharpoly
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.LinearAlgebra.IdempotentImageBaseChange
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! # Local matrix realization of an idempotent summand determinant

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph.
(blueprint: lem-weil-pbc-idempotent-charpoly-local-charpoly)
-/

@[expose] public section

universe u v

namespace Matrix

private theorem idempotentCharpoly_retract {S : Type*} [CommRing S]
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (T : Matrix n n S) (Q : Matrix n m S) (R : Matrix m n S) (hRQ : R * Q = 1) :
    idempotentCharpoly T (Q * R) = (R * T * Q).charpoly := by
  let Qc := Q.map Polynomial.C
  let Rc := R.map Polynomial.C
  have hRQc : Rc * Qc = 1 := by
    simpa [Rc, Qc] using congrArg (fun M => M.map Polynomial.C) hRQ
  have hscalar : Rc * Matrix.scalar n (Polynomial.X : Polynomial S) * Qc =
      Matrix.scalar m Polynomial.X := by
    rw [← Matrix.scalar_comm Polynomial.X (fun _ => Commute.all _ _) Rc,
      Matrix.mul_assoc, hRQc, Matrix.mul_one]
  unfold idempotentCharpoly charpoly
  have hC : Polynomial.C.mapMatrix (Q * R) = Qc * Rc := by
    simp [Qc, Rc, Matrix.map_mul]
  rw [hC]
  have hleft : 1 - Qc * Rc + T.charmatrix * (Qc * Rc) =
      1 + ((T.charmatrix - 1) * Qc) * Rc := by
    simp only [sub_mul, one_mul, Matrix.mul_assoc]
    abel
  rw [hleft, Matrix.det_one_add_mul_comm]
  congr 1
  unfold Matrix.charmatrix
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul]
  rw [← Matrix.mul_assoc Rc (Matrix.scalar n Polynomial.X), hscalar, hRQc]
  change 1 + (Matrix.scalar m Polynomial.X - Rc * (T.map Polynomial.C * Qc) - 1) =
    Matrix.scalar m Polynomial.X - (R * T * Q).map Polynomial.C
  rw [Matrix.map_mul, Matrix.map_mul]
  dsimp only [Rc, Qc]
  rw [Matrix.mul_assoc]
  abel

/-- On a finite standard cover, the summand determinant is a matrix characteristic polynomial.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph;
the determinant realization and the refinement argument are made explicit here.
(blueprint: lem-weil-pbc-idempotent-charpoly-local-charpoly)

Proof: reindex the ambient free module by `Fin (Fintype.card n)`. The image-base-change
lemma applied to P and 1-P splits it into their finite projective images. Choose finite
standard free covers for these two images using the finite-projective cover theorem.
Refine the covers by all pairwise products of their elements: multiplying expressions
for 1 in the two generated ideals shows that these products still span the unit ideal.
Localization at a product factors through either localization, so both summands are
finite free there, and their split decomposition is preserved by base change. Choose
finite bases of both summands and concatenate them to a basis of the ambient module.
The equation TP=PT shows that T preserves the summands. In this basis P is diag(1,0)
and T is diag(U,V), where U has size d, the rank of the first summand. Consequently
1-P+(X-T)P is diag(X-U,1). Ring maps commute with the determinant and with the displayed
polynomial matrix operations; conjugation preserves determinant. The determinant of
this block diagonal matrix is U.charpoly times det(1), which is U.charpoly. Enumerate
the finite product cover by Fin r and use these U as the existential witnesses.
No constant-rank assumption is needed: d may vary over the cover. Over the zero ring,
a one-element cover with f=1 and d=0 works, since all polynomial equalities hold.
For an empty ambient index set the determinant is 1, realized by the empty matrix.
-/
theorem exists_standardCover_idempotentCharpoly_eq_charpoly
    {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]
    (T P : Matrix n n A) (hP : P * P = P) (hTP : T * P = P * T) :
    ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i : Fin r, ∃ (d : ℕ) (U : Matrix (Fin d) (Fin d) (Localization.Away (f i))),
        (idempotentCharpoly T P).map (algebraMap A (Localization.Away (f i))) =
          U.charpoly := by
  classical
  -- The rectangular determinant identity does not require commutation.
  have _ := hTP
  clear hTP
  let b := Fintype.equivFin n
  let P0 := reindex b b P
  let T0 := reindex b b T
  let p : Module.End A (Fin (Fintype.card n) → A) := Matrix.toLin' P0
  have hp : IsIdempotentElem p := by
    change p.comp p = p
    dsimp [p, P0]
    rw [← Matrix.toLin'_mul]
    change Matrix.toLin' (reindexAlgEquiv A A b P * reindexAlgEquiv A A b P) = _
    rw [← map_mul, hP]
    rfl
  have : Module.Finite A p.range := by infer_instance
  have : Module.Projective A p.range := by
    apply Module.Projective.of_split p.range.subtype
      (LinearMap.IsIdempotentElem.isProj_range p hp).codRestrict
    ext x
    simp
  obtain ⟨r, f, hspan, hfree⟩ :=
    Module.exists_standardFreeCover_of_finite_projective A p.range
  refine ⟨r, f, hspan, ?_⟩
  intro i
  let S := Localization.Away (f i)
  -- Keep the inherited commutative-semiring instance throughout the base-change maps.
  let : CommSemiring S := (inferInstance : CommRing S).toCommSemiring
  let ρ := algebraMap A S
  let pS : Module.End S (Fin (Fintype.card n) → S) :=
    Matrix.toLin' ((LinearMap.toMatrix' p).map ρ)
  have hbc := LinearMap.idempotent_image_baseChange (Fintype.card n) p hp
    (algebraMap A S)
  dsimp only at hbc
  rw [toAlgebra_algebraMap] at hbc
  obtain ⟨_, _, _, _, hpS, _, _, _, _, e, _⟩ := hbc
  have : Module.Finite S (LocalizedModule.Away (f i) p.range) := (hfree i).1
  have : Module.Free S (LocalizedModule.Away (f i) p.range) := (hfree i).2
  let e' : LocalizedModule.Away (f i) p.range ≃ₗ[S] pS.range :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers (f i)) S
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) p.range)).equiv.symm.trans e
  have : Module.Finite S pS.range := Module.Finite.equiv e'
  have : Module.Free S pS.range := Module.Free.of_equiv e'
  by_cases hS : Nontrivial S
  · let := hS
    let d := Module.finrank S pS.range
    let c := (Module.finBasis S pS.range).equivFun
    let a := pS.range.subtype.comp c.symm.toLinearMap
    let z := c.toLinearMap.comp (LinearMap.IsIdempotentElem.isProj_range pS hpS).codRestrict
    have haz : a.comp z = pS := by
      ext x
      simp [a, z]
    have hza : z.comp a = LinearMap.id := by
      ext x
      simp [a, z]
    let Q := LinearMap.toMatrix' a
    let R := LinearMap.toMatrix' z
    have hQR : Q * R = P0.map ρ := by
      rw [← LinearMap.toMatrix'_comp, haz]
      simp [pS, p]
    have hRQ : R * Q = 1 := by
      rw [← LinearMap.toMatrix'_comp, hza, LinearMap.toMatrix'_id]
    refine ⟨d, R * T0.map ρ * Q, ?_⟩
    calc
      (idempotentCharpoly T P).map ρ = (idempotentCharpoly T0 P0).map ρ := by
        unfold idempotentCharpoly
        dsimp only [T0, P0]
        rw [Matrix.charmatrix_reindex]
        congr 1
        have hC : Polynomial.C.mapMatrix (reindex b b P) =
            reindex b b (Polynomial.C.mapMatrix P) := rfl
        rw [hC]
        change _ = (1 -
          reindexAlgEquiv (Polynomial A) (Polynomial A) b (Polynomial.C.mapMatrix P) +
          reindexAlgEquiv (Polynomial A) (Polynomial A) b T.charmatrix *
          reindexAlgEquiv (Polynomial A) (Polynomial A) b
            (Polynomial.C.mapMatrix P)).det
        rw [← map_mul, ← map_one (reindexAlgEquiv (Polynomial A) (Polynomial A) b),
          ← map_sub, ← map_add, Matrix.det_reindexAlgEquiv]
      _ = idempotentCharpoly (T0.map ρ) (P0.map ρ) := by
        unfold idempotentCharpoly
        rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
        congr 1
        rw [map_add, map_sub, map_one, map_mul]
        change 1 - (Polynomial.C.mapMatrix P0).map (Polynomial.map ρ) +
          T0.charmatrix.map (Polynomial.map ρ) *
            (Polynomial.C.mapMatrix P0).map (Polynomial.map ρ) = _
        rw [← Matrix.charmatrix_map]
        congr 2 <;> ext j k <;> simp
      _ = (R * T0.map ρ * Q).charpoly := by
        rw [← hQR]
        exact idempotentCharpoly_retract _ Q R hRQ
  · have : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    exact ⟨0, 0, Subsingleton.elim _ _⟩

end Matrix
