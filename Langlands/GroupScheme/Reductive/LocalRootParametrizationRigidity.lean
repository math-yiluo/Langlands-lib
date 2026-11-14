import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement

/-! # Scalar rigidity of local root parametrizations over arbitrary rings -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.NaturalLine

variable (R : CommRingCat.{u})

/-- A natural operation on the underlying sets of commutative `R`-algebras. -/
structure Operation where
  app : ∀ A : CommAlgCat.{u} R, A → A
  naturality : ∀ {A B : CommAlgCat.{u} R} (f : A ⟶ B) (a : A),
    app B (f.hom a) = f.hom (app A a)

variable {R}

/-- The substitution `X ↦ T^d` into the Laurent polynomial algebra. -/
def powerEvaluation (d : ℕ) : R[X] →ₐ[R] LaurentPolynomial R :=
  Polynomial.aeval (LaurentPolynomial.T (d : ℤ))

theorem powerEvaluation_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (powerEvaluation (R := R) d) := by
  have h : (powerEvaluation (R := R) d).toRingHom =
      (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R).comp
        (Polynomial.expand R d : R[X] →ₐ[R] R[X]).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [powerEvaluation, LaurentPolynomial.algebraMap_apply]
    · simp [powerEvaluation, Polynomial.toLaurent_X_pow]
  intro p q hpq
  have hpq' : (powerEvaluation (R := R) d).toRingHom p =
      (powerEvaluation (R := R) d).toRingHom q := hpq
  rw [h] at hpq'
  exact Polynomial.expand_injective hd (Polynomial.toLaurent_injective hpq')

/-- Commutation with one positive Laurent weight forces a natural scalar operation
on every algebra to be multiplication by its value at one over the base. -/
theorem Operation.eq_mul_of_laurent {d : ℕ} (hd : 0 < d) (F : Operation R)
    (hweight : F.app (CommAlgCat.of R (LaurentPolynomial R)) (LaurentPolynomial.T (d : ℤ)) =
      LaurentPolynomial.T (d : ℤ) *
        LaurentPolynomial.C (F.app (CommAlgCat.of R R) 1))
    (A : CommAlgCat.{u} R) (a : A) :
    F.app A a = algebraMap R A (F.app (CommAlgCat.of R R) 1) * a := by
  let P := F.app (CommAlgCat.of R R[X]) Polynomial.X
  have hP : P = Polynomial.C (F.app (CommAlgCat.of R R) 1) * Polynomial.X := by
    apply powerEvaluation_injective hd
    have h := F.naturality (CommAlgCat.ofHom (powerEvaluation (R := R) d)) Polynomial.X
    change F.app (CommAlgCat.of R (LaurentPolynomial R))
      (powerEvaluation d Polynomial.X) = powerEvaluation d P at h
    rw [powerEvaluation, Polynomial.aeval_X, hweight] at h
    unfold powerEvaluation
    rw [← h]
    simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    change LaurentPolynomial.T (d : ℤ) * LaurentPolynomial.C _ =
      LaurentPolynomial.C _ * LaurentPolynomial.T (d : ℤ)
    exact mul_comm _ _
  have h := F.naturality (CommAlgCat.ofHom (Polynomial.aeval a : R[X] →ₐ[R] A)) Polynomial.X
  change F.app A ((Polynomial.aeval a) Polynomial.X) = (Polynomial.aeval a) P at h
  rw [Polynomial.aeval_X, hP, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] at h
  exact h

end Langlands.GroupScheme.NaturalLine

namespace Langlands.GroupScheme.LocalSplitCell

open Corepresented.RingCoordinates

variable {R : Type u} [CommRing R]

/-- The function induced by an additive-group endomorphism on a coefficient algebra. -/
def scalarOperation (q : Ga R ⟶ Ga R) : NaturalLine.Operation (CommRingCat.of R) where
  app A a := (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (gaCoord (VectorGroup.scalarPoint (CommRingCat.of R) (specOver (CommRingCat.of R) A)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ≫ q.hom.hom))
  naturality {A B} f a := by
    let s := specMapOver f.hom
    have hs (x : Γ((specOver (CommRingCat.of R) A).left, ⊤)) :
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom (s.left.appTop x) =
          f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x) := by
      change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((Spec.map _).appTop x) = _
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
      rfl
    have hsi : s.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (f.hom a) := by
      apply (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
        (s.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f.hom a))
      rw [hs, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
    rw [← hs]
    congr 1
    have hc := congrFun (VectorGroup.coordinates_comp s
      (VectorGroup.scalarPoint (CommRingCat.of R) (specOver (CommRingCat.of R) A)
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ≫ q.hom.hom)) 0
    rw [← Category.assoc, VectorGroup.scalarPoint_comp, hsi] at hc
    exact hc

/-- A linear formula on all coefficient algebras determines the whole endomorphism. -/
theorem eq_scaleHom_of_scalarOperation {q : Ga R ⟶ Ga R} {c : R}
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A),
      (scalarOperation q).app A a = algebraMap R A c * a) : q = scaleHom c := by
  have H : q.hom.hom = (scaleHom c).hom.hom := by
    let A : CommAlgCat.{u} (CommRingCat.of R) :=
      CommAlgCat.of R (MvPolynomial (Fin 1) R)
    let Z := specOver (CommRingCat.of R) A
    have hZ : Z = (Ga R).X := rfl
    let a := (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (gaCoord (𝟙 (Ga R).X))
    have hq := h A a
    have ha : VectorGroup.scalarPoint (CommRingCat.of R) Z
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 𝟙 (Ga R).X := by
      rw [show (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = gaCoord (𝟙 (Ga R).X)
        from Iso.hom_inv_id_apply _ _]
      exact VectorGroup.scalarPoint_coordinate _ _
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (gaCoord (VectorGroup.scalarPoint (CommRingCat.of R) Z
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ≫ q.hom.hom)) = _ at hq
    rw [ha] at hq
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (gaCoord ((𝟙 (Ga R).X) ≫ q.hom.hom)) = _ at hq
    rw [Category.id_comp] at hq
    apply VectorGroup.points_ext
    intro j
    rw [Subsingleton.elim j 0]
    change gaCoord q.hom.hom = gaCoord (scaleHom c).hom.hom
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord q.hom.hom) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord (scaleHom c).hom.hom)
    rw [hq]
    have hc : (Scheme.ΓSpecIso (CommRingCat.of A)).hom (baseScalar Z c) =
        algebraMap R A c := by
      change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)) = _
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
        Iso.inv_hom_id_apply]
      rfl
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (baseScalar (Ga R).X c) =
      algebraMap R A c at hc
    have he := comp_scaleHom c (𝟙 (Ga R).X)
    rw [Category.id_comp] at he
    rw [he, gaCoord, VectorGroup.coordinates_scalarPoint, map_mul, hc]
  apply hom_ext_points
  intro Z a
  rw [H]

/-- On an affine test the base scalar has the prescribed algebra value. -/
theorem gamma_baseScalar (A : CommAlgCat.{u} (CommRingCat.of R)) (c : R) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (baseScalar (specOver (CommRingCat.of R) A) c) = algebraMap R A c := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)) = _
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]
  rfl

/-- The coefficient operation of a scaling map is multiplication. -/
theorem scalarOperation_scaleHom (c : R) (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A) :
    (scalarOperation (scaleHom c)).app A a = algebraMap R A c * a := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (gaCoord (VectorGroup.scalarPoint (CommRingCat.of R) (specOver (CommRingCat.of R) A)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ≫ (scaleHom c).hom.hom)) = _
  rw [comp_scaleHom, gaCoord, VectorGroup.coordinates_scalarPoint, map_mul,
    gamma_baseScalar]
  rw [gaCoord, VectorGroup.coordinates_scalarPoint, Iso.inv_hom_id_apply]

theorem scaleHom_injective : Function.Injective (scaleHom (R := R)) := by
  intro c c' h
  have H := congrArg
    (fun q => (scalarOperation q).app (CommAlgCat.of R R) 1) h
  simpa only [scalarOperation_scaleHom, Algebra.algebraMap_self, RingHom.id_apply,
    mul_one] using H

section Weight

variable {I : Type u} [Fintype I]

/-- Evaluation of a Laurent unit cocharacter retains the exact integer pairing. -/
theorem exponentValue_laurent (m ν : I → ℤ) :
    (splitTorus.exponentValue I
      (fun j => (unitOfInvertible (LaurentPolynomial.T (1 : ℤ) :
        LaurentPolynomial R)) ^ ν j) (Multiplicative.ofAdd m) : LaurentPolynomial R) =
      LaurentPolynomial.T (∑ j, m j * ν j) := by
  classical
  let z := unitOfInvertible (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial R)
  have hp (s : Finset I) :
      (∏ j ∈ s, (z ^ ν j) ^ m j) = z ^ (∑ j ∈ s, m j * ν j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, ← zpow_mul,
        mul_comm (ν j), zpow_add]
  change ((∏ j, (z ^ ν j) ^ m j : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = _
  rw [hp]
  have hz (n : ℤ) : ((z ^ n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T n := by
    cases n with
    | ofNat n => simp [z]
    | negSucc n =>
      simp only [zpow_negSucc]
      change LaurentPolynomial.T (-1 : ℤ) ^ (n + 1) =
        (LaurentPolynomial.T (Int.negSucc n) : LaurentPolynomial R)
      rw [LaurentPolynomial.T_pow]
      congr 1
      omega
  exact hz _

/-- Equivariance for a character of positive cocharacter degree forces scalar linearity. -/
theorem exists_scaleHom_of_weight (m ν : I → ℤ) {d : ℕ} (hd : 0 < d)
    (hpair : ∑ j, m j * ν j = (d : ℤ)) (q : Ga R ⟶ Ga R)
    (hq : ∀ (Z : Over (Spec (CommRingCat.of R)))
      (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
      rootPoint q Z (VectorGroup.charValue
        (splitTorus.exponentCharacter _ I m) Z t * c) =
      VectorGroup.scalarPoint _ Z (VectorGroup.charValue
        (splitTorus.exponentCharacter _ I m) Z t * gaCoord (rootPoint q Z c))) :
    ∃ c : R, q = scaleHom c := by
  let F := scalarOperation q
  let A : CommAlgCat.{u} (CommRingCat.of R) :=
    CommAlgCat.of R (LaurentPolynomial R)
  let t : specOver (CommRingCat.of R) A ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X :=
    Corepresented.torusPt I A (fun j =>
      unitOfInvertible (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial R) ^ ν j)
  have ht : (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (VectorGroup.charValue (splitTorus.exponentCharacter _ I m)
        (specOver (CommRingCat.of R) A) t) =
      LaurentPolynomial.T (d : ℤ) := by
    rw [Corepresented.charValue_torusPt, exponentValue_laurent, hpair]
  have hx : VectorGroup.charValue (splitTorus.exponentCharacter _ I m)
      (specOver (CommRingCat.of R) A) t =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (LaurentPolynomial.T (d : ℤ)) := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom _ =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom _
    rw [ht, Iso.inv_hom_id_apply]
  have hw := hq (specOver (CommRingCat.of R) A) t 1
  rw [mul_one, hx] at hw
  have H := congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord a)) hw
  simp only [gaCoord, VectorGroup.coordinates_scalarPoint, map_mul,
    Iso.inv_hom_id_apply] at H
  have H' : F.app A (LaurentPolynomial.T (d : ℤ)) =
      LaurentPolynomial.T (d : ℤ) * F.app A 1 := by
    simpa only [F, scalarOperation, rootPoint, gaCoord, map_one] using H
  have hn := F.naturality
    (CommAlgCat.ofHom (Algebra.ofId R (LaurentPolynomial R))) (1 : R)
  change F.app A (algebraMap R A 1) =
    algebraMap R A (F.app (CommAlgCat.of R R) 1) at hn
  rw [map_one] at hn
  rw [hn] at H'
  refine ⟨F.app (CommAlgCat.of R R) 1, eq_scaleHom_of_scalarOperation ?_⟩
  intro B b
  exact NaturalLine.Operation.eq_mul_of_laurent hd F H' B b

variable {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {m : I → ℤ}
  {u v : Ga R ⟶ G}

/-- Two actual equivariant parametrizations differ by a base-ring scalar. -/
theorem IsRootParametrization.exists_scalar (hu : IsRootParametrization i m u)
    (hv : IsRootParametrization i m v) (ν : I → ℤ) {d : ℕ} (hd : 0 < d)
    (hpair : ∑ j, m j * ν j = (d : ℤ)) :
    ∃ c : R, u = scaleHom c ≫ v := by
  let e := hu.represents.isoOfIsRepresentedBy hv.represents
  have he : e.hom ≫ v = u := hu.represents.isoOfIsRepresentedBy_hom_comp hv.represents
  have hc (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
      rootPoint e.hom Z c ≫ v.hom.hom = rootPoint u Z c := by
    rw [rootPoint, rootPoint, Category.assoc, ← Grp.comp_hom_hom, he]
  obtain ⟨c, hq⟩ := exists_scaleHom_of_weight m ν hd hpair e.hom (by
    intro Z t a
    let : Mono v.hom.hom := hv.represents.1
    apply (cancel_mono v.hom.hom).mp
    change rootPoint e.hom Z _ ≫ v.hom.hom = rootPoint v Z _
    have hcoord : rootPoint v Z (gaCoord (rootPoint e.hom Z a)) = rootPoint u Z a := by
      rw [rootPoint, VectorGroup.scalarPoint_coordinate]
      exact hc Z a
    rw [hc, ← hu.equivariant, ← hv.equivariant, hcoord])
  exact ⟨c, he.symm.trans (congrArg (fun q => q ≫ v) hq)⟩

/-- A root parametrization detects the scalar of a preceding scaling map. -/
theorem IsRootParametrization.scaleHom_comp_injective
    (hv : IsRootParametrization i m v) :
    Function.Injective (fun c : R => scaleHom c ≫ v) := by
  intro c c' h
  apply scaleHom_injective
  apply hom_ext_points
  intro Z a
  let : Mono v.hom.hom := hv.represents.1
  apply (cancel_mono v.hom.hom).mp
  have H := congrArg (fun q => q.hom.hom) h
  simp only [Grp.comp_hom_hom] at H
  simpa only [Category.assoc] using congrArg (fun q => a ≫ q) H

/-- Two root parametrizations of positive cocharacter degree differ by a unique unit. -/
theorem IsRootParametrization.existsUnique_unit (hu : IsRootParametrization i m u)
    (hv : IsRootParametrization i m v) (ν : I → ℤ) {d : ℕ} (hd : 0 < d)
    (hpair : ∑ j, m j * ν j = (d : ℤ)) :
    ∃! c : Rˣ, u = scaleHom (c : R) ≫ v := by
  obtain ⟨c, hc⟩ := hu.exists_scalar hv ν hd hpair
  obtain ⟨b, hb⟩ := hv.exists_scalar hu ν hd hpair
  have hcb : c * b = 1 := by
    apply hv.scaleHom_comp_injective
    calc
      scaleHom (c * b) ≫ v = (scaleHom b ≫ scaleHom c) ≫ v := by
        rw [scaleHom_comp_scaleHom]
      _ = v := by rw [Category.assoc, ← hc, ← hb]
      _ = scaleHom 1 ≫ v := by rw [scaleHom_one, Category.id_comp]
  let w : Rˣ := ⟨c, b, hcb, (mul_comm b c).trans hcb⟩
  refine ⟨w, hc, ?_⟩
  intro w' hw'
  apply Units.ext
  exact hv.scaleHom_comp_injective (hw'.symm.trans hc)

/-- For an actual fibrewise root datum over a local ring, no extra pairing data
are needed: the root-coroot pairing is the positive integer two. -/
theorem IsRootParametrization.existsUnique_unit_of_rootDatum [IsLocalRing R]
    [IsAffineHom G.X.hom]
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hu : IsRootParametrization i (P.root α) u)
    (hv : IsRootParametrization i (P.root α) v) :
    ∃! c : Rˣ, u = scaleHom (c : R) ≫ v := by
  apply hu.existsUnique_unit hv (P.coroot α) (d := 2) two_pos
  rw [← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
  rfl

/-- The unique unit comparing two parametrizations of the same actual root. -/
def IsRootParametrization.comparisonUnit [IsLocalRing R] [IsAffineHom G.X.hom]
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hu : IsRootParametrization i (P.root α) u)
    (hv : IsRootParametrization i (P.root α) v) : Rˣ :=
  (hu.existsUnique_unit_of_rootDatum hP α hv).exists.choose

theorem IsRootParametrization.comparisonUnit_spec [IsLocalRing R] [IsAffineHom G.X.hom]
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hu : IsRootParametrization i (P.root α) u)
    (hv : IsRootParametrization i (P.root α) v) :
    u = scaleHom (hu.comparisonUnit hP α hv : R) ≫ v :=
  (hu.existsUnique_unit_of_rootDatum hP α hv).exists.choose_spec

end Weight

end Langlands.GroupScheme.LocalSplitCell
