/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.Regular.RegularSequenceGradedPolynomial
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.ConormalRegular
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.RingTheory.Regular.RegularSequenceHigherRelations

/-!
# Conormal coordinates for an affine regular ideal

Source: Stacks Tags 00LN, 0631--0633 and 01R3.
(blueprint: lem-sc-regular-ideal-conormal-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ConormalGradedAlgebra

private theorem cotangent_independent {R : Type u} [CommRing R] {d : ℕ}
    (x : Fin d → R) (hx : RingTheory.Sequence.IsRegular R (List.ofFn x)) :
    LinearIndependent (R ⧸ Ideal.span (Set.range x)) (MvPolynomial.cotangentFamily x) := by
  classical
  let I := Ideal.span (Set.range x)
  refine Fintype.linearIndependent_iff.2 fun g hg k ↦ ?_
  choose r hr using fun j ↦ Ideal.Quotient.mk_surjective (g j)
  have hsum : (∑ j, r j * x j) ∈ I ^ 2 := by
    rw [← Ideal.toCotangent_eq_zero I ⟨_, Submodule.sum_mem _ fun j _ ↦
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)⟩]
    have he : (⟨∑ j, r j * x j, Submodule.sum_mem _ fun j _ ↦
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)⟩ : I) =
        ∑ j, r j • (⟨x j, Ideal.subset_span ⟨j, rfl⟩⟩ : I) := by
      ext
      simp
    rw [he, map_sum]
    simp_rw [map_smul]
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hr j, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rfl
  let F : MvPolynomial (Fin d) R := ∑ j, MvPolynomial.C (r j) * MvPolynomial.X j
  have hF : F.IsHomogeneous 1 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ ↦ MvPolynomial.isHomogeneous_C_mul_X _ _
  have hev : F.eval x ∈ I ^ (1 + 1) := by simpa [F] using hsum
  have hk := MvPolynomial.coeff_mem_of_eval_mem_pow_succ_of_eval_eq_zero
    (fun p hp hp0 ↦ Ideal.regularSequence_homogeneous_relation x hx 1 p hp hp0)
    hF hev (Finsupp.single k 1)
  have hcoeff : F.coeff (Finsupp.single k 1) = r k := by
    simp only [F, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X, Finsupp.single_eq_single_iff]
    simp [Finset.sum_ite_eq']
  rw [hcoeff] at hk
  rw [← hr k]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hk

private noncomputable def cotangentBasis {R : Type u} [CommRing R] {d : ℕ}
    (x : Fin d → R) (hx : RingTheory.Sequence.IsRegular R (List.ofFn x)) :
    Module.Basis (Fin d) (R ⧸ Ideal.span (Set.range x))
      (Ideal.span (Set.range x)).Cotangent :=
  Module.Basis.mk (cotangent_independent x hx) (MvPolynomial.span_cotangentFamily x).ge

private theorem exists_cotangent_basis {R : Type u} [CommRing R] {d : ℕ}
    (x : Fin d → R) (hx : RingTheory.Sequence.IsRegular R (List.ofFn x))
    (I : Ideal R) (hI : Ideal.span (Set.range x) = I) :
    ∃ b : Module.Basis (Fin d) (R ⧸ I) I.Cotangent,
      ∀ j, b j = I.toCotangent ⟨x j, hI ▸ Ideal.subset_span ⟨j, rfl⟩⟩ := by
  subst I
  exact ⟨cotangentBasis x hx, fun j ↦ Module.Basis.mk_apply _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem polynomial_monomial {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (d : Fin c →₀ ℕ) :
    ∃ x : (Ideal.span (Set.range f) ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      Ideal.regularSequenceGradedPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (Ideal.associatedGradedPiece (Ideal.span (Set.range f))) d.degree
          (Submodule.Quotient.mk x) := by
  classical
  let J := Ideal.span (Set.range f)
  let P := fun d : Fin c →₀ ℕ ↦
    ∃ x : (J ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      Ideal.regularSequenceGradedPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (Ideal.associatedGradedPiece J) d.degree (Submodule.Quotient.mk x)
  have hzero : P 0 := by
    refine ⟨⟨1, by simp⟩, by simp, ?_⟩
    change Ideal.regularSequenceGradedPolynomialMap f 1 = _
    rw [map_one]
    exact Ideal.associatedGraded_one J
  have hadd (d e : Fin c →₀ ℕ) (hd : P d) (he : P e) : P (d + e) := by
    obtain ⟨x, hx, hx'⟩ := hd
    obtain ⟨y, hy, hy'⟩ := he
    dsimp only [P]
    rw [Finsupp.degree.map_add]
    refine ⟨⟨x.val * y.val, by simpa [pow_add] using Ideal.mul_mem_mul x.property y.property⟩,
      ?_, ?_⟩
    · change x.val * y.val = _
      rw [hx, hy, Finsupp.prod_add_index]
      · intro a ha; simp
      · intro a ha b₁ b₂; exact pow_add _ _ _
    · rw [← one_mul (1 : R ⧸ J), ← MvPolynomial.monomial_mul_monomial, map_mul, hx', hy']
      exact Ideal.associatedGraded_mul J _ _ x y
  have hsingle (j : Fin c) : P (Finsupp.single j 1) := by
    dsimp only [P]
    rw [Finsupp.degree_single]
    refine ⟨⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩,
      by simp, ?_⟩
    change Ideal.regularSequenceGradedPolynomialMap f (MvPolynomial.X j) = _
    exact MvPolynomial.aeval_X (R := R ⧸ J) (S₁ := Ideal.associatedGraded J) _ j
  change P d
  induction d using Finsupp.induction_linear with
  | zero => exact hzero
  | add d e hd he => exact hadd d e hd he
  | single j k =>
    induction k with
    | zero => simpa using hzero
    | succ k hk =>
      simpa only [Finsupp.single_add] using hadd _ _ hk (hsingle j)

set_option backward.isDefEq.respectTransparency false in
private theorem lift_power {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s]
    (U : V.affineOpens) (n : ℕ) (r : Γ(V, U.1)) (hr : r ∈ s.ker.ideal U ^ n) :
    ∃ a : (power s n).val.obj (op U.1),
      (powerInclusion s n).val.app (op U.1) a = r := by
  obtain ⟨e, he⟩ := (presentation s).powerIdentification n
  have hm : r ∈ Set.range ((s.ker ^ n).toModulesι.app U.1) := by
    rw [(s.ker ^ n).range_toModulesι_app U]
    simpa using hr
  obtain ⟨a, ha⟩ := hm
  refine ⟨e.inv.val.app (op U.1) a, ?_⟩
  have hh : e.inv ≫ powerInclusion s n = (s.ker ^ n).toModulesι := by
    rw [← he, e.inv_hom_id_assoc]
  exact (congrArg (fun f ↦ f.val.app (op U.1) a) hh).trans ha

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

set_option backward.isDefEq.respectTransparency false in
/-- Regular affine generators give a conormal frame and the polynomial multiplication
comparison. Its monomials are represented by the actual coordinate products.
Source: Stacks Tags 00LN, 0631--0633 and 01R3.
(blueprint: lem-sc-regular-ideal-conormal-coordinates).

Proof: The regular-sequence graded-polynomial theorem identifies the associated
graded ring with the polynomial ring over the section quotient. Its degree-one
part gives the basis of I/I² consisting of the generator classes. The canonical
affine conormal comparison transports this basis to sections of the conormal
piece, preserving the classes of the actual ideal sections. Sheafify the basis
on the affine inverse image to get the free structure-module frame. On this
affine open the symmetric-algebra sheaf agrees with the symmetric algebra of
sections. The basis identifies this symmetric algebra with the polynomial ring.
The canonical symmetric comparison and the regular-sequence polynomial map
agree on scalars and each variable, hence on every polynomial; both affine
comparisons are isomorphisms, so its section map is bijective. The product law
of the conormal presentation gives the asserted representative of each monomial
by induction on its exponent vector. This includes degree zero, d = 0 and empty
inverse image; no nonzero hypothesis on the quotient is used separately. -/
theorem regular_ideal_conormal_coordinates {V S : Scheme.{u}}
    (s : S ⟶ V) [IsClosedImmersion s] (U : V.affineOpens) (d : ℕ)
    (x : Fin d → Γ(V, U.1))
    (hI : Ideal.span (Set.range x) = s.ker.ideal U)
    (hreg : RingTheory.Sequence.IsRegular Γ(V, U.1) (List.ofFn x)) :
    ∃ (coordinateLift : Fin d → (ConormalGradedAlgebra.power s 1).val.obj (op U.1))
      (conormalBasis : Module.Basis (Fin d) Γ(S, s ⁻¹ᵁ U.1)
    ((ConormalGradedAlgebra.piece s 1).val.obj (op (s ⁻¹ᵁ U.1)))),
      (∀ j : Fin d,
    (ConormalGradedAlgebra.powerInclusion s 1).val.app (op U.1) (coordinateLift j) = x j) ∧
      (∀ j : Fin d,
    conormalBasis j = ConormalGradedAlgebra.representative s 1 U.1 (coordinateLift j)) ∧
      (∀ α : Fin d →₀ ℕ,
    ∃ a : (ConormalGradedAlgebra.power s α.degree).val.obj (op U.1),
      (ConormalGradedAlgebra.powerInclusion s α.degree).val.app (op U.1) a =
          α.prod (fun j k ↦ x j ^ k) ∧
      (ConormalGradedAlgebra.symmetricComparison s).right.hom.app (op (s ⁻¹ᵁ U.1))
          (α.prod (fun j k ↦
            (@id ((SymmetricAlgebraSheaf.algebra (ConormalGradedAlgebra.piece s 1)).right.obj.obj
              (op (s ⁻¹ᵁ U.1)))
              ((SymmetricAlgebraSheaf.inclusion (ConormalGradedAlgebra.piece s 1)).val.app
                (op (s ⁻¹ᵁ U.1)) (conormalBasis j))) ^ k)) =
        ConormalGradedAlgebra.homogeneousClass s
          (ConormalGradedAlgebra.presentation s).algebra
          (ConormalGradedAlgebra.presentation s).inclusion α.degree U.1 a) ∧
      Nonempty ((piece s 1).over (s ⁻¹ᵁ U.1) ≅
        SheafOfModules.free (ULift.{u} (Fin d))) ∧
      Function.Bijective ((symmetricComparison s).right.hom.app (op (s ⁻¹ᵁ U.1)))  := by
  classical
  let I := s.ker.ideal U
  have hc : Ideal.span (Set.range x) = I := hI
  obtain ⟨bI, hbI⟩ := exists_cotangent_basis x hreg I hc
  let N := piece s 1
  obtain ⟨e, he⟩ := (Scheme.Modules.affine_conormal_sections.{u, u} s).2 U Γ(V, U.1)
    (RingEquiv.refl _) I (by simp [I])
  let q : (Γ(V, U.1) ⧸ I) ≃+* Γ(S, s ⁻¹ᵁ U.1) :=
    (Ideal.quotEquivOfEq (s.ker_apply U)).trans
      ((s.app U.1).hom.quotientKerEquivOfSurjective (s.app_surjective U.1 U.2))
  have hqmk (a : Γ(V, U.1)) : q (Ideal.Quotient.mk I a) = s.app U.1 a := by
    simp [q, I]
  let Eadd : (Fin d →₀ Γ(S, s ⁻¹ᵁ U.1)) ≃+ Γ(N, s ⁻¹ᵁ U.1) :=
    (Finsupp.mapRange.addEquiv q.symm.toAddEquiv).trans
      (bI.repr.symm.toAddEquiv.trans e.toAddEquiv)
  let E : (Fin d →₀ Γ(S, s ⁻¹ᵁ U.1)) ≃ₗ[Γ(S, s ⁻¹ᵁ U.1)] Γ(N, s ⁻¹ᵁ U.1) :=
    { Eadd with
      map_smul' := by
        intro a v
        obtain ⟨a, rfl⟩ := s.app_surjective U.1 U.2 a
        have hqa : q.symm (s.app U.1 a) = Ideal.Quotient.mk I a :=
          q.symm_apply_eq.mpr (hqmk a).symm
        have hmap : Finsupp.mapRange q.symm q.symm.map_zero ((s.app U.1 a) • v) =
            (Ideal.Quotient.mk I a) • Finsupp.mapRange q.symm q.symm.map_zero v := by
          ext j
          simp [hqa]
        change e (bI.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero
          ((s.app U.1 a) • v))) = (s.app U.1 a) •
            (show Γ(N, s ⁻¹ᵁ U.1) from
              e (bI.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero v)))
        rw [hmap, bI.repr.symm.map_smul]
        change e (a • bI.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero v)) =
          a • e (bI.repr.symm (Finsupp.mapRange q.symm q.symm.map_zero v))
        exact e.map_smul a _ }
  let b : Module.Basis (Fin d) Γ(S, s ⁻¹ᵁ U.1) Γ(N, s ⁻¹ᵁ U.1) := .ofRepr E.symm
  have hmem (j : Fin d) : x j ∈ I := hc ▸ Ideal.subset_span ⟨j, rfl⟩
  have hl (j : Fin d) : ∃ a : (power s 1).val.obj (op U.1),
      (powerInclusion s 1).val.app (op U.1) a = x j := by
    have hr : x j ∈ Set.range (s.ker.toModulesι.app U.1) := by
      rw [s.ker.range_toModulesι_app U]
      exact hmem j
    exact hr
  choose l hl using hl
  have hb (j : Fin d) : b j = representative s 1 U.1 (l j) := by
    change e (bI.repr.symm
      (Finsupp.mapRange q.symm q.symm.map_zero (Finsupp.single j 1))) = _
    rw [Finsupp.mapRange_single, map_one, Module.Basis.repr_symm_single, one_smul, hbI]
    exact he ⟨x j, hmem j⟩ (l j) (hl j)
  let A := presentation s
  let W := s ⁻¹ᵁ U.1
  let P := SymmetricAlgebraSheaf.algebra N
  let ψ := (symmetricComparison s).right.hom.app (op W)
  let qJ : (Γ(V, U.1) ⧸ Ideal.span (Set.range x)) ≃+* Γ(S, W) :=
    (Ideal.quotEquivOfEq hI).trans q
  have hqJ (a : Γ(V, U.1)) :
      qJ (Ideal.Quotient.mk (Ideal.span (Set.range x)) a) = s.app U.1 a := by
    simpa only [qJ, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk] using hqmk a
  have hchart := A.affineChart U
  rw [← hI] at hchart
  obtain ⟨eG, heG⟩ := hchart
  let φ : MvPolynomial (Fin d) (Γ(V, U.1) ⧸ Ideal.span (Set.range x)) →+*
      P.right.obj.obj (op W) :=
    MvPolynomial.eval₂Hom ((P.hom.hom.app (op W)).hom.comp qJ.toRingHom)
      (fun j ↦ (SymmetricAlgebraSheaf.inclusion N).val.app (op W) (b j))
  have hφC (r : Γ(V, U.1) ⧸ Ideal.span (Set.range x)) :
      φ (MvPolynomial.C r) = (P.hom.hom.app (op W)) (qJ r) := by
    exact MvPolynomial.eval₂Hom_C _ _ _
  have hφX (j : Fin d) : φ (MvPolynomial.X j) =
      (SymmetricAlgebraSheaf.inclusion N).val.app (op W) (b j) := by
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have hqc : N.IsQuasicoherent := A.pieceQuasicoherent 1
  have hsection := (quasiCoherentSymmetricAlgebra_affine_comparison S N).2
    ⟨W, U.2.preimage s⟩
  have hφ : Function.Bijective φ := by
    let ep := (MvPolynomial.mapEquiv (Fin d) qJ).trans
      (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv
    have hh : φ = (SymmetricAlgebraSheaf.sectionMap N (op W)).comp ep.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        rw [hφC]
        change _ = SymmetricAlgebraSheaf.sectionMap N (op W) (ep (MvPolynomial.C r))
        change (P.hom.hom.app (op W)) (qJ r) =
          SymmetricAlgebraSheaf.sectionMap N (op W) (ep (MvPolynomial.C r))
        simp only [ep, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply,
          MvPolynomial.map_C, AlgEquiv.coe_toRingEquiv]
        exact (congrArg (SymmetricAlgebraSheaf.sectionMap N (op W))
          ((SymmetricAlgebra.equivMvPolynomial b).symm.commutes (qJ r))).symm
      · intro j
        rw [hφX]
        change _ = SymmetricAlgebraSheaf.sectionMap N (op W) (ep (MvPolynomial.X j))
        change (SymmetricAlgebraSheaf.inclusion N).val.app (op W) (b j) = _
        simp only [ep, RingHom.comp_apply, RingEquiv.trans_apply,
          RingEquiv.coe_toRingHom, MvPolynomial.mapEquiv_apply, MvPolynomial.map_X,
          AlgEquiv.coe_toRingEquiv]
        exact (congrArg (SymmetricAlgebraSheaf.sectionMap N (op W))
          (SymmetricAlgebra.equivMvPolynomial_symm_X b j)).symm
    rw [hh]
    exact hsection.comp ep.bijective
  have hψ (a : N.val.obj (op W)) :
      ψ ((SymmetricAlgebraSheaf.inclusion N).val.app (op W) a) =
        (A.inclusion 1).val.app (op W) a := by
    exact A.symmetricComparison.exists.choose_spec W a
  have hcomp : eG.hom.hom.comp (ψ.hom.comp φ) =
      (Ideal.regularSequenceGradedPolynomialMap x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change eG.hom (ψ (φ (MvPolynomial.C
        (Ideal.Quotient.mk (Ideal.span (Set.range x)) r)))) = _
      erw [hφC]
      rw [hqJ]
      have hcψ : ψ ((P.hom.hom.app (op W)) (s.app U.1 r)) =
          A.algebra.hom.hom.app (op W) (s.app U.1 r) := by
        exact congrArg (fun f ↦ f.hom.app (op W) (s.app U.1 r))
          (symmetricComparison s).w
      rw [hcψ, ← A.constants U.1 r]
      obtain ⟨hr, h⟩ := heG 0 r
      apply h.trans
      symm
      change MvPolynomial.aeval _ (MvPolynomial.C _) = _
      rw [MvPolynomial.aeval_C]
      rfl
    · intro j
      change eG.hom (ψ (φ (MvPolynomial.X j))) = _
      erw [hφX]
      rw [hψ, hb]
      obtain ⟨hj, h⟩ := heG 1 (l j)
      change eG.hom (homogeneousClass s A.algebra A.inclusion 1 U.1 (l j)) = _
      rw [h]
      change DirectSum.of (Ideal.associatedGradedPiece (Ideal.span (Set.range x))) 1
        (Submodule.Quotient.mk ⟨(powerInclusion s 1).val.app (op U.1) (l j), hj⟩) = _
      simp only [hl]
      symm
      exact MvPolynomial.aeval_X (R := Γ(V, U.1) ⧸ Ideal.span (Set.range x))
        (S₁ := Ideal.associatedGraded (Ideal.span (Set.range x))) _ j
  have hθ := (Ideal.regularSequence_gradedPolynomial x hreg).1
  have hbij : Function.Bijective ψ := by
    have ht : Function.Bijective (fun p ↦ eG.hom (ψ (φ p))) := by
      change Function.Bijective (eG.hom.hom.comp (ψ.hom.comp φ))
      rw [hcomp]
      exact hθ
    constructor
    · intro a a' haa
      obtain ⟨p, rfl⟩ := hφ.2 a
      obtain ⟨p', rfl⟩ := hφ.2 a'
      exact congrArg φ (ht.1 (congrArg eG.hom haa))
    · intro y
      obtain ⟨p, hp⟩ := ht.2 (eG.hom y)
      exact ⟨φ p, (ConcreteCategory.bijective_of_isIso eG.hom).1 hp⟩
  refine ⟨l, b, hl, hb, ?_, (affine_conormal_frame s U d bI).1, hbij⟩
  intro α
  obtain ⟨z, hz, hz'⟩ := polynomial_monomial x α
  obtain ⟨a, ha⟩ := lift_power s U α.degree z.val (hI ▸ z.property)
  refine ⟨a, ha.trans hz, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso eG.hom).1
  have hc := congrArg (fun f ↦ f (MvPolynomial.monomial α 1)) hcomp
  have hφα : φ (MvPolynomial.monomial α 1) =
      α.prod (fun j k ↦
        (@id (P.right.obj.obj (op W))
          ((SymmetricAlgebraSheaf.inclusion N).val.app (op W) (b j))) ^ k) := by
    simp [φ, MvPolynomial.eval₂Hom_monomial]
  change eG.hom (ψ _) = _
  change eG.hom (ψ (φ (MvPolynomial.monomial α 1))) = _ at hc
  rw [hφα] at hc
  exact hc.trans (hz'.trans (by
    obtain ⟨hpa, hclass⟩ := heG α.degree a
    apply Eq.trans ?_ hclass.symm
    congr 2
    exact Subtype.ext ha.symm))

end AlgebraicGeometry.ConormalGradedAlgebra
