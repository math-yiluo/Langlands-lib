import Langlands.GroupScheme.Reductive.LocalSplitCommutatorPolynomials

/-! # Positive weight bounds for commutators on every scheme test -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Polynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

section Evaluation

variable {R : Type u} [CommRing R]

/-- Evaluation of the two universal coordinates at global sections of any test. -/
def lineEvalSections (Z : Over (Spec (CommRingCat.of R)))
    (x y : Γ(Z.left, ⊤)) : Polynomial (Polynomial R) →+* Γ(Z.left, ⊤) :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Gm.specHomEquiv Z.left (CommRingCat.of R) Z.hom).hom x) y

/-- The map to the universal two-variable line classifying two global sections. -/
def commutatorLinePoint (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)) :
    Z ⟶ Over.mk (lineBase R) :=
  Over.homMk ((Gm.specHomEquiv Z.left _).symm
    (CommRingCat.ofHom (lineEvalSections Z x y))) (by
      apply (Gm.specHomEquiv Z.left (CommRingCat.of R)).injective
      change (Scheme.ΓSpecIso _).inv ≫
        (Z.left.toSpecΓ ≫ Spec.map _ ≫ Spec.map _).appTop = _
      rw [← Spec.map_comp]
      change Gm.specHomEquiv Z.left _ ((Gm.specHomEquiv Z.left _).symm _) = _
      rw [Equiv.apply_symm_apply]
      ext a
      simp [lineEvalSections])

theorem commutatorLinePoint_appTop (Z : Over (Spec (CommRingCat.of R)))
    (x y : Γ(Z.left, ⊤)) (f : Polynomial (Polynomial R)) :
    (commutatorLinePoint Z x y).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial R)))).inv f) =
      lineEvalSections Z x y f := by
  have h := Equiv.apply_symm_apply
    (Gm.specHomEquiv Z.left (CommRingCat.of (Polynomial (Polynomial R))))
    (CommRingCat.ofHom (lineEvalSections Z x y))
  exact congrArg (fun ψ => ψ.hom f) h

variable {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))}
    {u : J → (Ga R ⟶ G)} {n : ℕ} {pos : Fin n → J}

/-- Universal commutator polynomials specialize on every scheme, without an
affineness assumption on that scheme. -/
theorem IsUnivComm.posComm_eq_sections {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E)
    (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)) :
    posComm u pos Z k l x y =
      orderedProduct u pos Z (fun p => lineEvalSections Z x y (E p)) := by
  have h := congrArg (fun z => commutatorLinePoint Z x y ≫ z) hE
  rw [comp_posComm, comp_orderedProduct] at h
  rw [commutatorLinePoint_appTop Z x y (C X),
    commutatorLinePoint_appTop Z x y X] at h
  have hz : (fun p => (commutatorLinePoint Z x y).left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial R)))).inv (E p))) =
      (fun p => lineEvalSections Z x y (E p)) := by
    funext p
    exact commutatorLinePoint_appTop Z x y (E p)
  rw [hz] at h
  simpa [lineEvalSections] using h

end Evaluation

section Height

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
    {G : GroupScheme (Spec (CommRingCat.of R))}
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
    {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

/-- Pairing a nonzero commutator monomial with any cocharacter gives its degree. -/
theorem IsUnivComm.coPairing_eq [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E)
    (ν : I → ℤ) (p : Fin n) {dS dT : ℕ}
    (h : ((E p).coeff dT).coeff dS ≠ 0) :
    (dS : ℤ) * coPairing (ch (pos k)) ν +
        (dT : ℤ) * coPairing (ch (pos l)) ν =
      coPairing (ch (pos p)) ν :=
  weight_eq_of_scaleST_eq (hE.scaleST_eq (neg := neg) hu ν p) h

/-- Coordinates below the sum of two nonnegative weights vanish identically. -/
theorem IsUnivComm.eq_zero_of_coPairing_lt_add
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E)
    (ν : I → ℤ)
    (hk : 0 ≤ coPairing (ch (pos k)) ν)
    (hl : 0 ≤ coPairing (ch (pos l)) ν) (p : Fin n)
    (hp : coPairing (ch (pos p)) ν <
      coPairing (ch (pos k)) ν + coPairing (ch (pos l)) ν) : E p = 0 := by
  ext dT dS
  rw [Polynomial.coeff_zero, Polynomial.coeff_zero]
  by_contra h
  obtain ⟨hS, hT⟩ := hE.one_le (i := i) (neg := neg) p h
  have hS' : (1 : ℤ) ≤ dS := by exact_mod_cast hS
  have hT' : (1 : ℤ) ≤ dT := by exact_mod_cast hT
  have hw := hE.coPairing_eq (neg := neg) hu ν p h
  have h1 := mul_le_mul_of_nonneg_right hS' hk
  have h2 := mul_le_mul_of_nonneg_right hT' hl
  simp only [one_mul] at h1 h2
  omega

/-- A commutator has ordered coordinates supported in weights at least the sum
of the two input weights, on every scheme test. -/
theorem exists_posComm_eq_weight_ge
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ p, coPairing (ch (neg p)) ν < 0)
    (hpos : ∀ p, 0 < coPairing (ch (pos p)) ν)
    (k l : Fin n) (Z : Over (Spec (CommRingCat.of R)))
    (x y : Γ(Z.left, ⊤)) :
    ∃ z : Fin n → Γ(Z.left, ⊤),
      posComm u pos Z k l x y = orderedProduct u pos Z z ∧
        ∀ p, coPairing (ch (pos p)) ν <
          coPairing (ch (pos k)) ν + coPairing (ch (pos l)) ν → z p = 0 := by
  obtain ⟨E, hE⟩ := exists_isUnivComm (i := i) (neg := neg) hu ν hneg hpos k l
  refine ⟨fun p => lineEvalSections Z x y (E p), hE.posComm_eq_sections Z x y, ?_⟩
  intro p hp
  change lineEvalSections Z x y (E p) = 0
  rw [hE.eq_zero_of_coPairing_lt_add (neg := neg) hu ν
    (hpos k).le (hpos l).le p hp, map_zero]

end Height

end Langlands.GroupScheme.LocalSplitCell
