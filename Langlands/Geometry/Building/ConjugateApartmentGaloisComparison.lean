import Langlands.Geometry.Building.ConjugateApartmentIndependence
import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.TorusConjugatorGaloisCocycle

/-! # Coefficient equivariance of actual conjugate-apartment comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "T'_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T'
local notation "G_K" => baseChanged k K G

/-- Canonical coefficient transport of an isomorphism between two descended
commutative group schemes. -/
def torusIsoGaloisTransport (σ : K ≃ₐ[k] K) (e : T_K ≅ T'_K) : T_K ≅ T'_K :=
  (CommGroupScheme.descentBaseChangeIso b (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) T).symm ≪≫
    (CommGroupScheme.baseChange (galoisBaseMap k K σ)).mapIso e ≪≫
    CommGroupScheme.descentBaseChangeIso b (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) T'

/-- Character transport commutes with the transported torus isomorphism. -/
theorem characterCongr_torusIsoGaloisTransport (σ : K ≃ₐ[k] K)
    (e : T_K ≅ T'_K) (a : characterLattice T_K) :
    characterLattice.congr (torusIsoGaloisTransport k K σ e)
        (characterLattice.galoisRepresentation k K T σ a) =
      characterLattice.galoisRepresentation k K T' σ (characterLattice.congr e a) := by
  rw [characterLattice.congr_apply, characterLattice.congr_apply]
  exact StarActionIndependence.descentTransport_inv_comp b (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) e a

variable (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G)
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

/-- The actual coefficient conjugate of a transporter still transports the
two original descended torus inclusions. -/
theorem conjugateTorusSquare_galois (σ : K ≃ₐ[k] K)
    (e : T_K ≅ T'_K) (g : rationalPoints G_K)
    (h : i_K ≫ (GroupScheme.innerIso G_K g).hom = CommGroupScheme.groupHom e.hom ≫ j_K) :
    i_K ≫ (GroupScheme.innerIso G_K (rationalConjugate k K G σ g)).hom =
      CommGroupScheme.groupHom (torusIsoGaloisTransport k K σ e).hom ≫ j_K := by
  have hh : StarActionIndependence.IsConjugatingPoint
      (C := T_K) (C' := T'_K) i_K j_K g e := h
  exact hh.baseChange_descent_of_eq b (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) i j
    (rationalConjugate_eq_baseChange_descent k K σ g)

namespace RootFunctionFamily

/-- Coefficient transport of a conjugate valuation family uses precisely the
coefficient-conjugated point and the canonically transported torus map. -/
theorem galoisAction_transport_inner (σ : K ≃ₐ[k] K)
    (e : T_K ≅ T'_K) (g : rationalPoints G_K) (φ : RootFunctionFamily T_K G_K) :
    galoisAction k K T' G σ (transportEquiv e (GroupScheme.innerIso G_K g) φ) =
      transportEquiv (torusIsoGaloisTransport k K σ e)
        (GroupScheme.innerIso G_K (rationalConjugate k K G σ g))
        (galoisAction k K T G σ φ) := by
  apply RootFunctionFamily.ext
  intro a u
  obtain ⟨a, rfl⟩ := (Representation.apply_bijective
    (characterLattice.galoisRepresentation k K T') σ).2 a
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
  obtain ⟨u, rfl⟩ := (rationalConjugate k K G σ).surjective u
  let u₀ := g⁻¹ * u * g
  have hu₀ : rationalPoints.map (GroupScheme.innerIso G_K g).hom u₀ = u := by
    simp only [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self]
    dsimp [u₀]
    group
  rw [← hu₀]
  have hu : rationalConjugate k K G σ
        (rationalPoints.map (GroupScheme.innerIso G_K g).hom u₀) =
      rationalPoints.map
        (GroupScheme.innerIso G_K (rationalConjugate k K G σ g)).hom
        (rationalConjugate k K G σ u₀) := by
    simp only [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self,
      map_mul, map_inv]
  rw [galoisAction_apply_conjugate,
    ← characterCongr_torusIsoGaloisTransport k K σ e, hu,
    transportEquiv_apply_map, transportEquiv_apply_map, galoisAction_apply_conjugate]

end RootFunctionFamily

namespace KPApartmentData

variable [IsAffineHom G.X.hom]
  [Mono (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  [Mono (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) j).hom.hom.left]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {ω : Kˣ → ℝ}
  (e : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
    (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T')
  (g : rationalPoints (baseChanged k K G))
  (h : (GroupScheme.baseChange (algebraBaseMap k K)).map i ≫
      (GroupScheme.innerIso (baseChanged k K G) g).hom =
    CommGroupScheme.groupHom e.hom ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map j)
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)
  (hD : GaloisStable k K i D)

include hD in
/-- Actual conjugate apartment data inherits coefficient stability from the
original apartment, by independence of the chosen transporter. -/
theorem galoisStable_transport_inner :
    GaloisStable k K j (D.transport e (GroupScheme.innerIso G_K g) h) := by
  intro σ φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  rw [RootFunctionFamily.galoisAction_transport_inner]
  have hind := D.transport_conjugation_independent
    (torusIsoGaloisTransport k K σ e) e
    (rationalConjugate k K G σ g) g
    (conjugateTorusSquare_galois k K i j σ e g h) h
  rw [← hind]
  exact ⟨RootFunctionFamily.galoisAction k K T G σ ψ, hD σ ψ hψ, rfl⟩

variable (hE : GaloisStable k K j
  (D.transport e (GroupScheme.innerIso (baseChanged k K G) g) h))

/-- The actual coefficient action on a conjugate apartment agrees with transport
by the coefficient-conjugated transporter, followed by identity on families. -/
theorem galoisAction_apartmentTransport_inner (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    galoisAction k K j (D.transport e (GroupScheme.innerIso G_K g) h) hE σ
        (D.apartmentTransportEquiv e (GroupScheme.innerIso G_K g) h x) =
      D.conjugateApartmentIdentification
        (torusIsoGaloisTransport k K σ e) e
        (rationalConjugate k K G σ g) g
        (conjugateTorusSquare_galois k K i j σ e g h) h
        (D.apartmentTransportEquiv (torusIsoGaloisTransport k K σ e)
          (GroupScheme.innerIso G_K (rationalConjugate k K G σ g))
          (conjugateTorusSquare_galois k K i j σ e g h)
          (galoisAction k K i D hD σ x)) := by
  apply Apartment.ext
  exact RootFunctionFamily.galoisAction_transport_inner k K σ e g x.val

/-- The realization of the conjugate apartment intertwines both actual
coefficient actions in the same original reduced-building quotient. -/
theorem conjugateApartmentMap_galois (σ : K ≃ₐ[k] K)
    (x : (D.transport e (GroupScheme.innerIso G_K g) h).Apartment) :
    galoisQuotientAction k K i D hD σ (D.conjugateApartmentMap e g h x) =
      D.conjugateApartmentMap e g h
        (galoisAction k K j (D.transport e (GroupScheme.innerIso G_K g) h) hE σ x) := by
  obtain ⟨x, rfl⟩ := (D.apartmentTransportEquiv e (GroupScheme.innerIso G_K g) h).surjective x
  rw [D.conjugateApartmentMap_transport, galoisQuotientAction_smul,
    galoisQuotientAction_apartmentMap,
    galoisAction_apartmentTransport_inner k K i j e g h D hD hE,
    D.conjugateApartmentMap_independent, D.conjugateApartmentMap_transport]

/-- The actual conjugate reduced-building equivalence is equivariant for the
canonical coefficient actions on both quotients. -/
theorem conjugateReducedBuildingEquiv_galois (σ : K ≃ₐ[k] K)
    (q : (D.transport e (GroupScheme.innerIso G_K g) h).ReducedBuilding) :
    galoisQuotientAction k K i D hD σ
        (D.conjugateReducedBuildingEquiv e g h q) =
      D.conjugateReducedBuildingEquiv e g h
        (galoisQuotientAction k K j
          (D.transport e (GroupScheme.innerIso G_K g) h) hE σ q) := by
  obtain ⟨u, x, rfl⟩ := ApartmentQuotient.exists_smul_apartment
    (D.transport e (GroupScheme.innerIso G_K g) h).sharpFixerFamily q
  change galoisQuotientAction k K i D hD σ
      (D.conjugateReducedBuildingEquiv e g h
        (u • (D.transport e (GroupScheme.innerIso G_K g) h).apartmentMap x)) =
    D.conjugateReducedBuildingEquiv e g h
      (galoisQuotientAction k K j
        (D.transport e (GroupScheme.innerIso G_K g) h) hE σ
        (u • (D.transport e (GroupScheme.innerIso G_K g) h).apartmentMap x))
  rw [D.conjugateReducedBuildingEquiv_smul, galoisQuotientAction_smul,
    galoisQuotientAction_smul, D.conjugateReducedBuildingEquiv_smul,
    galoisQuotientAction_apartmentMap]
  change rationalConjugate k K G σ u •
      galoisQuotientAction k K i D hD σ (D.conjugateApartmentMap e g h x) =
    rationalConjugate k K G σ u • D.conjugateApartmentMap e g h
      (galoisAction k K j (D.transport e (GroupScheme.innerIso G_K g) h) hE σ x)
  rw [conjugateApartmentMap_galois k K i j e g h D hD hE]

/-- A coefficient-fixed point of the original quotient has an actual fixed
preimage under the same-action conjugate-building equivalence. -/
theorem exists_galoisFixed_conjugate_preimage (y : D.ReducedBuilding)
    (hy : ∀ σ : K ≃ₐ[k] K, galoisQuotientAction k K i D hD σ y = y) :
    ∃ q : (D.transport e (GroupScheme.innerIso G_K g) h).ReducedBuilding,
      D.conjugateReducedBuildingEquiv e g h q = y ∧
        ∀ σ : K ≃ₐ[k] K, galoisQuotientAction k K j
          (D.transport e (GroupScheme.innerIso G_K g) h) hE σ q = q := by
  refine ⟨(D.conjugateReducedBuildingEquiv e g h).symm y,
    Equiv.apply_symm_apply _ y, ?_⟩
  intro σ
  apply (D.conjugateReducedBuildingEquiv e g h).injective
  rw [← conjugateReducedBuildingEquiv_galois k K i j e g h D hD hE,
    Equiv.apply_symm_apply, hy σ]

end KPApartmentData

/-- Actual conjugate apartments inherit coefficient stability, and the
same-action reduced-building comparison transfers canonical coefficient actions
and every fixed point. -/
def ConjugateApartmentGaloisComparisonStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G)
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map j).hom.hom.left]
    (e : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
      (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T')
    (g : rationalPoints (baseChanged k K G))
    (h : (GroupScheme.baseChange (algebraBaseMap k K)).map i ≫
        (GroupScheme.innerIso (baseChanged k K G) g).hom =
      CommGroupScheme.groupHom e.hom ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    (ω : Kˣ → ℝ)
    (D : KPApartmentData
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)
    (hD : KPApartmentData.GaloisStable k K i D),
    let E := D.transport e (GroupScheme.innerIso (baseChanged k K G) g) h
    ∃ hE : KPApartmentData.GaloisStable k K j E,
      (∀ (σ : K ≃ₐ[k] K) (q : E.ReducedBuilding),
        KPApartmentData.galoisQuotientAction k K i D hD σ
            (D.conjugateReducedBuildingEquiv e g h q) =
          D.conjugateReducedBuildingEquiv e g h
            (KPApartmentData.galoisQuotientAction k K j E hE σ q)) ∧
      ∀ y : D.ReducedBuilding,
        (∀ σ : K ≃ₐ[k] K, KPApartmentData.galoisQuotientAction k K i D hD σ y = y) →
        ∃ q : E.ReducedBuilding, D.conjugateReducedBuildingEquiv e g h q = y ∧
          ∀ σ : K ≃ₐ[k] K, KPApartmentData.galoisQuotientAction k K j E hE σ q = q

/-- Canonical character descent, transporter independence and quotient
semilinearity yield the actual fixed-point comparison. -/
theorem conjugateApartmentGaloisComparison : ConjugateApartmentGaloisComparisonStatement.{u} := by
  intro k K _ _ _ T T' G _ i j _ _ e g h ω D hD
  dsimp only
  let hE := KPApartmentData.galoisStable_transport_inner k K i j e g h D hD
  refine ⟨hE, ?_, ?_⟩
  · exact KPApartmentData.conjugateReducedBuildingEquiv_galois k K i j e g h D hD hE
  · exact KPApartmentData.exists_galoisFixed_conjugate_preimage k K i j e g h D hD hE

end Langlands.Geometry.Building
