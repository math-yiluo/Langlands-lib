import Langlands.GroupScheme.Rational.OrthogonalOrbitSpecialLinear
import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.Geometry.Building.RootBuildingGaloisFieldExtension

/-! # Field coordinates on a relative root group from an orthogonal orbit of simple roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Algebra

namespace Langlands.GroupScheme

namespace LinkedRootParametrization

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {α : characterLattice T} {ν : cocharacterLattice T}
  (X : LinkedRootParametrization i α ν)

/-- On the base point, the global value of a character is its rational value. -/
theorem charValue_base (χ : characterLattice T) (z : rationalPoints T.toGrp) :
    VectorGroup.charValue χ (Over.mk (𝟙 (Spec (CommRingCat.of k)))) z =
      secMap k (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ) z :
        k) := by
  rw [rationalCharacterEval_apply, Gm.affinePointsEquiv_val]
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ (Scheme.ΓSpecIso _).inv) _
  rw [Iso.hom_inv_id]
  rfl

/-- Conjugation by a rational torus point scales the positive rational root points by the
rational value of the root. -/
theorem conj_xpPoint (z : rationalPoints T.toGrp) (c : k) :
    rationalPoints.map i z * X.xpPoint c * (rationalPoints.map i z)⁻¹ =
      X.xpPoint
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm α) z : k) *
          c) := by
  have h := X.positive_equivariant (Over.mk (𝟙 (Spec (CommRingCat.of k)))) z (secMap k c)
  rw [charValue_base, ← map_mul] at h
  exact h

/-- Conjugation by a rational torus point scales the negative rational root points by the
rational value of the negative root. -/
theorem conj_xmPoint (z : rationalPoints T.toGrp) (c : k) :
    rationalPoints.map i z * X.xmPoint c * (rationalPoints.map i z)⁻¹ =
      X.xmPoint
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm (-α)) z :
          k) * c) := by
  have h := X.negative_equivariant (Over.mk (𝟙 (Spec (CommRingCat.of k)))) z (secMap k c)
  rw [charValue_base, ← map_mul] at h
  exact h

end LinkedRootParametrization

namespace SplitPinning

open SpecialLinear.BinaryPresentation GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance orthogonalOrbitRootCoordinatesIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (x : p.NormalizedSimpleRootParametrizations)
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (O : Set p.base.support) (hOs : ∀ (σ : K ≃ₐ[k] K) a, a ∈ O ↔ ρ σ a ∈ O)
    (hO : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → p.rootDatum.IsOrthogonal a b)
    [Fintype O]

section Transport

/-- The Galois transport of a family of scalars on the simple roots. -/
def galoisFamily (σ : K ≃ₐ[k] K) (c : p.base.support → K) : p.base.support → K :=
  fun a => σ (c ((ρ σ).symm a))

omit [Fintype O] in
theorem galoisFamily_apply (σ : K ≃ₐ[k] K) (c : p.base.support → K) (a : p.base.support) :
    galoisFamily k K p (ρ := ρ) σ c (ρ σ a) = σ (c a) := by
  simp [galoisFamily]

/-- The positive orbit product only depends on the coordinates on `O`. -/
theorem orbitXp_congr {c c' : p.base.support → K} (h : ∀ a ∈ O, c a = c' a) :
    orbitXp k K p x O hO c = orbitXp k K p x O hO c' := by
  rw [orbitXp, orbitXp]
  congr 1
  funext a
  exact Subtype.ext (by simp only [h a a.2])

/-- The negative orbit product only depends on the coordinates on `O`. -/
theorem orbitXm_congr {c c' : p.base.support → K} (h : ∀ a ∈ O, c a = c' a) :
    orbitXm k K p x O hO c = orbitXm k K p x O hO c' := by
  rw [orbitXm, orbitXm]
  congr 1
  funext a
  exact Subtype.ext (by simp only [h a a.2])

include hx hOs in
/-- Coefficient conjugation of a positive orbit product transports its coordinates. -/
theorem rationalConjugate_orbitXp (σ : K ≃ₐ[k] K) (c : p.base.support → K) :
    rationalConjugate k K G σ (orbitXp k K p x O hO c) =
      orbitXp k K p x O hO (galoisFamily k K p (ρ := ρ) σ c) := by
  apply RankOneRelation.map_prodHom_of_perm _ (rationalConjugate k K G σ).toMonoidHom
    ((ρ σ).subtypePerm (fun a => (hOs σ a).symm))
  intro a
  simp only [MulEquiv.coe_toMonoidHom, rankData_xp, Equiv.Perm.subtypePerm_apply]
  rw [RootMapsGaloisCompatible.rationalPoint k K hx σ a, galoisFamily_apply]

include hT hx hroot hOs in
/-- Coefficient conjugation of a negative orbit product transports its coordinates. -/
theorem rationalConjugate_orbitXm (σ : K ≃ₐ[k] K) (c : p.base.support → K) :
    rationalConjugate k K G σ (orbitXm k K p x O hO c) =
      orbitXm k K p x O hO (galoisFamily k K p (ρ := ρ) σ c) := by
  apply RankOneRelation.map_prodHom_of_perm _ (rationalConjugate k K G σ).toMonoidHom
    ((ρ σ).subtypePerm (fun a => (hOs σ a).symm))
  intro a
  simp only [MulEquiv.coe_toMonoidHom, rankData_xm, Equiv.Perm.subtypePerm_apply]
  have h := RootMapsGaloisCompatible.negPointFamily_rationalConjugate k K i p eT hT hx hroot σ a
    (c a)
  simp only [negPointFamily] at h
  rw [h, galoisFamily_apply]

/-- Rational points of the split torus act on positive orbit products through the values of
the simple roots. -/
theorem conj_orbitXp (w : rationalPoints p.torus.toGrp) (c : p.base.support → K) :
    rationalPoints.map p.inclusion w * orbitXp k K p x O hO c *
        (rationalPoints.map p.inclusion w)⁻¹ =
      orbitXp k K p x O hO (fun a =>
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
          (p.rootDatum.root a)) w : K) * c a) := by
  apply RankOneRelation.map_prodHom_of_perm _
    (MulAut.conj (rationalPoints.map p.inclusion w)).toMonoidHom (Equiv.refl _)
  intro a
  exact (x a).linked.conj_xpPoint w (c a)

/-- Rational points of the split torus act on negative orbit products through the values of
the negatives of the simple roots. -/
theorem conj_orbitXm (w : rationalPoints p.torus.toGrp) (c : p.base.support → K) :
    rationalPoints.map p.inclusion w * orbitXm k K p x O hO c *
        (rationalPoints.map p.inclusion w)⁻¹ =
      orbitXm k K p x O hO (fun a =>
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
          (-p.rootDatum.root a)) w : K) * c a) := by
  apply RankOneRelation.map_prodHom_of_perm _
    (MulAut.conj (rationalPoints.map p.inclusion w)).toMonoidHom (Equiv.refl _)
  intro a
  exact (x a).linked.conj_xmPoint w (c a)

omit [Fintype O] in
include hT in
/-- The scalar extension of `i` is the pinning inclusion after the inverse torus
identification. -/
theorem map_baseChange_map
    (y : rationalPoints ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp) :
    rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map i) y =
      rationalPoints.map p.inclusion (rationalPoints.map (CommGroupScheme.groupHom eT.inv) y) := by
  have hcomp : ∀ {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of K))} (f : H₁ ⟶ H₂)
      (f' : H₂ ⟶ H₃) (y : rationalPoints H₁),
      rationalPoints.map (f ≫ f') y = rationalPoints.map f' (rationalPoints.map f y) := by
    intro H₁ H₂ H₃ f f' y
    rw [rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply,
      Grp.comp_hom_hom, Category.assoc]
  rw [← hcomp, hT, ← Category.assoc]
  have h1 : CommGroupScheme.groupHom eT.inv ≫ CommGroupScheme.groupHom eT.hom = 𝟙 _ :=
    congrArg CommGroupScheme.groupHom eT.inv_hom_id
  rw [h1, Category.id_comp]
  rfl

end Transport

section Coordinates

variable [FiniteDimensional k K] [IsGalois k K]
    {E : Type u} [Field E] [Algebra k E] (τ : p.base.support → (E →ₐ[k] K))
    (hτ : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → τ (ρ σ a) = σ.toAlgHom.comp (τ a))

/-- Every family of scalars on `O` that is Galois equivariant comes from a unique element of
`E` through the embeddings `τ`. -/
def FamiliesFromField : Prop :=
  ∀ c : p.base.support → K,
    (∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → c (ρ σ a) = σ (c a)) →
      ∃ t : E, ∀ a ∈ O, c a = τ a t

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (iS : S.toGrp ⟶ G)
    (g : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S ⟶ p.torus)
    (hg : CommGroupScheme.groupHom g ≫ p.inclusion =
      (GroupScheme.baseChange (algebraBaseMap k K)).map iS)
    (bS : characterLattice S)
    (hres : ∀ b ∈ O, g ≫ p.rootDatum.root b =
      characterLattice.baseChange (algebraBaseMap k K) S bS)
    (hS : IsSplitTorus S.toGrp) (hb0 : bS ≠ 0) [Smooth G.X.hom]

include hT hx hroot hOs hτ hg hres hS hb0 in
/-- The upper unipotents go into the relative root group of `bS`. -/
theorem fieldSL2_upper_mem (t : E) :
    fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper t) ∈
      Langlands.Geometry.Building.rootGroupPoints iS bS := by
  rw [← Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS bS hb0,
    rationalExtend_fieldSL2_upper]
  exact orbitXp_mem_rootGroupPoints k K iS p x O hO g hg bS hres _

include hT hx hroot hOs hτ hg hres hS hb0 in
/-- The lower unipotents go into the relative root group of `-bS`. -/
theorem fieldSL2_lower_mem (t : E) :
    fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower t) ∈
      Langlands.Geometry.Building.rootGroupPoints iS (-bS) := by
  rw [← Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS (-bS)
    (neg_ne_zero.mpr hb0), rationalExtend_fieldSL2_lower]
  exact orbitXm_mem_rootGroupPoints k K iS p x O hO g hg bS hres _

omit [Smooth G.X.hom] in
include hT hx hroot hOs hτ in
/-- Injectivity of the upper parametrization, given uniqueness of orbit coordinates on `O`. -/
theorem fieldSL2_upper_injective
    (huniq : ∀ c c' : p.base.support → K,
      orbitXp k K p x O hO c = orbitXp k K p x O hO c' → ∀ a ∈ O, c a = c' a)
    {a₀ : p.base.support} (ha₀ : a₀ ∈ O) :
    Function.Injective fun t : E => fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper t) := by
  intro s t h
  have h1 := congrArg (rationalExtend k K G) h
  simp only [rationalExtend_fieldSL2_upper] at h1
  exact (τ a₀).toRingHom.injective (huniq _ _ h1 a₀ ha₀)

omit [Smooth G.X.hom] in
include hT hx hroot hOs hτ in
/-- Injectivity of the lower parametrization, given uniqueness of orbit coordinates on `O`. -/
theorem fieldSL2_lower_injective
    (huniq : ∀ c c' : p.base.support → K,
      orbitXm k K p x O hO c = orbitXm k K p x O hO c' → ∀ a ∈ O, c a = c' a)
    {a₀ : p.base.support} (ha₀ : a₀ ∈ O) :
    Function.Injective fun t : E => fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower t) := by
  intro s t h
  have h1 := congrArg (rationalExtend k K G) h
  simp only [rationalExtend_fieldSL2_lower] at h1
  exact (τ a₀).toRingHom.injective (huniq _ _ h1 a₀ ha₀)

include hT hx hroot hOs hτ hS hb0 in
/-- Every rational point of the relative root group of `bS` is an upper unipotent image,
given that every point of its scalar extension is a positive orbit product, with unique
coordinates on `O`, and that Galois equivariant families come from `E`. -/
theorem exists_fieldSL2_upper_eq
    (hprod : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
      (characterLattice.baseChange (algebraBaseMap k K) S bS) →
        ∃ c : p.base.support → K, g = orbitXp k K p x O hO c)
    (huniq : ∀ c c' : p.base.support → K,
      orbitXp k K p x O hO c = orbitXp k K p x O hO c' → ∀ a ∈ O, c a = c' a)
    (hfam : FamiliesFromField k K p (ρ := ρ) O τ)
    {g : rationalPoints G} (hgb : g ∈ Langlands.Geometry.Building.rootGroupPoints iS bS) :
    ∃ t : E, fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper t) = g := by
  have hgK := (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
    bS hb0 g).2 hgb
  obtain ⟨c, hc⟩ := hprod _ hgK
  have hfix : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → c (ρ σ a) = σ (c a) := by
    intro σ a ha
    have h1 : orbitXp k K p x O hO (galoisFamily k K p (ρ := ρ) σ c) =
        orbitXp k K p x O hO c := by
      rw [← rationalConjugate_orbitXp k K p x hx O hOs hO σ c, ← hc,
        rationalConjugate_rationalExtend]
    have h2 := huniq _ _ h1 (ρ σ a) ((hOs σ a).1 ha)
    rw [galoisFamily_apply] at h2
    exact h2.symm
  obtain ⟨t, ht⟩ := hfam c hfix
  refine ⟨t, rationalExtend_injective_of_isAffineHom k K ?_⟩
  rw [rationalExtend_fieldSL2_upper, hc]
  exact orbitXp_congr k K p x O hO (fun a ha => (ht a ha).symm)

include hT hx hroot hOs hτ hS hb0 in
/-- Every rational point of the relative root group of `-bS` is a lower unipotent image,
under the analogous hypotheses for negative orbit products. -/
theorem exists_fieldSL2_lower_eq
    (hprod : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
      (characterLattice.baseChange (algebraBaseMap k K) S (-bS)) →
        ∃ c : p.base.support → K, g = orbitXm k K p x O hO c)
    (huniq : ∀ c c' : p.base.support → K,
      orbitXm k K p x O hO c = orbitXm k K p x O hO c' → ∀ a ∈ O, c a = c' a)
    (hfam : FamiliesFromField k K p (ρ := ρ) O τ)
    {g : rationalPoints G} (hgb : g ∈ Langlands.Geometry.Building.rootGroupPoints iS (-bS)) :
    ∃ t : E, fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower t) = g := by
  have hgK := (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff (K := K) iS hS
    (-bS) (neg_ne_zero.mpr hb0) g).2 hgb
  obtain ⟨c, hc⟩ := hprod _ hgK
  have hfix : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → c (ρ σ a) = σ (c a) := by
    intro σ a ha
    have h1 : orbitXm k K p x O hO (galoisFamily k K p (ρ := ρ) σ c) =
        orbitXm k K p x O hO c := by
      rw [← rationalConjugate_orbitXm k K i p eT hT x hx hroot O hOs hO σ c, ← hc,
        rationalConjugate_rationalExtend]
    have h2 := huniq _ _ h1 (ρ σ a) ((hOs σ a).1 ha)
    rw [galoisFamily_apply] at h2
    exact h2.symm
  obtain ⟨t, ht⟩ := hfam c hfix
  refine ⟨t, rationalExtend_injective_of_isAffineHom k K ?_⟩
  rw [rationalExtend_fieldSL2_lower, hc]
  exact orbitXm_congr k K p x O hO (fun a ha => (ht a ha).symm)

omit [Smooth G.X.hom] in
include hT hx hroot hOs hτ in
/-- Conjugation by a rational point of `T` multiplies the upper parameter by `χ z`, when the
embeddings of `χ z` are the values of the simple roots of `O` at the scalar extension of `z`. -/
theorem conj_fieldSL2_upper (χ : rationalPoints T.toGrp → E)
    (hχ : ∀ z, ∀ a ∈ O, τ a (χ z) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
        (p.rootDatum.root a))
        (rationalPoints.map (CommGroupScheme.groupHom eT.inv)
          (rationalExtend k K T.toGrp z)) : K))
    (z : rationalPoints T.toGrp) (t : E) :
    rationalPoints.map i z * fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper t) *
        (rationalPoints.map i z)⁻¹ =
      fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper (χ z * t)) := by
  apply rationalExtend_injective_of_isAffineHom k K
  rw [map_mul, map_mul, map_inv, rationalExtend_fieldSL2_upper, rationalExtend_fieldSL2_upper,
    rationalExtend_map, map_baseChange_map k K i p eT hT, conj_orbitXp]
  apply orbitXp_congr
  intro a ha
  rw [map_mul, hχ z a ha]

omit [Smooth G.X.hom] in
include hT hx hroot hOs hτ in
/-- Conjugation by a rational point of `T` multiplies the lower parameter by `χ z`, when the
embeddings of `χ z` are the values of the negatives of the simple roots of `O`. -/
theorem conj_fieldSL2_lower (χ : rationalPoints T.toGrp → E)
    (hχ : ∀ z, ∀ a ∈ O, τ a (χ z) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
        (-p.rootDatum.root a))
        (rationalPoints.map (CommGroupScheme.groupHom eT.inv)
          (rationalExtend k K T.toGrp z)) : K))
    (z : rationalPoints T.toGrp) (t : E) :
    rationalPoints.map i z * fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower t) *
        (rationalPoints.map i z)⁻¹ =
      fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower (χ z * t)) := by
  apply rationalExtend_injective_of_isAffineHom k K
  rw [map_mul, map_mul, map_inv, rationalExtend_fieldSL2_lower, rationalExtend_fieldSL2_lower,
    rationalExtend_map, map_baseChange_map k K i p eT hT, conj_orbitXm]
  apply orbitXm_congr
  intro a ha
  rw [map_mul, hχ z a ha]

include hT hx hroot hOs hτ hg hres hS hb0 in
/-- The upper unipotents as a homomorphism into the relative root group of `bS`. -/
def upperRootHom : Multiplicative E →* Langlands.Geometry.Building.rootGroupPoints iS bS where
  toFun t := ⟨fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper t.toAdd),
    fieldSL2_upper_mem k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0 t.toAdd⟩
  map_one' := Subtype.ext (by
    simp only [toAdd_one, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
    rfl)
  map_mul' s t := Subtype.ext (by
    simp only [toAdd_mul, Matrix.SpecialLinearGroup.transvection_add, map_mul]
    rfl)

include hT hx hroot hOs hτ hg hres hS hb0 in
/-- The lower unipotents as a homomorphism into the relative root group of `-bS`. -/
def lowerRootHom :
    Multiplicative E →* Langlands.Geometry.Building.rootGroupPoints iS (-bS) where
  toFun t := ⟨fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower t.toAdd),
    fieldSL2_lower_mem k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0 t.toAdd⟩
  map_one' := Subtype.ext (by
    simp only [toAdd_one, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
    rfl)
  map_mul' s t := Subtype.ext (by
    simp only [toAdd_mul, Matrix.SpecialLinearGroup.transvection_add, map_mul]
    rfl)

theorem upperRootHom_apply (t : E) :
    (upperRootHom k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0
      (Multiplicative.ofAdd t) : rationalPoints G) =
      fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper t) :=
  rfl

theorem lowerRootHom_apply (t : E) :
    (lowerRootHom k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0
      (Multiplicative.ofAdd t) : rationalPoints G) =
      fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower t) :=
  rfl

variable
    (hprodp : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
      (characterLattice.baseChange (algebraBaseMap k K) S bS) →
        ∃ c : p.base.support → K, g = orbitXp k K p x O hO c)
    (huniqp : ∀ c c' : p.base.support → K,
      orbitXp k K p x O hO c = orbitXp k K p x O hO c' → ∀ a ∈ O, c a = c' a)
    (hprodm : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
      (characterLattice.baseChange (algebraBaseMap k K) S (-bS)) →
        ∃ c : p.base.support → K, g = orbitXm k K p x O hO c)
    (huniqm : ∀ c c' : p.base.support → K,
      orbitXm k K p x O hO c = orbitXm k K p x O hO c' → ∀ a ∈ O, c a = c' a)
    (hfam : FamiliesFromField k K p (ρ := ρ) O τ)
    {a₀ : p.base.support} (ha₀ : a₀ ∈ O)

/-- Field coordinates on the relative root group of `bS`. -/
def upperRootEquiv : Multiplicative E ≃* Langlands.Geometry.Building.rootGroupPoints iS bS :=
  MulEquiv.ofBijective (upperRootHom k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0)
    ⟨fun s t h => by
      exact fieldSL2_upper_injective k K i p eT hT x hx hroot O hOs hO τ hτ huniqp ha₀
        (congrArg Subtype.val h),
     fun y => by
      obtain ⟨t, ht⟩ := exists_fieldSL2_upper_eq k K i p eT hT x hx hroot O hOs hO τ hτ iS bS hS
        hb0 hprodp huniqp hfam y.2
      exact ⟨Multiplicative.ofAdd t, Subtype.ext ht⟩⟩

/-- Field coordinates on the relative root group of `-bS`. -/
def lowerRootEquiv :
    Multiplicative E ≃* Langlands.Geometry.Building.rootGroupPoints iS (-bS) :=
  MulEquiv.ofBijective (lowerRootHom k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0)
    ⟨fun s t h => by
      exact fieldSL2_lower_injective k K i p eT hT x hx hroot O hOs hO τ hτ huniqm ha₀
        (congrArg Subtype.val h),
     fun y => by
      obtain ⟨t, ht⟩ := exists_fieldSL2_lower_eq k K i p eT hT x hx hroot O hOs hO τ hτ iS bS hS
        hb0 hprodm huniqm hfam y.2
      exact ⟨Multiplicative.ofAdd t, Subtype.ext ht⟩⟩

theorem upperRootEquiv_apply (t : E) :
    (upperRootEquiv k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0 hprodp huniqp
      hfam ha₀ (Multiplicative.ofAdd t) : rationalPoints G) =
      fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (upper t) :=
  rfl

theorem lowerRootEquiv_apply (t : E) :
    (lowerRootEquiv k K i p eT hT x hx hroot O hOs hO τ hτ iS g hg bS hres hS hb0 hprodm huniqm
      hfam ha₀ (Multiplicative.ofAdd t) : rationalPoints G) =
      fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ (lower t) :=
  rfl

end Coordinates

end SplitPinning

end Langlands.GroupScheme
