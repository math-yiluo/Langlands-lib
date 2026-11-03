import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.Rational.RootFiniteness

/-! # Uniqueness of the scalar structure of weight vector coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

/-! ### Scaling in vector coordinates -/

section Scaling

variable (e : ∀ T : Over (Spec (CommRingCat.of k)),
  (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))

/-- The point whose coordinates are `c` times those of `v`. -/
def coordinateSmul (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) (v : T ⟶ V.X) :
    T ⟶ V.X :=
  (e T).symm (Multiplicative.ofAdd (c • (e T v).toAdd))

theorem coordinateSmul_coord (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (v : T ⟶ V.X) : (e T (coordinateSmul e T c v)).toAdd = c • (e T v).toAdd := by
  simp [coordinateSmul]

variable {e}

/-- Scaling commutes with restriction along morphisms of test schemes. -/
theorem IsNaturalVectorCoordinates.comp_coordinateSmul (he : IsNaturalVectorCoordinates e)
    {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T) (c : Γ(T.left, ⊤)) (v : T ⟶ V.X) :
    f ≫ coordinateSmul e T c v = coordinateSmul e W (f.left.appTop c) (f ≫ v) := by
  apply (e W).injective
  apply Multiplicative.toAdd.injective
  rw [he T W f, coordinateSmul_coord, coordinateSmul_coord, he T W f]
  funext j
  simp [map_mul]

/-- Restriction along a morphism that is injective on global functions is injective on
points of a scheme with natural vector coordinates. -/
theorem IsNaturalVectorCoordinates.cancel (he : IsNaturalVectorCoordinates e)
    {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T) (hf : Function.Injective f.left.appTop)
    {x y : T ⟶ V.X} (h : f ≫ x = f ≫ y) : x = y := by
  apply (e T).injective
  apply Multiplicative.toAdd.injective
  funext j
  apply hf
  have hj := congrArg (fun z => (e W z).toAdd j) h
  simpa only [he T W f] using hj

/-- Scaling by the value of the weight at a torus point is the torus action. -/
theorem IsWeightVectorCoordinates.coordinateSmul_eq_act {b : AutomorphicAction S.toGrp V}
    {χ : characterLattice S} (he : IsWeightVectorCoordinates b χ e)
    (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ V.X) :
    coordinateSmul e T
      (Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom χ).hom.hom) : Γ(T.left, ⊤)) v =
      b.act s v := by
  apply (e T).injective
  apply Multiplicative.toAdd.injective
  rw [coordinateSmul_coord, he.2]

end Scaling

/-! ### The universal test scheme -/

namespace WeightVectorUniqueness

section Universal

variable (k n)

/-- The coordinate ring `k[y][x₁, …, xₙ]` of the universal test scheme. -/
abbrev UniversalRing : Type u := MvPolynomial (Fin n) k[X]

/-- The universal test scheme `Spec k[y][x₁, …, xₙ]` over `Spec k`. -/
abbrev universalScheme : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (UniversalRing k n))))

/-- The universal coordinate vector `(x₁, …, xₙ)`. -/
def universalCoord : Fin n → Γ((universalScheme k n).left, ⊤) :=
  fun j => (Scheme.ΓSpecIso (CommRingCat.of (UniversalRing k n))).inv (MvPolynomial.X j)

/-- The universal scalar `y`. -/
def universalScalar : Γ((universalScheme k n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (UniversalRing k n))).inv (MvPolynomial.C Polynomial.X)

variable {k n}

/-- The structure ring map `k → Γ(T, ⊤)` of a scheme over `Spec k`. -/
def structureRingHom (T : Over (Spec (CommRingCat.of k))) : k →+* Γ(T.left, ⊤) :=
  (Gm.specHomEquiv T.left (CommRingCat.of k) T.hom).hom

/-- The ring map `y ↦ c`, `xⱼ ↦ zⱼ` from the universal coordinate ring. -/
def classifyingRingHom (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (z : Fin n → Γ(T.left, ⊤)) : UniversalRing k n →+* Γ(T.left, ⊤) :=
  MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom (structureRingHom T) c) z

theorem classifyingRingHom_algebraMap (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (z : Fin n → Γ(T.left, ⊤)) (a : k) :
    classifyingRingHom T c z (algebraMap k (UniversalRing k n) a) = structureRingHom T a := by
  simp [classifyingRingHom, MvPolynomial.algebraMap_apply]

/-- The morphism to the universal test scheme classifying a scalar and a coordinate vector. -/
def classifyingMap (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (z : Fin n → Γ(T.left, ⊤)) : T ⟶ universalScheme k n :=
  Over.homMk ((Gm.specHomEquiv T.left _).symm (CommRingCat.ofHom (classifyingRingHom T c z))) (by
    apply (Gm.specHomEquiv T.left (CommRingCat.of k)).injective
    change (Scheme.ΓSpecIso _).inv ≫ (T.left.toSpecΓ ≫ Spec.map _ ≫ Spec.map _).appTop = _
    rw [← Spec.map_comp]
    change Gm.specHomEquiv T.left _ ((Gm.specHomEquiv T.left _).symm _) = _
    rw [Equiv.apply_symm_apply]
    ext a
    exact classifyingRingHom_algebraMap T c z a)

theorem classifyingMap_appTop (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (z : Fin n → Γ(T.left, ⊤)) (r : UniversalRing k n) :
    (classifyingMap T c z).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (UniversalRing k n))).inv r) =
      classifyingRingHom T c z r := by
  have h := Equiv.apply_symm_apply (Gm.specHomEquiv T.left (CommRingCat.of (UniversalRing k n)))
    (CommRingCat.ofHom (classifyingRingHom T c z))
  exact congrArg (fun ψ => ψ.hom r) h

theorem classifyingMap_universalScalar (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (z : Fin n → Γ(T.left, ⊤)) :
    (classifyingMap T c z).left.appTop (universalScalar k n) = c := by
  rw [universalScalar, classifyingMap_appTop]
  simp [classifyingRingHom]

theorem classifyingMap_universalCoord (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (z : Fin n → Γ(T.left, ⊤)) (j : Fin n) :
    (classifyingMap T c z).left.appTop (universalCoord k n j) = z j := by
  rw [universalCoord, classifyingMap_appTop]
  simp [classifyingRingHom]

variable {e e' : ∀ T : Over (Spec (CommRingCat.of k)),
  (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}

/-- The universal point, with coordinates `(x₁, …, xₙ)` in the coordinates `e`. -/
def universalPoint (e : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))) :
    universalScheme k n ⟶ V.X :=
  (e _).symm (Multiplicative.ofAdd (universalCoord k n))

theorem classifyingMap_universalPoint
    (he : IsNaturalVectorCoordinates e) (T : Over (Spec (CommRingCat.of k)))
    (c : Γ(T.left, ⊤)) (v : T ⟶ V.X) :
    classifyingMap T c (e T v).toAdd ≫ universalPoint e = v := by
  apply (e T).injective
  apply Multiplicative.toAdd.injective
  rw [he _ T]
  funext j
  simp only [universalPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  exact classifyingMap_universalCoord _ _ _ j

end Universal

/-! ### Restriction along `y ↦ t ^ D` -/

section Laurent

variable (k n)

/-- The coordinate ring `k[t, t⁻¹][x₁, …, xₙ]` of the Laurent test scheme. -/
abbrev LaurentRing : Type u := MvPolynomial (Fin n) k[T;T⁻¹]

/-- The Laurent test scheme `Spec k[t, t⁻¹][x₁, …, xₙ]` over `Spec k`. -/
abbrev laurentScheme : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentRing k n))))

variable {k n}

/-- The ring map `y ↦ t ^ D`, `xⱼ ↦ xⱼ`. -/
def powerRingHom (D : ℕ) : UniversalRing k n →+* LaurentRing k n :=
  MvPolynomial.map (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T D))

theorem powerRingHom_injective {D : ℕ} (hD : 0 < D) :
    Function.Injective (powerRingHom (k := k) (n := n) D) := by
  apply MvPolynomial.map_injective
  have h : Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T D) =
      (Polynomial.toLaurent : k[X] →+* k[T;T⁻¹]).comp
        (Polynomial.expand k D : k[X] →ₐ[k] k[X]).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp [Polynomial.toLaurent_X_pow]
  rw [h]
  exact Polynomial.toLaurent_injective.comp (Polynomial.expand_injective hD)

/-- The morphism `Spec k[t, t⁻¹][x] ⟶ Spec k[y][x]` given by `y ↦ t ^ D`. -/
def powerMap (D : ℕ) : laurentScheme k n ⟶ universalScheme k n :=
  Over.homMk (Spec.map (CommRingCat.ofHom (powerRingHom D))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change powerRingHom D (algebraMap k (UniversalRing k n) a) = algebraMap k (LaurentRing k n) a
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, powerRingHom,
      MvPolynomial.map_C]
    congr 1
    simp [LaurentPolynomial.algebraMap_apply])

theorem powerMap_appTop (D : ℕ) (r : UniversalRing k n) :
    (powerMap (k := k) (n := n) D).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (UniversalRing k n))).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentRing k n))).inv (powerRingHom D r) := by
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (powerRingHom (k := k) (n := n) D))
  exact (congrArg (fun φ => φ.hom r) h).symm

theorem powerMap_appTop_injective {D : ℕ} (hD : 0 < D) :
    Function.Injective (powerMap (k := k) (n := n) D).left.appTop := by
  intro a a' h
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of (UniversalRing k n))).inv r = a :=
    ⟨(Scheme.ΓSpecIso _).hom a, by simp⟩
  obtain ⟨r', rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of (UniversalRing k n))).inv r = a' :=
    ⟨(Scheme.ΓSpecIso _).hom a', by simp⟩
  rw [powerMap_appTop, powerMap_appTop] at h
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentRing k n))).hom h
  simp only [Iso.inv_hom_id_apply] at h'
  rw [powerRingHom_injective hD h']

theorem powerMap_universalScalar (D : ℕ) :
    (powerMap (k := k) (n := n) D).left.appTop (universalScalar k n) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentRing k n))).inv
        (MvPolynomial.C (LaurentPolynomial.T D)) := by
  rw [universalScalar, powerMap_appTop]
  simp [powerRingHom]

theorem isUnit_laurentT :
    IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (LaurentRing k n))).inv
      (MvPolynomial.C (LaurentPolynomial.T 1))) :=
  ((LaurentPolynomial.isUnit_T 1).map MvPolynomial.C).map _

/-- The torus point `ζ(t)` of the Laurent test scheme, for a cocharacter `ζ`. -/
def laurentTorusPoint (ζ : cocharacterLattice S) : laurentScheme k n ⟶ S.X :=
  (Gm.pointsEquiv _ (laurentScheme k n)).symm (isUnit_laurentT (k := k) (n := n)).unit ≫
    (CommGroupScheme.groupHom ζ).hom.hom

theorem pointsEquiv_laurentTorusPoint {χ : characterLattice S} {ζ : cocharacterLattice S}
    {D : ℕ} (hD : latticePairing S χ ζ = D) :
    (Gm.pointsEquiv _ (laurentScheme k n)
        (laurentTorusPoint ζ ≫ (CommGroupScheme.groupHom χ).hom.hom) :
          Γ((laurentScheme k n).left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentRing k n))).inv
        (MvPolynomial.C (LaurentPolynomial.T D)) := by
  have hζχ : ζ ≫ χ = (gmEndEquiv k).symm D := by
    rw [← hD, latticePairing_apply, AddEquiv.symm_apply_apply]
  rw [laurentTorusPoint, ← comp_groupHom_comp, hζχ, gmEndEquiv_symm_comp, map_zpow,
    MulEquiv.apply_symm_apply, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
    ← map_pow, ← map_pow, LaurentPolynomial.T_pow, mul_one]

end Laurent

end WeightVectorUniqueness

/-! ### Uniqueness -/

section Uniqueness

open WeightVectorUniqueness

variable {b : AutomorphicAction S.toGrp V} {χ : characterLattice S}

/-- A nonzero character of a split torus pairs positively with some cocharacter. -/
theorem _root_.Langlands.GroupScheme.IsSplitTorus.exists_pairing_eq_pos
    (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ ∃ ζ : cocharacterLattice S, latticePairing S χ ζ = D := by
  have hlin : LinearIndependent ℚ (fun _ : Unit => toRat χ) := by
    rw [linearIndependent_unique_iff]
    intro h
    exact hχ (hS.character_toRat_injective (h.trans (map_zero toRat).symm))
  obtain ⟨d, hd, ζ, hζ⟩ := hS.exists_scaled_pairings (fun _ : Unit => χ) hlin (fun _ => 1)
  lift d to ℕ using hd.le
  exact ⟨d, by exact_mod_cast hd, ζ, by simpa using hζ ()⟩

/-- Positive multiples of a nonzero character of a split torus are nonzero. -/
theorem _root_.Langlands.GroupScheme.IsSplitTorus.nsmul_ne_zero (hS : IsSplitTorus S.toGrp)
    {a : characterLattice S} (ha : a ≠ 0) {r : ℕ} (hr : r ≠ 0) : r • a ≠ 0 := by
  intro h
  apply ha
  apply hS.character_toRat_injective
  have h' : toRat (r • a) = toRat (0 : characterLattice S) := congrArg toRat h
  rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul ℚ, smul_eq_zero] at h'
  rw [map_zero]
  exact h'.resolve_left (by exact_mod_cast hr)

variable {e : ∀ T : Over (Spec (CommRingCat.of k)),
  (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}

/-- On the Laurent test scheme, scaling by `t ^ D` is the action of `ζ(t)`. -/
theorem IsWeightVectorCoordinates.powerMap_coordinateSmul (he : IsWeightVectorCoordinates b χ e)
    {ζ : cocharacterLattice S} {D : ℕ} (hD : latticePairing S χ ζ = D) {N : ℕ}
    (v : universalScheme k N ⟶ V.X) :
    powerMap D ≫ coordinateSmul e _ (universalScalar k N) v =
      b.act (laurentTorusPoint ζ) (powerMap D ≫ v) := by
  rw [he.1.comp_coordinateSmul, powerMap_universalScalar, ← pointsEquiv_laurentTorusPoint hD,
    he.coordinateSmul_eq_act]

/-- Two systems of weight vector coordinates scale universal points in the same way. -/
theorem coordinateSmul_universalScalar_eq (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0)
    {m : ℕ} {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates b χ e) (he' : IsWeightVectorCoordinates b χ e') {N : ℕ}
    (v : universalScheme k N ⟶ V.X) :
    coordinateSmul e _ (universalScalar k N) v = coordinateSmul e' _ (universalScalar k N) v := by
  obtain ⟨D, hD, ζ, hζ⟩ := hS.exists_pairing_eq_pos hχ
  apply he.1.cancel (powerMap D) (powerMap_appTop_injective hD)
  rw [he.powerMap_coordinateSmul hζ, he'.powerMap_coordinateSmul hζ]

/-- Two systems of weight vector coordinates of a nonzero weight of a split torus define
the same scalar multiplication. -/
theorem coordinateSmul_eq_of_isWeightVectorCoordinates (hS : IsSplitTorus S.toGrp)
    (hχ : χ ≠ 0) {m : ℕ} {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates b χ e) (he' : IsWeightVectorCoordinates b χ e')
    (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) (v : T ⟶ V.X) :
    coordinateSmul e T c v = coordinateSmul e' T c v := by
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : T ⟶ universalScheme k n,
      g.left.appTop (universalScalar k n) = c ∧ g ≫ universalPoint e = v :=
    ⟨_, classifyingMap_universalScalar T c _, classifyingMap_universalPoint he.1 T c v⟩
  rw [← hg₁, ← hg₂, ← he.1.comp_coordinateSmul, ← he'.1.comp_coordinateSmul,
    coordinateSmul_universalScalar_eq hS hχ he he']

/-- One system of vector coordinates of a nonzero weight of a split torus gives the unique
weight vector structure of that weight. -/
theorem hasUniqueWeightVectorStructure_of_coordinates (hS : IsSplitTorus S.toGrp)
    (hχ : χ ≠ 0) (he : IsWeightVectorCoordinates b χ e) :
    HasUniqueWeightVectorStructure b χ :=
  ⟨⟨n, e, he⟩, fun _ _ _ _ h₁ h₂ T c v =>
    coordinateSmul_eq_of_isWeightVectorCoordinates hS hχ h₁ h₂ T c v⟩

end Uniqueness

end Langlands.GroupScheme.RelativeRoot
