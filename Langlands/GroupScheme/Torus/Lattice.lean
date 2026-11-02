import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.MultiplicativeLaurent
import Langlands.GroupScheme.Cartier.Characters
import Langlands.AbelianScheme.RationalBaseChange
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision

/-! # Character and cocharacter lattices of commutative group schemes and split tori -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme

/-! ### Character and cocharacter lattices -/

section Lattices

variable {S : Scheme.{u}}

/-- The character lattice `X^*(T) = Hom(T, 𝔾_m)` of a commutative group scheme, with the
pointwise group law of homomorphisms written additively. -/
abbrev characterLattice (T : CommGroupScheme S) : Type u := T ⟶ Gm S

/-- The cocharacter lattice `X_*(T) = Hom(𝔾_m, T)` of a commutative group scheme, with the
pointwise group law of homomorphisms written additively. -/
abbrev cocharacterLattice (T : CommGroupScheme S) : Type u := Gm S ⟶ T

/-- Evaluation of a homomorphism of commutative group schemes at a point, as an additive map
from homomorphisms to points written additively. -/
abbrev evalPoint {G H : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X) :
    (G ⟶ H) →+ Additive (U ⟶ H.X) :=
  GroupScheme.evalHom G.toGrp H.toGrp U x

theorem evalPoint_apply {G H : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X) (f : G ⟶ H) :
    (evalPoint x f).toMul = x ≫ (CommGroupScheme.groupHom f).hom.hom := rfl

/-- On points, a sum of homomorphisms acts by the product of the values. -/
theorem comp_groupHom_add {G H : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X) (f g : G ⟶ H) :
    x ≫ (CommGroupScheme.groupHom (f + g)).hom.hom =
      (x ≫ (CommGroupScheme.groupHom f).hom.hom) * (x ≫ (CommGroupScheme.groupHom g).hom.hom) :=
  congrArg Additive.toMul ((evalPoint x).map_add f g)

/-- On points, the zero homomorphism is the identity point. -/
@[simp] theorem comp_groupHom_zero {G H : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X) :
    x ≫ (CommGroupScheme.groupHom (0 : G ⟶ H)).hom.hom = 1 :=
  congrArg Additive.toMul ((evalPoint (H := H) x).map_zero)

/-- On points, an integer multiple of a homomorphism acts by the power of the value. -/
theorem comp_groupHom_zsmul {G H : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X) (m : ℤ)
    (f : G ⟶ H) :
    x ≫ (CommGroupScheme.groupHom (m • f)).hom.hom =
      (x ≫ (CommGroupScheme.groupHom f).hom.hom) ^ m :=
  congrArg Additive.toMul (map_zsmul (evalPoint x) m f)

/-- On points, a finite sum of homomorphisms acts by the product of the values. -/
theorem comp_groupHom_sum {G H : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X) {J : Type*}
    (s : Finset J) (f : J → (G ⟶ H)) :
    x ≫ (CommGroupScheme.groupHom (∑ i ∈ s, f i)).hom.hom =
      ∏ i ∈ s, x ≫ (CommGroupScheme.groupHom (f i)).hom.hom :=
  congrArg Additive.toMul (map_sum (evalPoint x) f s)

/-- On points, composition of homomorphisms of commutative group schemes is composition. -/
@[simp] theorem comp_groupHom_comp {G H K : CommGroupScheme S} {U : Over S} (x : U ⟶ G.X)
    (f : G ⟶ H) (g : H ⟶ K) :
    x ≫ (CommGroupScheme.groupHom (f ≫ g)).hom.hom =
      (x ≫ (CommGroupScheme.groupHom f).hom.hom) ≫ (CommGroupScheme.groupHom g).hom.hom := by
  rw [Category.assoc]
  rfl

/-- Homomorphisms of commutative group schemes agree when they agree on all points. -/
theorem CommGroupScheme.hom_ext_points {G H : CommGroupScheme S} {f g : G ⟶ H}
    (h : ∀ (U : Over S) (x : U ⟶ G.X), x ≫ (CommGroupScheme.groupHom f).hom.hom =
      x ≫ (CommGroupScheme.groupHom g).hom.hom) : f = g :=
  congrArg Additive.ofMul (_root_.Langlands.GroupScheme.hom_ext_points h)

/-- Base change along the identity of the base, as a commutative group scheme. -/
def CommGroupScheme.baseChangeIdIso (T : CommGroupScheme S) :
    (CommGroupScheme.baseChange (𝟙 S)).obj T ≅ T where
  hom := Additive.ofMul
    ((Functor.mapGrpNatIso Over.pullbackId).app T.toGrp ≪≫ Functor.mapGrpIdIso.app T.toGrp).hom
  inv := Additive.ofMul
    ((Functor.mapGrpNatIso Over.pullbackId).app T.toGrp ≪≫ Functor.mapGrpIdIso.app T.toGrp).inv
  hom_inv_id := congrArg Additive.ofMul (Iso.hom_inv_id _)
  inv_hom_id := congrArg Additive.ofMul (Iso.inv_hom_id _)

namespace characterLattice

/-- Characters agree with the published Cartier characters over the identity test scheme:
`Hom(T, 𝔾_m)` and `Hom(T_{S'}, 𝔾_{m,S'})` for `S' = S`, by the canonical identification of the
base change along the identity. -/
def cartierEquiv (T : CommGroupScheme S) :
    characterLattice T ≃+ Cartier.CharacterHom T (Over.mk (𝟙 S)) where
  toFun χ := (CommGroupScheme.baseChangeIdIso T).hom ≫ χ
  invFun ψ := (CommGroupScheme.baseChangeIdIso T).inv ≫ ψ
  left_inv χ := by simp
  right_inv ψ := by simp
  map_add' χ ψ := Preadditive.comp_add _ _ _ _ _ _

/-- Base change of characters along a morphism of base schemes, followed by the canonical
identification of the base change of `𝔾_m`. -/
def baseChange {S' : Scheme.{u}} (b : S' ⟶ S) (T : CommGroupScheme S) :
    characterLattice T →+ characterLattice ((CommGroupScheme.baseChange b).obj T) where
  toFun χ := (CommGroupScheme.baseChange b).map χ ≫ (Gm.commBaseChangeIso b).hom
  map_zero' := by simp
  map_add' χ ψ := by simp [Functor.map_add, Preadditive.add_comp]

theorem baseChange_apply {S' : Scheme.{u}} (b : S' ⟶ S) (T : CommGroupScheme S)
    (χ : characterLattice T) :
    baseChange b T χ = (CommGroupScheme.baseChange b).map χ ≫ (Gm.commBaseChangeIso b).hom :=
  rfl

end characterLattice

end Lattices

/-! ### Units of Laurent polynomials over a domain -/

namespace Gm

/-- Over a domain, every unit of `R[T, T⁻¹]` is a unit constant times a power of `T`. -/
theorem exists_eq_C_mul_T_of_isUnit {R : Type*} [CommRing R] [IsDomain R] {u : R[T;T⁻¹]}
    (hu : IsUnit u) : ∃ (c : Rˣ) (m : ℤ), u = LaurentPolynomial.C (c : R) * LaurentPolynomial.T m := by
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  obtain ⟨a, p, hp⟩ := LaurentPolynomial.exists_T_pow u
  obtain ⟨b, q, hq⟩ := LaurentPolynomial.exists_T_pow v
  have hpq : p * q = Polynomial.X ^ (a + b) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow]
    calc u * LaurentPolynomial.T a * (v * LaurentPolynomial.T b)
        = (u * v) * (LaurentPolynomial.T a * LaurentPolynomial.T b) := by ring
      _ = LaurentPolynomial.T ((a + b : ℕ) : ℤ) := by
        rw [huv, one_mul, ← LaurentPolynomial.T_add]
        push_cast
        rfl
  obtain ⟨j, -, w, hw⟩ := (dvd_prime_pow Polynomial.prime_X (a + b)).1 ⟨q, hpq.symm⟩
  obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.1 (w⁻¹).isUnit
  have hp' : p = Polynomial.X ^ j * Polynomial.C (c : R) := by
    rw [hc.2]
    exact (Units.eq_mul_inv_iff_mul_eq w).2 hw
  refine ⟨hc.1.unit, (j : ℤ) - a, ?_⟩
  have hu' : u = Polynomial.toLaurent p * LaurentPolynomial.T (-(a : ℤ)) := by
    rw [hp, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one]
  rw [hu', hp', map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, IsUnit.unit_spec,
    mul_comm (LaurentPolynomial.T (j : ℤ)), mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg]

/-! ### The universal unit point -/

variable (k : Type u) [CommRing k]

/-- The structure map `k → k[T, T⁻¹]` as a morphism of commutative rings. -/
abbrev laurentC : CommRingCat.of k ⟶ CommRingCat.of k[T;T⁻¹] :=
  CommRingCat.ofHom LaurentPolynomial.C

/-- The universal point of `𝔾_m` over `Spec k`: the coordinate unit `T` on `Spec k[T, T⁻¹]`,
given by the published comparison of `𝔾_m` with the relative Laurent spectrum. -/
def laurentPoint : Over.mk (Spec.map (laurentC k)) ⟶ (Gm (Spec (CommRingCat.of k))).X :=
  (relativeLaurentIso (CommRingCat.of k)).inv

/-- The map to `Spec k[T, T⁻¹]` classifying a point of `𝔾_m`. -/
def laurentLift {U : Over (Spec (CommRingCat.of k))} (x : U ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    U ⟶ Over.mk (Spec.map (laurentC k)) :=
  x ≫ (relativeLaurentIso (CommRingCat.of k)).hom

/-- Every point of `𝔾_m` over a scheme over `Spec k` is a restriction of the universal point. -/
theorem comp_laurentPoint {U : Over (Spec (CommRingCat.of k))}
    (x : U ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    laurentLift k x ≫ laurentPoint k = x := by
  rw [laurentLift, laurentPoint, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The unit of `k[T, T⁻¹]` attached to the universal point is `T`. -/
theorem affinePointsEquiv_laurentPoint :
    affinePointsEquiv _ (laurentPoint k) = relativeCoordUnit k := by
  apply Units.ext
  rw [← relativeLaurentIso_affinePointsEquiv_val]
  change (Scheme.ΓSpecIso _).hom (specHomEquiv _ _
    ((relativeLaurentIso (CommRingCat.of k)).inv ≫ (relativeLaurentIso _).hom).left
      (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
  rw [Iso.inv_hom_id]
  exact (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv_hom_id_apply (LaurentPolynomial.T 1)

/-- The unit of `k[T, T⁻¹]` attached to a power of the universal point is a power of `T`. -/
theorem affinePointsEquiv_laurentPoint_zpow (m : ℤ) :
    ((affinePointsEquiv _ (laurentPoint k ^ m) : (k[T;T⁻¹])ˣ) : k[T;T⁻¹]) =
      LaurentPolynomial.T m := by
  rw [map_zpow, affinePointsEquiv_laurentPoint, relativeCoordUnit_zpow_val]

end Gm

/-! ### Endomorphisms of `𝔾_m` -/

section Endomorphisms

variable {S : Scheme.{u}}

/-- On points, the `m`-th multiple of the identity of `𝔾_m` is the `m`-th power map. -/
theorem Gm.comp_zsmul_id {U : Over S} (x : U ⟶ (Gm S).X) (m : ℤ) :
    x ≫ (CommGroupScheme.groupHom (m • 𝟙 (Gm S))).hom.hom = x ^ m := by
  rw [comp_groupHom_zsmul]
  rfl

/-- The power maps `m ↦ (x ↦ x ^ m)` as an additive map to endomorphisms of `𝔾_m`. -/
def Gm.powerHom (S : Scheme.{u}) : ℤ →+ (Gm S ⟶ Gm S) := zmultiplesHom _ (𝟙 (Gm S))

@[simp] theorem Gm.powerHom_apply (m : ℤ) : Gm.powerHom S m = m • 𝟙 (Gm S) := rfl

variable (k : Type u) [CommRing k] [IsDomain k]

theorem Gm.powerHom_injective :
    Function.Injective (Gm.powerHom (Spec (CommRingCat.of k))) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have h := Gm.comp_zsmul_id (Gm.laurentPoint k) m
  rw [← Gm.powerHom_apply, hm, comp_groupHom_zero] at h
  have h' := congrArg (fun x => ((Gm.affinePointsEquiv _ x : (k[T;T⁻¹])ˣ) : k[T;T⁻¹])) h
  change ((Gm.affinePointsEquiv (Spec.map (Gm.laurentC k)) 1 : (k[T;T⁻¹])ˣ) : k[T;T⁻¹]) =
    ((Gm.affinePointsEquiv (Spec.map (Gm.laurentC k)) (Gm.laurentPoint k ^ m) :
      (k[T;T⁻¹])ˣ) : k[T;T⁻¹]) at h'
  rw [map_one, Units.val_one, Gm.affinePointsEquiv_laurentPoint_zpow,
    ← LaurentPolynomial.T_zero] at h'
  exact (AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0) h').symm

theorem Gm.powerHom_surjective :
    Function.Surjective (Gm.powerHom (Spec (CommRingCat.of k))) := by
  intro f
  set u := Gm.affinePointsEquiv _ (Gm.laurentPoint k ≫ (CommGroupScheme.groupHom f).hom.hom)
  obtain ⟨c, m, hcm⟩ := Gm.exists_eq_C_mul_T_of_isUnit u.isUnit
  -- Evaluation at `1` shows that the constant is `1`.
  let ev : CommRingCat.of k[T;T⁻¹] ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) 1)
  have hev : Gm.affineMap ev _ ≫ Gm.laurentPoint k = 1 := by
    apply (Gm.affinePointsEquiv _).injective
    rw [Gm.affinePointsEquiv_naturality, Gm.affinePointsEquiv_laurentPoint, map_one]
    apply Units.ext
    change LaurentPolynomial.eval₂ (RingHom.id k) 1 (LaurentPolynomial.T 1) = 1
    rw [LaurentPolynomial.eval₂_T]
    simp
  have hc : c = 1 := by
    have h := Gm.affinePointsEquiv_naturality ev _
      (Gm.laurentPoint k ≫ (CommGroupScheme.groupHom f).hom.hom)
    rw [← Category.assoc, hev, MonObj.one_comp, map_one] at h
    have h' := congrArg Units.val h
    change (1 : k) = LaurentPolynomial.eval₂ (RingHom.id k) 1 (u : k[T;T⁻¹]) at h'
    rw [hcm, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T] at h'
    apply Units.ext
    simpa using h'.symm
  subst hc
  have hτ : Gm.laurentPoint k ≫ (CommGroupScheme.groupHom f).hom.hom = Gm.laurentPoint k ^ m := by
    apply (Gm.affinePointsEquiv _).injective
    apply Units.ext
    change (u : k[T;T⁻¹]) = _
    rw [hcm, Gm.affinePointsEquiv_laurentPoint_zpow]
    simp
  refine ⟨m, ?_⟩
  apply CommGroupScheme.hom_ext_points
  intro U x
  rw [Gm.powerHom_apply, Gm.comp_zsmul_id]
  conv_rhs => rw [← Gm.comp_laurentPoint k x]
  rw [Category.assoc, hτ, GrpObj.comp_zpow, Gm.comp_laurentPoint]

/-- `End(𝔾_m) ≅ ℤ` over a domain (Milne 12.9): every endomorphism of `𝔾_m` is a power map,
and the power `m` is determined by the endomorphism. The inverse sends `m` to the `m`-th power
map `m • 𝟙`. -/
def gmEndEquiv : (Gm (Spec (CommRingCat.of k)) ⟶ Gm (Spec (CommRingCat.of k))) ≃+ ℤ :=
  (AddEquiv.ofBijective (Gm.powerHom _) ⟨Gm.powerHom_injective k, Gm.powerHom_surjective k⟩).symm

@[simp] theorem gmEndEquiv_symm_apply (m : ℤ) :
    (gmEndEquiv k).symm m = m • 𝟙 (Gm (Spec (CommRingCat.of k))) := rfl

/-- On points, `(gmEndEquiv k).symm m` is the `m`-th power map. -/
theorem gmEndEquiv_symm_comp {U : Over (Spec (CommRingCat.of k))}
    (x : U ⟶ (Gm (Spec (CommRingCat.of k))).X) (m : ℤ) :
    x ≫ (CommGroupScheme.groupHom ((gmEndEquiv k).symm m)).hom.hom = x ^ m :=
  Gm.comp_zsmul_id x m

theorem gmEndEquiv_zsmul_id (m : ℤ) :
    gmEndEquiv k (m • 𝟙 (Gm (Spec (CommRingCat.of k)))) = m := by
  rw [← gmEndEquiv_symm_apply, AddEquiv.apply_symm_apply]

@[simp] theorem gmEndEquiv_id : gmEndEquiv k (𝟙 (Gm (Spec (CommRingCat.of k)))) = 1 := by
  simpa using gmEndEquiv_zsmul_id k 1

theorem eq_gmEndEquiv_zsmul (f : Gm (Spec (CommRingCat.of k)) ⟶ Gm (Spec (CommRingCat.of k))) :
    f = gmEndEquiv k f • 𝟙 (Gm (Spec (CommRingCat.of k))) := by
  rw [← gmEndEquiv_symm_apply, AddEquiv.symm_apply_apply]

/-- `gmEndEquiv` turns composition into multiplication. -/
theorem gmEndEquiv_comp (f g : Gm (Spec (CommRingCat.of k)) ⟶ Gm (Spec (CommRingCat.of k))) :
    gmEndEquiv k (f ≫ g) = gmEndEquiv k f * gmEndEquiv k g := by
  conv_lhs => rw [eq_gmEndEquiv_zsmul k f, eq_gmEndEquiv_zsmul k g]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, smul_smul,
    gmEndEquiv_zsmul_id, mul_comm]

end Endomorphisms

/-! ### The character pairing -/

section Pairing

variable {k : Type u} [CommRing k] [IsDomain k]

/-- The pairing `⟨χ, λ⟩ = gmEndEquiv k (λ ≫ χ)` between characters and cocharacters of a
commutative group scheme over a domain. -/
def latticePairing (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    characterLattice T →ₗ[ℤ] cocharacterLattice T →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun χ ν => gmEndEquiv k (ν ≫ χ))
    (fun χ ψ ν => by rw [Preadditive.comp_add, map_add])
    (fun c χ ν => by rw [Preadditive.comp_zsmul, map_zsmul, smul_eq_mul])
    (fun χ ν ν' => by rw [Preadditive.add_comp, map_add])
    (fun c χ ν => by rw [Preadditive.zsmul_comp, map_zsmul, smul_eq_mul])

theorem latticePairing_apply (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (χ : characterLattice T) (ν : cocharacterLattice T) :
    latticePairing T χ ν = gmEndEquiv k (ν ≫ χ) := rfl

end Pairing

/-! ### Split tori -/

namespace splitTorus

variable (S : Scheme.{u}) (I : Type u) [Finite I]

/-- The split torus is commutative: its group of points over every test scheme is a product
of unit groups. -/
instance isCommMonObj : IsCommMonObj (splitTorus S I).X :=
  (isCommMonObj_iff_isMulCommutative _).2 fun T =>
    { is_comm := ⟨fun x y => (pointsEquiv I T).injective (by rw [map_mul, map_mul, mul_comm])⟩ }

/-- The split torus `𝔾_m^I` as a commutative group scheme. -/
abbrev commGroupScheme : CommGroupScheme S where
  toGrp := splitTorus S I

/-- The `i`-th coordinate character `t ↦ tᵢ`. -/
def proj (i : I) : commGroupScheme S I ⟶ Gm S :=
  Additive.ofMul (Pi.π (fun _ : I => (Gm S).toGrp) i)

theorem comp_proj {T : Over S} (x : T ⟶ (splitTorus S I).X) (i : I) :
    Gm.pointsEquiv S T (x ≫ (CommGroupScheme.groupHom (proj S I i)).hom.hom) =
      pointsEquiv I T x i := rfl

open Classical in
/-- The points of the `i`-th coordinate cocharacter `s ↦ (1, …, s, …, 1)`. -/
def singlePoints (i : I) (T : Over S) : (T ⟶ (Gm S).X) →* (T ⟶ (splitTorus S I).X) :=
  (pointsEquiv I T).symm.toMonoidHom.comp
    ((MonoidHom.mulSingle (fun _ : I => (Γ(T.left, ⊤))ˣ) i).comp
      (Gm.pointsEquiv S T).toMonoidHom)

open Classical in
theorem pointsEquiv_singlePoints (i : I) {T : Over S} (x : T ⟶ (Gm S).X) :
    pointsEquiv I T (singlePoints S I i T x) = Pi.mulSingle i (Gm.pointsEquiv S T x) :=
  MulEquiv.apply_symm_apply _ _

theorem singlePoints_naturality (i : I) {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (Gm S).X) :
    singlePoints S I i T' (a ≫ x) = a ≫ singlePoints S I i T x := by
  classical
  apply (pointsEquiv I T').injective
  rw [pointsEquiv_naturality, pointsEquiv_singlePoints, pointsEquiv_singlePoints,
    Gm.pointsEquiv_naturality]
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.mulSingle_eq_of_ne h]

/-- The `i`-th coordinate cocharacter `s ↦ (1, …, s, …, 1)`. -/
def single (i : I) : Gm S ⟶ commGroupScheme S I :=
  Additive.ofMul (homOfPoints (singlePoints S I i)
    (fun {_ _} a x => singlePoints_naturality S I i a x))

theorem comp_single (i : I) {T : Over S} (x : T ⟶ (Gm S).X) :
    x ≫ (CommGroupScheme.groupHom (single S I i)).hom.hom = singlePoints S I i T x :=
  comp_homOfPoints _ (fun {_ _} a x => singlePoints_naturality S I i a x) T x

open Classical in
theorem pointsEquiv_comp_single (i : I) {T : Over S} (x : T ⟶ (Gm S).X) :
    pointsEquiv I T (x ≫ (CommGroupScheme.groupHom (single S I i)).hom.hom) =
      Pi.mulSingle i (Gm.pointsEquiv S T x) := by
  rw [comp_single, pointsEquiv_singlePoints]

open Classical in
/-- The coordinate cocharacters and characters are dual. -/
theorem single_comp_proj (i j : I) :
    single S I i ≫ proj S I j = if i = j then 𝟙 (Gm S) else 0 := by
  apply CommGroupScheme.hom_ext_points
  intro T x
  apply (Gm.pointsEquiv S T).injective
  rw [comp_groupHom_comp, comp_proj, pointsEquiv_comp_single]
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
    rfl
  · rw [comp_groupHom_zero, Pi.mulSingle_eq_of_ne (Ne.symm h), map_one]

/-- The coordinate decomposition of the identity of the split torus. -/
theorem sum_proj_comp_single [Fintype I] :
    ∑ i, proj S I i ≫ single S I i = 𝟙 (commGroupScheme S I) := by
  classical
  apply CommGroupScheme.hom_ext_points
  intro T x
  apply (pointsEquiv I T).injective
  rw [comp_groupHom_sum, map_prod]
  change _ = pointsEquiv I T x
  conv_rhs => rw [← Finset.univ_prod_mulSingle (pointsEquiv I T x)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [comp_groupHom_comp, pointsEquiv_comp_single, comp_proj]

end splitTorus

/-! ### Lattices of split tori over a domain -/

namespace splitTorus

variable (k : Type u) [CommRing k] [IsDomain k] (I : Type u) [Finite I]

local notation "𝕋" => commGroupScheme (Spec (CommRingCat.of k)) I

/-- `X^*(𝔾_m^I) ≃ ℤ^I`. The inverse sends `m` to the character `t ↦ ∏ tᵢ ^ mᵢ`. -/
def characterLatticeEquiv : characterLattice 𝕋 ≃+ (I → ℤ) where
  toFun χ i := gmEndEquiv k (single _ I i ≫ χ)
  invFun m := ∑ᶠ i, m i • proj _ I i
  left_inv χ := by
    let _ : Fintype I := Fintype.ofFinite I
    change ∑ᶠ i, gmEndEquiv k (single _ I i ≫ χ) • proj _ I i = χ
    rw [finsum_eq_sum_of_fintype]
    conv_rhs => rw [← Category.id_comp χ, ← sum_proj_comp_single]
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.assoc, eq_gmEndEquiv_zsmul k (single _ I i ≫ χ), Preadditive.comp_zsmul,
      Category.comp_id, gmEndEquiv_zsmul_id]
  right_inv m := by
    classical
    let _ : Fintype I := Fintype.ofFinite I
    funext j
    change gmEndEquiv k (single _ I j ≫ ∑ᶠ i, m i • proj _ I i) = m j
    rw [finsum_eq_sum_of_fintype]
    rw [Preadditive.comp_sum]
    simp_rw [Preadditive.comp_zsmul, single_comp_proj]
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [ite_eq_right (Ne.symm hij), smul_zero])
      (by simp), ite_eq_left rfl, gmEndEquiv_zsmul_id]
  map_add' χ ψ := by
    funext i
    simp [Preadditive.comp_add]

/-- `X_*(𝔾_m^I) ≃ ℤ^I`. The inverse sends `m` to the cocharacter `s ↦ (s ^ mᵢ)ᵢ`. -/
def cocharacterLatticeEquiv : cocharacterLattice 𝕋 ≃+ (I → ℤ) where
  toFun ν i := gmEndEquiv k (ν ≫ proj _ I i)
  invFun m := ∑ᶠ i, m i • single _ I i
  left_inv ν := by
    let _ : Fintype I := Fintype.ofFinite I
    change ∑ᶠ i, gmEndEquiv k (ν ≫ proj _ I i) • single _ I i = ν
    rw [finsum_eq_sum_of_fintype]
    conv_rhs => rw [← Category.comp_id ν, ← sum_proj_comp_single]
    rw [Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Category.assoc, eq_gmEndEquiv_zsmul k (ν ≫ proj _ I i), Preadditive.zsmul_comp,
      Category.id_comp, gmEndEquiv_zsmul_id]
  right_inv m := by
    classical
    let _ : Fintype I := Fintype.ofFinite I
    funext j
    change gmEndEquiv k ((∑ᶠ i, m i • single _ I i) ≫ proj _ I j) = m j
    rw [finsum_eq_sum_of_fintype]
    rw [Preadditive.sum_comp]
    simp_rw [Preadditive.zsmul_comp, single_comp_proj]
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [ite_eq_right hij, smul_zero])
      (by simp), ite_eq_left rfl, gmEndEquiv_zsmul_id]
  map_add' ν ν' := by
    funext i
    simp [Preadditive.add_comp]

theorem characterLatticeEquiv_symm_eq [Fintype I] (m : I → ℤ) :
    (characterLatticeEquiv k I).symm m = ∑ i, m i • proj _ I i := by
  exact finsum_eq_sum_of_fintype _

theorem cocharacterLatticeEquiv_symm_eq [Fintype I] (m : I → ℤ) :
    (cocharacterLatticeEquiv k I).symm m = ∑ i, m i • single _ I i := by
  exact finsum_eq_sum_of_fintype _

/-- On points, the character attached to `m` is `t ↦ ∏ tᵢ ^ mᵢ`. -/
theorem pointsEquiv_characterLatticeEquiv_symm [Fintype I] (m : I → ℤ)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :
    Gm.pointsEquiv _ T (x ≫ (CommGroupScheme.groupHom ((characterLatticeEquiv k I).symm m)).hom.hom) =
      ∏ i, pointsEquiv I T x i ^ m i := by
  rw [characterLatticeEquiv_symm_eq]
  refine (congrArg (Gm.pointsEquiv _ T)
    (comp_groupHom_sum (G := 𝕋) x Finset.univ fun i => m i • proj _ I i)).trans ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine (congrArg (Gm.pointsEquiv _ T)
    (comp_groupHom_zsmul (G := 𝕋) x (m i) (proj _ I i))).trans ?_
  rw [map_zpow, comp_proj]

/-- On points, the cocharacter attached to `m` is `s ↦ (s ^ mᵢ)ᵢ`. -/
theorem pointsEquiv_cocharacterLatticeEquiv_symm (m : I → ℤ)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    pointsEquiv I T (x ≫ (CommGroupScheme.groupHom ((cocharacterLatticeEquiv k I).symm m)).hom.hom) =
      fun i => Gm.pointsEquiv _ T x ^ m i := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  rw [cocharacterLatticeEquiv_symm_eq, comp_groupHom_sum, map_prod]
  funext j
  rw [Finset.prod_apply, Finset.prod_eq_single j]
  · rw [comp_groupHom_zsmul, map_zpow, pointsEquiv_comp_single, Pi.pow_apply,
      Pi.mulSingle_eq_same]
  · intro i _ hij
    rw [comp_groupHom_zsmul, map_zpow, pointsEquiv_comp_single, Pi.pow_apply,
      Pi.mulSingle_eq_of_ne (Ne.symm hij), one_zpow]
  · simp

/-- Under the lattice equivalences the pairing is the dot product. -/
theorem latticePairing_eq_sum [Fintype I] (χ : characterLattice 𝕋) (ν : cocharacterLattice 𝕋) :
    latticePairing 𝕋 χ ν =
      ∑ i, characterLatticeEquiv k I χ i * cocharacterLatticeEquiv k I ν i := by
  conv_lhs => rw [← (characterLatticeEquiv k I).symm_apply_apply χ, characterLatticeEquiv_symm_eq]
  rw [latticePairing_apply, Preadditive.comp_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, map_zsmul, smul_eq_mul]
  rfl

theorem latticePairing_symm_symm [Fintype I] (m n : I → ℤ) :
    latticePairing 𝕋 ((characterLatticeEquiv k I).symm m)
      ((cocharacterLatticeEquiv k I).symm n) = ∑ i, m i * n i := by
  rw [latticePairing_eq_sum, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The pairing between the character and cocharacter lattices of a split torus is perfect. -/
instance isPerfPair_latticePairing : (latticePairing 𝕋).IsPerfPair := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have : (dotProductEquiv ℤ I : (I → ℤ) →ₗ[ℤ] Module.Dual ℤ (I → ℤ)).IsPerfPair :=
    LinearMap.IsPerfPair.of_bijective _ (dotProductEquiv ℤ I).bijective
  refine LinearMap.IsPerfPair.congr (characterLatticeEquiv k I).toIntLinearEquiv
    (cocharacterLatticeEquiv k I).toIntLinearEquiv (latticePairing 𝕋)
    (p := (dotProductEquiv ℤ I : (I → ℤ) →ₗ[ℤ] Module.Dual ℤ (I → ℤ))) ?_
  refine LinearMap.ext fun m => LinearMap.ext fun n => ?_
  change latticePairing 𝕋 ((characterLatticeEquiv k I).symm m)
    ((cocharacterLatticeEquiv k I).symm n) = dotProduct m n
  rw [latticePairing_symm_symm]
  rfl

end splitTorus

/-! ### Tori over a field -/

section Tori

variable {k : Type u} [Field k]

/-- A group scheme over a field `k` is a torus if it becomes a split torus after base change to
some field extension of `k` (Milne 12.14). -/
def IsTorus (T : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
    IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)

/-- A split torus is a torus. -/
theorem IsSplitTorus.isTorus {T : GroupScheme (Spec (CommRingCat.of k))} (h : IsSplitTorus T) :
    IsTorus T :=
  ⟨k, inferInstance, inferInstance, h.baseChange _⟩

end Tori

end Langlands.GroupScheme
