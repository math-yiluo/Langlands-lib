import Langlands.GroupScheme.Examples.UnitaryAlgebraPresentation
import Langlands.Algebra.CentralSimple.NumberFieldLandherrStatement
import Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormStatement
import Langlands.GroupScheme.Quaternionic.GaloisGramDescent
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction
import Langlands.GroupScheme.GaloisPointTower

/-! # The Hasse kernel for special unitary groups of algebras with involution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.UnitaryAlgebra

open Quaternionic Quaternionic.FirstKindInvolution GaloisPoint Langlands.GaloisAlgebraDescent
  Langlands.CentralSimple Langlands.CentralSimple.UnitaryPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Embedding

variable {F E B : Type u} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B] [FiniteDimensional F B]

local notation "U" => FiniteAlgebraUnits.groupScheme (Module.finBasis F B)
local notation "Rₐ" R => CommAlgCat.of F R
local notation "unitEquiv[" R "]" =>
  FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F B) (Rₐ R)

variable {τ : FirstKindInvolution F B} {G : GroupScheme (Spec (CommRingCat.of F))}
  (p : Presentation E τ G)

/-- The points of `G` as units of the scalar-extended algebra. -/
def toUnits (R : Type u) [CommRing R] [Algebra F R] :
    G.affinePoints (Rₐ R) →* (R ⊗[F] B)ˣ :=
  (specialUnitaryPoints E τ R).subtype.comp (p.pointsEquiv (Rₐ R)).toMonoidHom

omit [FiniteDimensional F B] in
theorem toUnits_mem (R : Type u) [CommRing R] [Algebra F R] (x : G.affinePoints (Rₐ R)) :
    toUnits p R x ∈ specialUnitaryPoints E τ R :=
  (p.pointsEquiv (Rₐ R) x).property

/-- The points of `G` as points of the unit group scheme of `B`. -/
def toAmbient (R : Type u) [CommRing R] [Algebra F R] :
    G.affinePoints (Rₐ R) →* (U).affinePoints (Rₐ R) :=
  (unitEquiv[R]).symm.toMonoidHom.comp (toUnits p R)

@[simp] theorem unitEquiv_toAmbient (R : Type u) [CommRing R] [Algebra F R]
    (x : G.affinePoints (Rₐ R)) :
    (unitEquiv[R]) (toAmbient p R x) = toUnits p R x :=
  MulEquiv.apply_symm_apply _ _

theorem toAmbient_injective (R : Type u) [CommRing R] [Algebra F R] :
    Function.Injective (toAmbient p R) := by
  intro x y h
  apply (p.pointsEquiv (Rₐ R)).injective
  apply Subtype.ext
  have hh := congrArg (fun z => (unitEquiv[R]) z) h
  rw [unitEquiv_toAmbient, unitEquiv_toAmbient] at hh
  exact hh

theorem toAmbient_naturality {R R' : Type u} [CommRing R] [CommRing R'] [Algebra F R]
    [Algebra F R'] (f : R →ₐ[F] R') (x : G.affinePoints (Rₐ R)) :
    toAmbient p R' (G.affinePointMap (CommAlgCat.ofHom f) x) =
      (U).affinePointMap (CommAlgCat.ofHom f) (toAmbient p R x) := by
  apply (unitEquiv[R']).injective
  rw [unitEquiv_toAmbient]
  have h := FiniteAlgebraUnits.affinePointsEquiv_naturality (Module.finBasis F B)
    (CommAlgCat.ofHom f) (toAmbient p R x)
  change (unitEquiv[R']) ((U).affinePointMap (CommAlgCat.ofHom f) (toAmbient p R x)) = _ at h
  rw [h, unitEquiv_toAmbient]
  change ((p.pointsEquiv (Rₐ R') (G.affinePointMap (CommAlgCat.ofHom f) x) :
    (R' ⊗[F] B)ˣ)) = _
  rw [p.naturality]
  rfl

/-- A special unitary unit comes from a point of `G`. -/
theorem exists_toAmbient_eq (R : Type u) [CommRing R] [Algebra F R]
    (w : (U).affinePoints (Rₐ R)) (hw : (unitEquiv[R]) w ∈ specialUnitaryPoints E τ R) :
    ∃ x : G.affinePoints (Rₐ R), toAmbient p R x = w := by
  refine ⟨(p.pointsEquiv (Rₐ R)).symm ⟨_, hw⟩, (unitEquiv[R]).injective ?_⟩
  rw [unitEquiv_toAmbient]
  change (((p.pointsEquiv (Rₐ R)) ((p.pointsEquiv (Rₐ R)).symm ⟨_, hw⟩)) :
    (R ⊗[F] B)ˣ) = _
  rw [MulEquiv.apply_symm_apply]

section Fixed

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [Algebra E B] [IsScalarTower F E B] [FiniteDimensional E B] [Algebra.IsCentral E B]
  [IsSimpleRing B] [FiniteDimensional F B] in
/-- A Galois-fixed unit of `L ⊗[F] B` comes from a unit of `B`. -/
theorem exists_unit_of_fixed (t : (L ⊗[F] B)ˣ)
    (ht : ∀ s : L ≃ₐ[F] L, coefficientConjugate F L B s t = t) :
    ∃ y : Bˣ, (1 : L) ⊗ₜ[F] (y : B) = t := by
  let i : B →ₐ[F] L ⊗[F] B := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (B := B) (algebraMap F L).injective
  have hinv (s : L ≃ₐ[F] L) : coefficientConjugate F L B s ((t⁻¹ : (L ⊗[F] B)ˣ) : L ⊗[F] B) =
      ((t⁻¹ : (L ⊗[F] B)ˣ) : L ⊗[F] B) := by
    have hf : Units.map (coefficientConjugate F L B s).toMonoidHom t = t :=
      Units.ext (ht s)
    change ((Units.map (coefficientConjugate F L B s).toMonoidHom t⁻¹ : (L ⊗[F] B)ˣ) :
      L ⊗[F] B) = _
    rw [_root_.map_inv, hf]
  obtain ⟨y, hy⟩ := (mem_range_includeRight_iff F L B (t : L ⊗[F] B)).mpr ht
  obtain ⟨y', hy'⟩ := (mem_range_includeRight_iff F L B ((t⁻¹ : (L ⊗[F] B)ˣ) : L ⊗[F] B)).mpr hinv
  change i y = t at hy
  change i y' = _ at hy'
  refine ⟨⟨y, y', hi ?_, hi ?_⟩, hy⟩
  · rw [_root_.map_mul, _root_.map_one, hy, hy', Units.mul_inv]
  · rw [_root_.map_mul, _root_.map_one, hy, hy', Units.inv_mul]

omit [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B] [FiniteDimensional E B]
  [Algebra.IsCentral E B] [IsSimpleRing B] [FiniteDimensional F B] in
/-- A Galois-fixed unit of `E ⊗[F] L` comes from a unit of `E`. -/
theorem exists_fieldUnit_of_fixed (t : (E ⊗[F] L)ˣ)
    (ht : ∀ s : L ≃ₐ[F] L,
      Algebra.TensorProduct.map (AlgHom.id F E) s.toAlgHom (t : E ⊗[F] L) = t) :
    ∃ z : Eˣ, (z : E) ⊗ₜ[F] (1 : L) = t := by
  let c := Algebra.TensorProduct.comm F E L
  let t' : (L ⊗[F] E)ˣ := Units.map c.toMonoidHom t
  have ht' (s : L ≃ₐ[F] L) : coefficientConjugate F L E s t' = t' := by
    have hcomm : ∀ x : E ⊗[F] L, coefficientConjugate F L E s (c x) =
        c (Algebra.TensorProduct.map (AlgHom.id F E) s.toAlgHom x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul e l => rfl
      | add x y hx hy => simp only [_root_.map_add, hx, hy]
    change coefficientConjugate F L E s (c t) = c t
    rw [hcomm, ht s]
  obtain ⟨z, hz⟩ := exists_unit_of_fixed (B := E) t' ht'
  refine ⟨z, ?_⟩
  apply c.injective
  change c ((z : E) ⊗ₜ[F] (1 : L)) = c t
  rw [← show ((t' : (L ⊗[F] E)ˣ) : L ⊗[F] E) = c t from rfl, ← hz]
  rfl

end Fixed

section Galois

variable {L : Type u} [Field L] [Algebra F L]

theorem unitEquiv_conjugate (s : L ≃ₐ[F] L) (x : (U).affinePoints (Rₐ L)) :
    (unitEquiv[L]) (conjugate F L U s x) =
      Units.map (coefficientConjugate F L B s).toMonoidHom ((unitEquiv[L]) x) :=
  FiniteAlgebraUnits.affinePointsEquiv_naturality _ (CommAlgCat.ofHom s.toAlgHom) x

omit [Algebra E B] [IsScalarTower F E B] [FiniteDimensional E B] [Algebra.IsCentral E B]
  [IsSimpleRing B] [FiniteDimensional F B] in
private def tensorAut : (L ≃ₐ[F] L) →* RingAut (L ⊗[F] B) where
  toFun s := (Algebra.TensorProduct.congr s (AlgEquiv.refl : B ≃ₐ[F] B)).toRingEquiv
  map_one' := by
    change (Algebra.TensorProduct.congr AlgEquiv.refl AlgEquiv.refl).toRingEquiv = _
    rw [Algebra.TensorProduct.congr_refl]
    rfl
  map_mul' s t := by
    change (Algebra.TensorProduct.congr (t.trans s) (AlgEquiv.refl : B ≃ₐ[F] B)).toRingEquiv = _
    rw [show (AlgEquiv.refl : B ≃ₐ[F] B) = AlgEquiv.refl.trans AlgEquiv.refl from rfl,
      Algebra.TensorProduct.congr_trans]
    rfl

/-- Finite-algebra Hilbert 90 gives a unit primitive of the cocycle in the unit group
of `B`. -/
theorem exists_ambient_coboundary [Infinite F] [FiniteDimensional F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) :
    ∃ b : (U).affinePoints (Rₐ L), ∀ s : L ≃ₐ[F] L,
      toAmbient p L (GaloisCocycle.value ξ s) = b * (conjugate F L U s b)⁻¹ := by
  let c₀ (s : L ≃ₐ[F] L) := toAmbient p L (GaloisCocycle.value ξ s)
  let c (s : L ≃ₐ[F] L) := (unitEquiv[L]) (c₀ s)
  let H : Subgroup (L ≃ₐ[F] L) := ⊤
  have hc₀ (s t : L ≃ₐ[F] L) : c₀ (s * t) = c₀ s * conjugate F L U s (c₀ t) := by
    change toAmbient p L (GaloisCocycle.value ξ (s * t)) = _
    rw [GaloisCocycle.value_mul ξ s t, _root_.map_mul]
    congr 1
    exact toAmbient_naturality p s.toAlgHom (GaloisCocycle.value ξ t)
  have hc₁ : c 1 = 1 := by
    have hval := hc₀ 1 1
    rw [one_mul, conjugate_one] at hval
    have h₁ := mul_left_cancel (hval.symm.trans (mul_one _).symm)
    change (unitEquiv[L]) (c₀ 1) = 1
    rw [h₁, _root_.map_one]
  have hc (s t : L ≃ₐ[F] L) :
      c (s * t) = c s * Units.map (tensorAut (B := B) s).toMonoidHom (c t) := by
    change (unitEquiv[L]) (c₀ (s * t)) = _
    rw [hc₀, _root_.map_mul, unitEquiv_conjugate]
    rfl
  obtain ⟨b, hb⟩ := Langlands.Algebra.exists_unit_coboundary H
    ((tensorAut (B := B)).comp H.subtype) (fun s => coefficientConjugate_smul F L B s.val)
    (fun s => c s.val) hc₁ (fun s t => hc s.val t.val)
  refine ⟨(unitEquiv[L]).symm b, fun s => (unitEquiv[L]).injective ?_⟩
  rw [_root_.map_mul, _root_.map_inv, unitEquiv_conjugate, MulEquiv.apply_symm_apply]
  exact eq_mul_inv_of_mul_eq (hb ⟨s, Subgroup.mem_top s⟩)

variable (E) in
/-- A unit primitive of a cocycle together with the descended symmetric unit
`b⁻¹ τ(b⁻¹)` and the descended relative reduced norm of `b⁻¹`. -/
structure CocycleDescent (ξ : Cocycle G (GaloisCocycle.cover F L)) where
  primitive : (U).affinePoints (Rₐ L)
  coboundary : ∀ s : L ≃ₐ[F] L,
    toAmbient p L (GaloisCocycle.value ξ s) = primitive * (conjugate F L U s primitive)⁻¹
  symmetric : Bˣ
  norm : Eˣ
  tensor_symmetric : (τ.baseChange L).gramTransform ((unitEquiv[L]) primitive)⁻¹ 1 =
    (1 : L) ⊗ₜ[F] (symmetric : B)
  tensor_norm : (relativeNorm F E B L ((unitEquiv[L]) primitive)⁻¹ : E ⊗[F] L) =
    (norm : E) ⊗ₜ[F] (1 : L)

private theorem conjugate_inv_primitive {b : (U).affinePoints (Rₐ L)}
    {ξ : Cocycle G (GaloisCocycle.cover F L)}
    (hb : ∀ s : L ≃ₐ[F] L,
      toAmbient p L (GaloisCocycle.value ξ s) = b * (conjugate F L U s b)⁻¹)
    (s : L ≃ₐ[F] L) :
    Units.map (coefficientConjugate F L B s).toMonoidHom ((unitEquiv[L]) b)⁻¹ =
      ((unitEquiv[L]) b)⁻¹ * toUnits p L (GaloisCocycle.value ξ s) := by
  have h := congrArg (fun z => (unitEquiv[L]) z) (hb s)
  change (unitEquiv[L]) (toAmbient p L (GaloisCocycle.value ξ s)) =
    (unitEquiv[L]) (b * (conjugate F L U s b)⁻¹) at h
  rw [unitEquiv_toAmbient, _root_.map_mul, _root_.map_inv, unitEquiv_conjugate] at h
  rw [h, _root_.map_inv]
  group

/-- Every cocycle on a finite Galois cover of an infinite field has a descent. -/
theorem exists_cocycleDescent [Infinite F] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) : Nonempty (CocycleDescent E p ξ) := by
  obtain ⟨b, hb⟩ := exists_ambient_coboundary p ξ
  let q := (unitEquiv[L]) b
  have hconj := conjugate_inv_primitive p hb
  -- the symmetric element
  let T := (τ.baseChange L).gramTransform q⁻¹ 1
  have hTunit : IsUnit T := (τ.baseChange L).isUnit_gramTransform q⁻¹ isUnit_one
  have hTfix (s : L ≃ₐ[F] L) : coefficientConjugate F L B s hTunit.unit = hTunit.unit := by
    rw [IsUnit.unit_spec]
    have hm := map_gramTransform τ s.toAlgHom q⁻¹ (1 : L ⊗[F] B)
    change coefficientConjugate F L B s T =
      (τ.baseChange L).gramTransform (Units.map (coefficientConjugate F L B s).toMonoidHom q⁻¹)
        (coefficientConjugate F L B s 1) at hm
    rw [hm, _root_.map_one, hconj s, gramTransform_mul]
    congr 1
    have hc := (toUnits_mem p L (GaloisCocycle.value ξ s)).1
    rw [gramTransform, mul_one]
    exact hc
  obtain ⟨y, hy⟩ := exists_unit_of_fixed hTunit.unit hTfix
  -- the norm
  let N := relativeNorm F E B L q⁻¹
  have hNfix (s : L ≃ₐ[F] L) :
      Algebra.TensorProduct.map (AlgHom.id F E) s.toAlgHom (N : E ⊗[F] L) = N := by
    have h := relativeNorm_naturality F E B s.toAlgHom q⁻¹
    change relativeNorm F E B L (Units.map (coefficientConjugate F L B s).toMonoidHom q⁻¹) =
      _ at h
    rw [hconj s, _root_.map_mul, show relativeNorm F E B L (toUnits p L (GaloisCocycle.value ξ s))
      = 1 from (toUnits_mem p L (GaloisCocycle.value ξ s)).2, mul_one] at h
    have h' := congrArg (fun z : (E ⊗[F] L)ˣ => (z : E ⊗[F] L)) h
    exact h'.symm.trans rfl
  obtain ⟨z, hz⟩ := exists_fieldUnit_of_fixed N hNfix
  exact ⟨⟨b, hb, y, z, by rw [hy, IsUnit.unit_spec], hz.symm⟩⟩

end Galois

section Local

variable {L K : Type u} [Field L] [Algebra F L] [IsGalois F L] [Field K] [Algebra F K]
  {ξ : Cocycle G (GaloisCocycle.cover F L)} (d : CocycleDescent E p ξ)
  (M : Type u) [Field M] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M] [FiniteDimensional K M] [IsGalois K M]

private theorem relative_unitEquiv {B' C : Type u} [Field B'] [Field C] [Algebra F B']
    [Algebra F C] [Algebra B' C] [IsScalarTower F B' C] (b : (U).affinePoints (Rₐ B')) :
    (unitEquiv[C]) (relativeExtend F B' C U b) =
      Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F B' C)
        (AlgHom.id F B)).toMonoidHom ((unitEquiv[B']) b) :=
  FiniteAlgebraUnits.affinePointsEquiv_naturality _
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom F B' C)) b

private theorem exists_local_primitive_correction
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ (r : (U).affinePoints (Rₐ K)) (y : G.affinePoints (Rₐ M)),
      relativeExtend F K M U r = (toAmbient p M y)⁻¹ * relativeExtend F L M U d.primitive := by
  obtain ⟨y, hy⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
    (K := K) (M := M) ξ h
  let Bm := relativeExtend F L M U d.primitive
  let Y := toAmbient p M y
  let act := relativeConjugate F K M U
  have hfix (s : M ≃ₐ[K] M) : act s (Y⁻¹ * Bm) = Y⁻¹ * Bm := by
    let s₀ := s.restrictScalars F
    let s₁ := s₀.restrictNormal L
    let c := GaloisCocycle.value ξ s₁
    have h₁ : toAmbient p M (relativeExtend F L M G c) =
        relativeExtend F L M U (toAmbient p L c) :=
      toAmbient_naturality p (IsScalarTower.toAlgHom F L M) c
    have h₂ : toAmbient p M (conjugate F M G s₀ y) = act s Y :=
      toAmbient_naturality p s₀.toAlgHom y
    have h₃ : relativeExtend F L M U (conjugate F L U s₁ d.primitive) = act s Bm := by
      change GaloisCocycle.coverMap F L M ≫ GaloisCocycle.arrow F L s₁ ≫ d.primitive =
        GaloisCocycle.arrow F M s₀ ≫ GaloisCocycle.coverMap F L M ≫ d.primitive
      rw [← Category.assoc, ← Category.assoc, GaloisCocycle.arrow_coverMap]
    have he := congrArg (fun z => toAmbient p M z) (hy s)
    change toAmbient p M (relativeExtend F L M G c) =
      toAmbient p M (y * (conjugate F M G s₀ y)⁻¹) at he
    rw [h₁, d.coboundary s₁, _root_.map_mul, _root_.map_inv, h₃, _root_.map_mul,
      _root_.map_inv, h₂] at he
    rw [_root_.map_mul, _root_.map_inv]
    have he' := congrArg (fun z => Y⁻¹ * z * act s Bm) he
    change Y⁻¹ * (Bm * (act s Bm)⁻¹) * act s Bm =
      Y⁻¹ * (Y * (act s Y)⁻¹) * act s Bm at he'
    group at he'
    simpa only [_root_.zpow_neg_one] using he'.symm
  let z : relativeFixedSubgroup F K M U := ⟨Y⁻¹ * Bm, hfix⟩
  exact ⟨(relativeFixedEquiv F K M U).symm z, y, relativeExtend_descend F K M U z⟩

include M in
private theorem local_of_comparisonField
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ x : (K ⊗[F] B)ˣ, (1 : K) ⊗ₜ[F] (d.symmetric : B) = (x : K ⊗[F] B) * τ.baseChange K x ∧
      (relativeNorm F E B K x : E ⊗[F] K) = (d.norm : E) ⊗ₜ[F] (1 : K) := by
  obtain ⟨r, y, hr⟩ := exists_local_primitive_correction p d M h
  let Bm := (unitEquiv[M]) (relativeExtend F L M U d.primitive)
  let Y := (unitEquiv[M]) (toAmbient p M y)
  let P := ((unitEquiv[K]) r)⁻¹
  let k := IsScalarTower.toAlgHom F K M
  let l := IsScalarTower.toAlgHom F L M
  have hP : Units.map (Algebra.TensorProduct.map k (AlgHom.id F B)).toMonoidHom P = Bm⁻¹ * Y := by
    change Units.map (Algebra.TensorProduct.map k (AlgHom.id F B)).toMonoidHom
      (((unitEquiv[K]) r)⁻¹) = _
    rw [_root_.map_inv, ← relative_unitEquiv r, hr, _root_.map_mul, _root_.map_inv]
    change (Y⁻¹ * Bm)⁻¹ = Bm⁻¹ * Y
    group
  have hBm : Bm = Units.map (Algebra.TensorProduct.map l (AlgHom.id F B)).toMonoidHom
      ((unitEquiv[L]) d.primitive) := relative_unitEquiv d.primitive
  have hYmem : Y ∈ specialUnitaryPoints E τ M := by
    change (unitEquiv[M]) (toAmbient p M y) ∈ _
    rw [unitEquiv_toAmbient]
    exact toUnits_mem p M y
  have hinj : Function.Injective (Algebra.TensorProduct.map k (AlgHom.id F B)) :=
    TensorProduct.map_injective_of_flat_flat k.toLinearMap (LinearMap.id : B →ₗ[F] B)
      k.injective Function.injective_id
  have hinjF : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F E) k) :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id : E →ₗ[F] E) k.toLinearMap
      Function.injective_id k.injective
  have hmapE (x : E ⊗[F] K) : Algebra.TensorProduct.map (AlgHom.id E E) k x =
      Algebra.TensorProduct.map (AlgHom.id F E) k x := by
    induction x using TensorProduct.inductionOn with
    | tmul e c => rfl
    | add x x' hx hx' => rw [_root_.map_add, _root_.map_add, hx, hx']
  have hinjE : Function.Injective (Algebra.TensorProduct.map (AlgHom.id E E) k) := by
    intro a b hab
    apply hinjF
    rw [← hmapE, ← hmapE]
    exact hab
  refine ⟨P, ?_, ?_⟩
  · apply hinj
    have hY : (τ.baseChange M).gramTransform Y 1 = 1 := by
      rw [gramTransform, mul_one]
      exact hYmem.1
    have hB : (τ.baseChange M).gramTransform Bm⁻¹ 1 = (1 : M) ⊗ₜ[F] (d.symmetric : B) := by
      have e := congrArg (fun x => Algebra.TensorProduct.map l (AlgHom.id F B) x)
        d.tensor_symmetric
      simp only at e
      rw [map_gramTransform τ, _root_.map_one, Algebra.TensorProduct.map_tmul, _root_.map_one,
        AlgHom.id_apply, _root_.map_inv, ← hBm] at e
      exact e
    have hm := map_gramTransform τ k P (1 : K ⊗[F] B)
    rw [_root_.map_one, hP, gramTransform_mul, hY, hB] at hm
    rw [Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.id_apply, ← hm,
      gramTransform, mul_one]
  · apply hinjE
    have hn := relativeNorm_naturality F E B k P
    rw [hP, _root_.map_mul, show relativeNorm F E B M Y = 1 from hYmem.2, mul_one,
      hBm, _root_.map_inv, relativeNorm_naturality, ← _root_.map_inv] at hn
    have hn' : Algebra.TensorProduct.map (AlgHom.id E E) l
        (((relativeNorm F E B L ((unitEquiv[L]) d.primitive))⁻¹ : (E ⊗[F] L)ˣ) : E ⊗[F] L) =
        Algebra.TensorProduct.map (AlgHom.id E E) k (relativeNorm F E B K P : E ⊗[F] K) :=
      congrArg (fun z : (E ⊗[F] M)ˣ => (z : E ⊗[F] M)) hn
    have ht : (((relativeNorm F E B L ((unitEquiv[L]) d.primitive))⁻¹ : (E ⊗[F] L)ˣ) :
        E ⊗[F] L) = (d.norm : E) ⊗ₜ[F] (1 : L) := by
      rw [← _root_.map_inv]
      exact d.tensor_norm
    rw [← hn', ht, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      _root_.map_one, _root_.map_one]

/-- Triviality of the cocycle on the full pullback to a field of characteristic zero gives
local solutions of `y = x τ(x)` and `z = Nrd(x)`. -/
theorem CocycleDescent.exists_local_of_baseChange_isTrivial [FiniteDimensional F L] [CharZero K]
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ x : (K ⊗[F] B)ˣ, (1 : K) ⊗ₜ[F] (d.symmetric : B) = (x : K ⊗[F] B) * τ.baseChange K x ∧
      (relativeNorm F E B K x : E ⊗[F] K) = (d.norm : E) ⊗ₜ[F] (1 : K) := by
  obtain ⟨M, _, _, _, _, _, _, _, _⟩ :=
    CentralSimpleUnits.exists_finiteGalois_over_baseChange F K L
  exact local_of_comparisonField p d M h

end Local

section Global

variable {L : Type u} [Field L] [Algebra F L]

/-- The unit `1 ⊗ X` of `L ⊗[F] B` as a point of the unit group scheme. -/
private def includeUnitPoint (X : Bˣ) : (U).affinePoints (Rₐ L) :=
  (unitEquiv[L]).symm
    (Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] L ⊗[F] B).toMonoidHom X)

private theorem unitEquiv_includeUnitPoint (X : Bˣ) :
    (unitEquiv[L]) (includeUnitPoint (F := F) (L := L) X) =
      Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] L ⊗[F] B).toMonoidHom X :=
  MulEquiv.apply_symm_apply _ _

private theorem conjugate_includeUnitPoint (X : Bˣ) (s : L ≃ₐ[F] L) :
    conjugate F L U s (includeUnitPoint X) = includeUnitPoint X := by
  apply (unitEquiv[L]).injective
  rw [unitEquiv_conjugate, unitEquiv_includeUnitPoint]
  apply Units.ext
  change coefficientConjugate F L B s ((1 : L) ⊗ₜ[F] (X : B)) = (1 : L) ⊗ₜ[F] (X : B)
  rw [coefficientConjugate_tmul, _root_.map_one]

variable [FiniteDimensional F L] [IsGalois F L]
  {ξ : Cocycle G (GaloisCocycle.cover F L)} (d : CocycleDescent E p ξ)

/-- A global solution `X` of `y = X τ(X)` and `z = Nrd(X)` trivializes the cocycle. -/
theorem CocycleDescent.isTrivial_of_global (X : Bˣ) (hX : (d.symmetric : B) = X * τ X)
    (hN : reducedNorm E B E ((1 : E) ⊗ₜ[E] (X : B)) = d.norm) : ξ.IsTrivial := by
  have hw : ∀ s, toAmbient p L (GaloisCocycle.value ξ s) =
      (d.primitive * includeUnitPoint (F := F) (L := L) X) *
        (conjugate F L U s (d.primitive * includeUnitPoint (F := F) (L := L) X))⁻¹ := by
    intro s
    rw [d.coboundary s, _root_.map_mul, conjugate_includeUnitPoint (F := F) (L := L) X s]
    group
  let r := includeUnitPoint (F := F) (L := L) X
  let w := d.primitive * r
  let q := (unitEquiv[L]) d.primitive
  let X₁ := Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] L ⊗[F] B).toMonoidHom X
  have hwq : (unitEquiv[L]) w = q * X₁ := by
    change (unitEquiv[L]) (d.primitive * r) = _
    rw [_root_.map_mul, unitEquiv_includeUnitPoint]
  have hX₁ : (τ.baseChange L).gramTransform X₁ 1 = (1 : L) ⊗ₜ[F] (d.symmetric : B) := by
    change ((1 : L) ⊗ₜ[F] (X : B)) * 1 * τ.baseChange L ((1 : L) ⊗ₜ[F] (X : B)) = _
    rw [mul_one, baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hX]
  have hwmem : (unitEquiv[L]) w ∈ specialUnitaryPoints E τ L := by
    rw [hwq]
    refine ⟨(mem_unitaryPoints τ _).mpr ?_, ?_⟩
    · have h := (τ.baseChange L).gramTransform_mul q X₁ 1
      rw [hX₁, ← d.tensor_symmetric, ← gramTransform_mul, mul_inv_cancel,
        gramTransform_one, gramTransform, mul_one] at h
      exact h
    · change relativeNorm F E B L (q * X₁) = 1
      have hX₁n : relativeNorm F E B L X₁ = relativeNorm F E B L q⁻¹ := by
        apply Units.ext
        rw [relativeNorm_includeRight, hN, d.tensor_norm]
      rw [_root_.map_mul, hX₁n, ← _root_.map_mul, mul_inv_cancel, _root_.map_one]
  obtain ⟨x, hx⟩ := exists_toAmbient_eq p L w hwmem
  refine (GaloisCocycle.isTrivial_iff ξ).mpr ⟨x, fun s => toAmbient_injective p L ?_⟩
  have hc : toAmbient p L (conjugate F L G s x) = conjugate F L U s (toAmbient p L x) :=
    toAmbient_naturality p s.toAlgHom x
  rw [_root_.map_mul, _root_.map_inv, hc, hx]
  exact hw s

end Global

section Arithmetic

variable [NumberField F] [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

include p in
/-- Landherr's theorem and the unitary norm theorem give the Hasse kernel of a group
presented as `SU(B, τ)`: a cocycle on a finite Galois cover that is trivial on the full
pullback at every place is trivial. -/
theorem isTrivial_of_landherr_unitaryNorm (hL : NumberFieldLandherrStatement.{u})
    (hN : NumberFieldUnitaryNormStatement.{u})
    (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (SU3Root.conjugation F E e))
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  obtain ⟨d⟩ := exists_cocycleDescent p ξ
  have hloc (v : Global.Place F) : ∃ x : (Global.placeCompletion F v ⊗[F] B)ˣ,
      (1 : Global.placeCompletion F v) ⊗ₜ[F] (d.symmetric : B) =
          (x : Global.placeCompletion F v ⊗[F] B) * τ.baseChange (Global.placeCompletion F v) x ∧
        (relativeNorm F E B (Global.placeCompletion F v) x :
          E ⊗[F] Global.placeCompletion F v) =
          (d.norm : E) ⊗ₜ[F] (1 : Global.placeCompletion F v) := by
    rcases v with v | v
    · let : CharZero v.Completion :=
        charZero_of_injective_algebraMap (algebraMap F v.Completion).injective
      exact d.exists_local_of_baseChange_isTrivial p (K := v.Completion) (hξ (.inl v))
    · let : CharZero (Global.FiniteCompletion F v) := charZero_of_injective_algebraMap
        (algebraMap F (Global.FiniteCompletion F v)).injective
      exact d.exists_local_of_baseChange_isTrivial p (K := Global.FiniteCompletion F v)
        (hξ (.inr v))
  have hsym : τ (d.symmetric : B) = d.symmetric := by
    apply Algebra.TensorProduct.includeRight_injective (A := L) (algebraMap F L).injective
    change (1 : L) ⊗ₜ[F] τ (d.symmetric : B) = (1 : L) ⊗ₜ[F] (d.symmetric : B)
    rw [← baseChange_tmul, ← d.tensor_symmetric, involution_gramTransform, FirstKindInvolution.map_one]
  obtain ⟨x, hx⟩ := hL F E B τ hτ d.symmetric hsym (fun v => (hloc v).imp fun _ h => h.1)
  let nx : Eˣ := reducedNormUnits E B E
    (Units.map (Algebra.TensorProduct.includeRight : B →ₐ[E] E ⊗[E] B).toMonoidHom x)
  have hnx : (nx : E) = reducedNorm E B E ((1 : E) ⊗ₜ[E] (x : B)) := rfl
  obtain ⟨w, hw1, hw2⟩ := hN F E B τ hτ (d.norm * nx⁻¹) (fun v => by
    obtain ⟨xv, hxv1, hxv2⟩ := hloc v
    let K := Global.placeCompletion F v
    let X₁ := Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] K ⊗[F] B).toMonoidHom x
    refine ⟨X₁⁻¹ * xv, (mem_unitaryPoints τ _).mpr ?_, ?_⟩
    · have hX₁ : (τ.baseChange K).gramTransform X₁ 1 = (1 : K) ⊗ₜ[F] (d.symmetric : B) := by
        change ((1 : K) ⊗ₜ[F] (x : B)) * 1 * τ.baseChange K ((1 : K) ⊗ₜ[F] (x : B)) = _
        rw [mul_one, baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hx]
      have hxv : (τ.baseChange K).gramTransform xv 1 = (1 : K) ⊗ₜ[F] (d.symmetric : B) := by
        rw [gramTransform, mul_one, ← hxv1]
      have h := (τ.baseChange K).gramTransform_mul X₁⁻¹ xv 1
      rw [hxv, ← hX₁, ← gramTransform_mul, inv_mul_cancel, gramTransform_one, gramTransform,
        mul_one] at h
      exact h
    · have hX₁n : relativeNorm F E B K X₁ =
          Units.map (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] K).toMonoidHom nx :=
        Units.ext (relativeNorm_includeRight F E B K x)
      rw [_root_.map_mul, Units.val_mul, hxv2, _root_.map_inv, hX₁n, ← _root_.map_inv]
      change ((nx⁻¹ : Eˣ) : E) ⊗ₜ[F] (1 : K) * ((d.norm : E) ⊗ₜ[F] (1 : K)) =
        ((d.norm * nx⁻¹ : Eˣ) : E) ⊗ₜ[F] (1 : K)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.val_mul, mul_comm])
  refine d.isTrivial_of_global p (x * w) ?_ ?_
  · rw [Units.val_mul, FirstKindInvolution.map_mul, hx,
      show (x : B) * w * (τ w * τ x) = x * ((w : B) * τ w) * τ x by noncomm_ring, hw1, mul_one]
  · have h1 : (1 : E) ⊗ₜ[E] ((x * w : Bˣ) : B) =
        ((1 : E) ⊗ₜ[E] (x : B)) * ((1 : E) ⊗ₜ[E] (w : B)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.val_mul]
    rw [h1, _root_.map_mul, ← hnx, hw2, ← Units.val_mul, mul_comm d.norm nx⁻¹, ← mul_assoc,
      mul_inv_cancel, one_mul]

end Arithmetic

end Embedding

end Langlands.GroupScheme.UnitaryAlgebra
