import Langlands.GroupScheme.Rational.CocycleTorusReductionBasic
import Langlands.GroupScheme.Rational.FiniteGaloisCocycleValues
import Langlands.GroupScheme.FiniteFieldTorsorPoint.LangGroupScheme
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Finite-Galois cocycles of smooth connected affine groups over finite fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

section FieldMaps

variable {K : Type u} [Field K]

/-- The spectrum map of a homomorphism of field extensions is quasi-compact, flat and
surjective. -/
theorem ringTestMap_fpqc {A B : Type u} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) :
    QuasiCompact (ringTestMap K f).left ∧ Flat (ringTestMap K f).left ∧
      Surjective (ringTestMap K f).left := by
  let : Algebra A B := f.toRingHom.toAlgebra
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc A B
  exact ⟨h₃, h₂, h₁⟩

/-- The spectrum map of a homomorphism of field extensions is an epimorphism over the base. -/
theorem epi_ringTestMap {A B : Type u} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) : Epi (ringTestMap K f) := by
  obtain ⟨-, h₂, h₃⟩ := ringTestMap_fpqc f
  have := Flat.epi_of_flat_of_surjective (ringTestMap K f).left
  exact Over.epi_of_epi_left _

/-- An actual point of an affine group scheme of finite type with values in an algebraic field
extension `Ω` comes from a finite subextension, which may be chosen to contain any given finite
subset of `Ω`. -/
theorem exists_finite_factor {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (x : ringTest K Ω ⟶ G.X) (T : Set Ω) [Finite T] :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ T ⊆ E ∧
      ∃ xE : ringTest K E ⟶ G.X, ringTestMap K E.val ≫ xE = x := by
  classical
  let y := Lie.pointCoordinates G x
  have := Lie.coordinateAlgebraFiniteType G
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := CommRingCat.of K)
    (A := Lie.coordinateAlgebra G)
  let S : Set Ω := ((s.image y : Finset Ω) : Set Ω) ∪ T
  let E := IntermediateField.adjoin K S
  have hfin : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := K) z).isIntegral
  have hmem : ∀ d, y d ∈ E := by
    intro d
    have hd : d ∈ Algebra.adjoin (CommRingCat.of K) (s : Set (Lie.coordinateAlgebra G)) := by
      rw [hs]
      trivial
    induction hd using Algebra.adjoin_induction with
    | mem d hd =>
      exact IntermediateField.subset_adjoin K S
        (Or.inl (Finset.mem_coe.2 (Finset.mem_image_of_mem y hd)))
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact E.algebraMap_mem r
    | add a b _ _ ha hb =>
      rw [map_add]
      exact E.add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact E.mul_mem ha hb
  let yE : Lie.coordinateAlgebra G →ₐ[CommRingCat.of K] E :=
    { toFun := fun d => ⟨y d, hmem d⟩
      map_one' := Subtype.ext (map_one y)
      map_mul' := fun a b => Subtype.ext (map_mul y a b)
      map_zero' := Subtype.ext (map_zero y)
      map_add' := fun a b => Subtype.ext (map_add y a b)
      commutes' := fun r => Subtype.ext (y.commutes r) }
  refine ⟨E, hfin, fun z hz => IntermediateField.subset_adjoin K S (Or.inr hz),
    (Lie.pointCoordinates G).symm yE, ?_⟩
  apply (Lie.pointCoordinates G).injective
  have h : ringTestMap K E.val ≫ (Lie.pointCoordinates G).symm yE =
      Lie.affineMap G E.val ((Lie.pointCoordinates G).symm yE) := by
    rw [Lie.affineMap_apply, FiniteFieldTorsorPoint.ringTestMap_eq_algSpec_map]
    rfl
  rw [h, Lie.pointCoordinates_naturality, Equiv.apply_symm_apply]
  ext d
  rfl

end FieldMaps

section Frobenius

variable {K : Type u} [Field K] [Fintype K]
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {G : GroupScheme (Spec (CommRingCat.of K))}

omit [Fintype K] [FiniteDimensional K L] [IsGalois K L] in
theorem ringTestMap_galois_mul (σ τ : L ≃ₐ[K] L) :
    ringTestMap K (σ * τ).toAlgHom = ringTestMap K σ.toAlgHom ≫ ringTestMap K τ.toAlgHom := by
  rw [← ringTestMap_comp]
  congr 1

omit [Fintype K] [FiniteDimensional K L] [IsGalois K L] in
/-- The Galois values of a natural cocycle on a finite Galois cover satisfy the crossed
homomorphism rule. -/
theorem toFun_galois_mul (ξ : Cocycle G (ringTest K L)) (σ τ : L ≃ₐ[K] L) :
    ξ.toFun (𝟙 _) (ringTestMap K (σ * τ).toAlgHom) =
      ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom) *
        (ringTestMap K σ.toAlgHom ≫ ξ.toFun (𝟙 _) (ringTestMap K τ.toAlgHom)) := by
  rw [ringTestMap_galois_mul, ξ.cocycle (𝟙 _) (ringTestMap K σ.toAlgHom), ← ξ.naturality,
    Category.comp_id]

/-- Over a finite field, a natural cocycle on a finite Galois cover is a coboundary as soon as
the coboundary equation holds at the Frobenius automorphism. -/
theorem isTrivial_of_frobenius (ξ : Cocycle G (ringTest K L)) (c : ringTest K L ⟶ G.X)
    (h : ξ.toFun (𝟙 _) (ringTestMap K (FiniteField.frobeniusAlgEquivOfAlgebraic K L).toAlgHom) =
      c * (ringTestMap K (FiniteField.frobeniusAlgEquivOfAlgebraic K L).toAlgHom ≫ c)⁻¹) :
    ξ.IsTrivial := by
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  have key : ∀ n : ℕ, ξ.toFun (𝟙 _) (ringTestMap K (φ ^ n).toAlgHom) =
      c * (ringTestMap K (φ ^ n).toAlgHom ≫ c)⁻¹ := by
    intro n
    induction n with
    | zero =>
      have h1 : (φ ^ 0).toAlgHom = AlgHom.id K L := by
        rw [pow_zero]
        rfl
      rw [h1, ringTestMap_id, toFun_self, Category.id_comp, mul_inv_cancel]
    | succ n ih =>
      rw [pow_succ, toFun_galois_mul, ih, h, ringTestMap_galois_mul]
      simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
      group
  have : Finite L := Module.finite_of_finite K
  refine isTrivial_of_galois ξ c fun σ => ?_
  obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 σ
  exact key n.1

end Frobenius

section Main

variable {K : Type u} [Field K]

/-- Over a finite field, every natural cocycle of a smooth connected affine group on a finite
Galois cover is a coboundary. -/
theorem isTrivial_of_finite [Fintype K] (G : GroupScheme (Spec (CommRingCat.of K)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ξ : Cocycle G (ringTest K L)) : ξ.IsTrivial := by
  have : Finite L := Module.finite_of_finite K
  let κ : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let φL := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  obtain ⟨x, hx⟩ := FiniteFieldTorsorPoint.exists_eq_inv_mul_frobenius G (AlgebraicClosure K)
    (ringTestMap K κ ≫ ξ.toFun (𝟙 _) (ringTestMap K φL.toAlgHom))
  obtain ⟨E, hfin, hT, xE, hxE⟩ := exists_finite_factor G x (Set.range κ)
  have : Finite E := Module.finite_of_finite K
  let κE : L →ₐ[K] E :=
    { toFun := fun l => ⟨κ l, hT ⟨l, rfl⟩⟩
      map_one' := Subtype.ext (map_one κ)
      map_mul' := fun a b => Subtype.ext (map_mul κ a b)
      map_zero' := Subtype.ext (map_zero κ)
      map_add' := fun a b => Subtype.ext (map_add κ a b)
      commutes' := fun r => Subtype.ext (κ.commutes r) }
  let φE := FiniteField.frobeniusAlgEquivOfAlgebraic K E
  have h₁ : φE.toAlgHom.comp κE = κE.comp φL.toAlgHom :=
    AlgHom.ext fun l => (map_pow κE l (Fintype.card K)).symm
  have h₂ : E.val.comp φE.toAlgHom =
      (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).comp E.val :=
    AlgHom.ext fun e => map_pow E.val e (Fintype.card K)
  have h₃ : E.val.comp κE = κ := AlgHom.ext fun _ => rfl
  have hs₁ : ringTestMap K φE.toAlgHom ≫ ringTestMap K κE =
      ringTestMap K κE ≫ ringTestMap K φL.toAlgHom := by
    rw [← ringTestMap_comp, ← ringTestMap_comp, h₁]
  have hs₂ : ringTestMap K E.val ≫ ringTestMap K φE.toAlgHom =
      ringTestMap K (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) ≫ ringTestMap K E.val := by
    rw [← ringTestMap_comp, ← ringTestMap_comp, h₂]
  have hs₃ : ringTestMap K E.val ≫ ringTestMap K κE = ringTestMap K κ := by
    rw [← ringTestMap_comp, h₃]
  have hnat : ξ.toFun (ringTestMap K κE) (ringTestMap K κE ≫ ringTestMap K φL.toAlgHom) =
      ringTestMap K κE ≫ ξ.toFun (𝟙 _) (ringTestMap K φL.toAlgHom) := by
    rw [← ξ.naturality, Category.comp_id]
  have key : (ξ.refine (ringTestMap K κE)).IsTrivial := by
    refine isTrivial_of_frobenius _ xE⁻¹ ?_
    rw [refine_toFun, Category.id_comp, hs₁, hnat]
    have := epi_ringTestMap (K := K) E.val
    apply (cancel_epi (ringTestMap K E.val)).1
    rw [← Category.assoc, hs₃, hx, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv,
      ← Category.assoc, hs₂, Category.assoc, GrpObj.comp_inv, hxE, GrpObj.comp_inv, inv_inv]
  obtain ⟨h₄, h₅, h₆⟩ := ringTestMap_fpqc κE
  exact (isTrivial_refine_iff ξ (ringTestMap K κE)).1 key

end Main

/-- Over a finite field, every cocycle of a connected reductive group on a finite Galois cover
has a torus reduction: it is a coboundary, so it reduces to the trivial torus. -/
theorem nonempty_torusReduction_of_finite {K : Type u} [Field K] [Finite K]
    {G : GroupScheme (Spec (CommRingCat.of K))} (hG : IsConnectedReductive G)
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))) :
    Nonempty ξ.TorusReduction := by
  have := Fintype.ofFinite K
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  exact TorusReduction.nonempty_of_isTrivial (isTrivial_of_finite G (L := L) ξ)

end Langlands.GroupScheme.Cocycle
